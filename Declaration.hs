module Declaration where

import Data.Set
import Data.Map
import Data.List
import Data.Maybe
import Control.Monad
import Control.Applicative hiding (Const)
import Debug.Trace

import qualified Core as C
import Core hiding (Inductive,Fixpoint)
import Elaborator
import Typecheck
import Utils
import Normalization
import Substitution
import Parser
import Lexer(Loc)
import Prettyprint
import Inductive
import Equations

{-
  here we process top-level declarations
-}

checkDecl :: ElabState -> Decl -> Either Error ElabState
checkDecl st decl = case decl of
  Inductive defs -> checkInductive st defs
  Definition defs -> checkDefinition st defs
  
checkInductive :: ElabState -> [Inductive] -> Either Error ElabState
checkInductive st defs = do 

  let defcount = length defs
      
      (def_locs, binders, paramss, arities, ctors) = unzip5 defs
      
      names = fmap binderName binders
      
      qnames = fmap (\name -> [moduleName st, name]) names

      ctor_names = fmap (fmap (binderName . fst)) ctors
      
      ctor_qnames = concat (zipWith (\qname ctornames -> fmap (\name -> qname ++ [name]) ctornames) qnames ctor_names)

  mapM_ (ensureUnique st) ctor_qnames
  mapM_ (ensureUnique st) qnames

  let f :: Context -> [Param] -> Either Error Context
      f ctx ((bind,Nothing):_) = Left (show (binderLoc bind) ++ "cannot infer parameters of inductive type")
      f ctx ((bind,Just ty):params) = do
        (ty,_) <- infer st ctx noSubst ty
        f ((binderName bind, ty) : ctx) params
      f ctx [] = pure ctx

  paramss <- mapM (f []) paramss
    
  arities <- zipWithM (\p a -> fmap fst (infer st p noSubst a)) paramss arities
    
  let extendArity :: Term -> Context -> Term
      extendArity = Data.List.foldl (\acc (name,ty) -> Pi name ty acc) 
    
      -- arities extended with parameters
      arities_ext = zipWith extendArity arities paramss
  
      -- context with extended arities
      arities_ctx = reverse (zipWith (,) names arities_ext)

      checkCtor :: Context -> Int -> Int -> Ctor -> Either Error Term
      checkCtor ctx defno paramno (bind,expr) = do
        (t,_) <- infer st ctx noSubst expr
        allOccurrencesPositive (signature st) ctx (exprLoc expr) defcount defno paramno (length ctx - defcount) (length ctx) t
        pure t
      
      checkDef :: (Int,Context,[Ctor]) -> Either Error [Term]
      checkDef (defno, params, ctors) = do
        mapM (checkCtor (params ++ arities_ctx) defno (length params)) ctors
    
  (ctor_tys) <- mapM checkDef (zip3 [0..] paramss ctors)

  let fresh_id = newName st
      -- abstracted ctors explicitly quantify over the datatype parameters
      abstractCtors :: Context -> [Term] -> [Term]
      abstractCtors params ctors = fmap (flip f params) ctors where
        f = Data.List.foldl (\acc (name,ty) -> Pi name ty acc)
      
      abstracted_ctors = zipWith abstractCtors paramss ctor_tys
      
      computeArity (Pi _ _ b) = 1 + computeArity b
      computeArity _ = 0
      
      ctor_arities = fmap (fmap computeArity) ctor_tys -- compute arities
      
      uniparamno = 0 :: Int
      --Data.List.foldr getUniparamno (minimum (fmap length paramss)) (concat abstracted_ctors)
  
      def_refs = fmap (\defno -> Ind fresh_id defno uniparamno) [0 .. defcount - 1]
      
      def_consts = fmap (flip App []) def_refs
  
      def_name_loc_refs = zip3 qnames def_locs def_refs
      
      ctor_instances = fmap (fmap (psubst (reverse def_consts))) abstracted_ctors
      
      ctor_refs = concat (zipWith3
        (\ctors params defno ->
          fmap
            (\ctorno ->
              Con
                fresh_id
                defno
                ctorno
                (length params))
            [0.. length ctors - 1])
        ctor_instances
        paramss
        [0..])
      
      ctor_locs = concat (fmap (fmap (exprLoc . snd)) ctors)
      
      ctor_ref_name_locs = zip3 ctor_qnames ctor_locs ctor_refs
      
      obs = signature st
      
      object = zipWith5 (\arity ctor_names ctor_arities ctor_tys params ->
        C.Inductive {
          indSort = arity,
          paramno = length params,
          introRules = zip3 ctor_names ctor_arities ctor_tys})
        arities_ext
        ctor_names
        ctor_arities
        ctor_instances
        paramss
      
      name_loc_refs = ctor_ref_name_locs ++ def_name_loc_refs
      name_names = zip (concat ctor_names) ctor_qnames ++ zip names qnames
   
  when debug $ traceM (intercalate "\n" (fmap showQName qnames))
  
  pure st {
    newName = fresh_id + 1,
    internalNames = updateNameSpace name_loc_refs (internalNames st),
    signature = obs{sigInd = Data.Map.insert fresh_id object (sigInd obs)}}

checkDefinition :: ElabState -> [Function] -> Either Error ElabState
checkDefinition st defs = do
  let 
    checkSignature = fmap fst . infer st [] noSubst
    
    (locs, binders, tys, clausess) = unzip4 defs
    
    defcount = length defs
    
    checkClauses st clauses ty =
      compileEquations st [] 0 noSubst (fmap mkProblem clauses) ty
    
    (names,qnames) = unzip (fmap (\bind ->
      let name = binderName bind in (name, [moduleName st, name])) binders)
  
  mapM_ (ensureUnique st) qnames

  --traceM "checking signatures"

  tys <- mapM checkSignature tys

  -- insert types into context
  let
    obj_id = newName st
    obs = signature st
    alldefs = sigDef obs
    names = internalNames st
    defnos = [0 .. defcount - 1]
    uniparamno = 0
    heads = fmap (\n -> Def obj_id n uniparamno) defnos
    newnames = updateNameSpace (zip3 qnames locs heads) names
    
    dum_body = error "body of dummy"
    dum_defs = fmap (flip (,) dum_body) tys 
    dum_sig = Signature (sigInd obs) (Data.Map.insert obj_id dum_defs alldefs)
    dum_st = st {
      newName = obj_id + 1,
      internalNames = newnames,
      signature = dum_sig}

  --traceM "checking clauses"

  trees <- zipWithM (checkClauses dum_st) clausess tys
  
  --traceM $ showCaseTree (head trees)
  
  let
    defs = zip tys trees
    sig = Signature (sigInd obs) (Data.Map.insert obj_id defs alldefs)
    
  when debug $ traceM (intercalate "\n" (fmap showQName qnames))

  pure (st {
    newName = obj_id + 1,
    internalNames = newnames,
    signature = sig})