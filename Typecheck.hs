module Typecheck where

import Core
import Substitution
import Normalization
import Elaborator
import Lexer(Loc)
import Parser
import Prettyprint
import Utils

import Debug.Trace
import Data.Maybe
import Data.Map

typeOfHead :: Signature -> Context -> Substitution -> Head -> Term
typeOfHead sig ctx subst = g where
  g (DBI  n) = snd (fromMaybe (error "TypeOfHead: DBI out of range") (nth n ctx))
  g (DBL  n) = snd (fromMaybe (error "TypeOfHead: DBL out of range") (nth (length ctx - n - 1) ctx))
  g (Ind i j _) = let
    block = fromJust (Data.Map.lookup i (sigInd sig))
    def   = block !! j
    in indSort def
  g (Con i j k _) = let
    block    = fromJust (Data.Map.lookup i (sigInd sig))
    def      = block !! j
    (_,_,ty) = introRules def !! k
    in ty
  g (Def i j _) = fst (fromJust (Data.Map.lookup i (sigDef sig)) !! j)

typeOf :: Signature -> Context -> Substitution -> Term -> Term
typeOf sig ctx subst = f where
  f (App head tail)   = h (typeOfHead sig ctx subst head) tail
  f (Pi name src dst) = Type 0
    
  h ty [] = ty
  h (Pi name src dst) (arg : args) = h (reduce sig subst (Substitution.subst arg dst)) args

-- look up a qualified name in the symbol table
lookupQualified :: ElabState -> Loc -> QName -> Either String (Head,Term)
lookupQualified st loc qname =
  case lookupQName qname st of
    Nothing -> err (show loc ++ "unknown name: " ++ showQName qname)
    Just (_,ref) -> pure (ref, typeOfHead
      (signature st)
      (error "type of constant should not inspect context")
      (error "type of constant should not inspect substitution")
      ref)

-- look up a name in the symbol table and lookup Unqualified if appropriate
lookupUnqualified :: ElabState -> Loc -> Name -> Either String (Head,Term)
lookupUnqualified st loc name = let
  in case lookupName name st of
    Nothing      -> Left (show loc ++ "unbound variable")
    Just [qname] -> lookupQualified st loc qname
    Just xs      -> Left (show loc ++ "ambiguous name")

-- lookup a name in the context and return appropriate uses if present
lookupCtx :: Context -> Loc -> Name -> Maybe (Head,Term)
lookupCtx ctx loc name = f 0 ctx where
  f n [] = Nothing
  f n ((name1,ty):hyps)
    | name == name1 = pure (DBI n, lift (n + 1) ty)
    | otherwise     = f (n + 1) hyps

inferHead :: ElabState -> Context -> Substitution -> EHead -> Either String (Head,Term)
inferHead st ctx subst head = case head of
  EName loc xs -> lookupQualified st loc xs
  EVar  loc x -> maybe (lookupUnqualified st loc x) Right (lookupCtx ctx loc x)

check :: ElabState -> Context -> Substitution -> Expr -> Term -> Either String Term
check st ctx subst expr ty = do
  let loc = exprLoc expr
      sig = signature st
  (term, ty1) <- infer st ctx subst expr
  if convertible sig subst (length ctx) ty ty1
  then pure term
  else Left (
    show loc ++
    "\nin context:" ++
    showContext ctx ++
    "\nwith substitution:\n" ++
    showSubst subst ++
    "\nexpected type:\n" ++
    showTerm ctx ty ++
    "\nbut term:\n" ++
    showTerm ctx term ++
    "\nhas type:\n" ++
    showTerm ctx ty1 ++
    "\nreduced:\n"++
    showTerm ctx (reduce sig subst ty) ++
    "\n<=/=>\n" ++
    showTerm ctx (reduce sig subst ty1))

infer :: ElabState -> Context -> Substitution -> Expr -> Either String (Term,Term)
infer st ctx subst expr = case expr of
  EType loc -> do
    pure (Type 0, Type 0)
  EApply loc head args -> do
    (head,head_ty) <- inferHead st ctx subst head
    (args,app_ty) <- checkArgs head_ty args
    pure (App head args, app_ty)
    where
      checkArgs :: Term -> [Expr] -> Either String ([Term],Term)
      checkArgs head_ty [] = pure ([], head_ty)
      checkArgs head_ty (arg:args) = do
        let head_ty' = reduce (signature st) subst head_ty
        case reduce (signature st) subst head_ty of
          Pi name src dst -> do
            arg <- check st ctx subst arg src
            let dst' = Substitution.subst arg dst
            (args, dst) <- checkArgs dst' args
            pure (arg:args, dst)
          x -> Left (
            show loc ++
            "\nin context:" ++
            showContext ctx ++
            "\nexpected a function in application, but got:\n" ++
            showTerm ctx x)      
  EPi loc name src dst -> do
    let name1 = fromMaybe "" (fmap binderName name)
    (src,src_k) <- infer st ctx subst src
    (dst,dst_k) <- infer st ((name1,src):ctx) subst dst
    pure (Pi name1 src dst, Type 0)