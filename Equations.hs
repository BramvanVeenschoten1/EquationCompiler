module Equations where

import Unification
import Parser
import Core
import Typecheck
import Elaborator
import Lexer(Loc)
import Normalization
import Substitution
import Utils
import Prettyprint

import Data.Maybe
import Data.Map
import Data.List
import Control.Monad
import Debug.Trace


{-
input:
  signature,
  context + lenght,
  substitution,
  problems,
  expected type,
output:
  casetree

original steps:
- done
- intro
- splitCon
- splitEq
- splitEmpty

new steps:
- done
- intro
- split + unify indices
  gather constructors to type introduced variables,
  construct unification problems,
  solve problem for each constructor
  continue in case of positive success
  refute branch in case of negative success,
  or if the constraint has a different ctor
- split absurd
  like split, but expect negative success in every branch

order of trying:
- done
- intro
- refute
- split

let's do left to right for now

notes:
- nested patterns yield more constraints after splitting
- unification happens only on the type of the split variable and
  the constructor applied to the parameters and its arguments
- for a core language, it may be useful to dispense with parameters,
  as they are completely subsumed by indices as far as unification is concerned
  the uses of parameters are:
  - uniform parameters for positivity checking
  - regular parameters can be disregarded from user patterns
    this is subsumed by implicit constructor arguments though.
- add default cases, only useful when we have dags

def filter : Pi (A : Type)(p : A -> Bool)(xs : List A), List A
| a p List.nil = nil
| a p (cons x xs) = filter0 A (p x) x (filter A p xs)
and filter0 : Pi (A : Type)(b : Bool)(x : A)(xs : List A), List A
| A bool.true x xs = cons A x xs
| A bool.false _ xs = xs

filter : Pi (A : Type)(p : A -> Bool)(xs : List A), List A
filter0 : Pi (A : Type)(b : Bool)(x : A)(xs : List A), List A

filter a p List.nil = nil
filter a p (cons x xs) = filter0 A (p x) x (filter A p xs)

filter0 A bool.true x xs = cons A x xs
filter0 A bool.false _ xs = xs

TODO:
  - dont inspect aburd rhs'
  - stronger check for constructor patterns
  - desugar let to fun?
    => probably harder than including let, still quasi-important to implement
  - lift cases?
-}

data Problem = Problem {
  problemNames       :: Map Int String,  -- DB: => Var
  problemConstraints :: Map Int Pattern, -- DBL => Pattern
  problemPatterns    :: [Pattern],
  problemRHS         :: Expr}

showProblem (Problem n c p r) =
  "names:\n" ++
  showMap n ++
  "\nconstraints:\n" ++
  showMap c ++
  "\npatterns:\n" ++
  show p ++ "\n"

mkProblem :: Clause -> Problem
mkProblem (pats, rhs) = Problem Data.Map.empty Data.Map.empty pats rhs

isApp :: Pattern -> Bool
isApp (PApp _ _ _) = True
isApp _ = False

isRefuted :: Tree -> Bool
isRefuted (Refuted _) = True
isRefuted _ = False

mkCtx :: [Term] -> Int -> Map Int String -> Context
mkCtx ctx k names = zipWith getName [0..] ctx where
  getName n ty = case Data.Map.lookup (k - n - 1) names of
    Just x -> (x,ty)
    _ -> ("",ty)

insertPattern :: Int -> Pattern -> Problem -> Problem
insertPattern k p (Problem n c ps r) = case p of
  PApp _ _ _ -> Problem n (Data.Map.insert k p c) ps r
  PVar _ x   -> Problem (Data.Map.insert k x n) c ps r
  _          -> Problem n c ps r

deletePattern :: Int -> Problem -> Problem
deletePattern k (Problem n c p r) =
  Problem n (Data.Map.delete k c) p r

compileEquations :: ElabState ->
                    [Term] ->
                    Int ->
                    Substitution ->
                    [Problem] ->
                    Term ->
                    Either String Tree
compileEquations _ _ _ _ [] _ = Left "No clauses left"
compileEquations st ctx k subst (probs @ (problem : _)) ty
  | Prelude.null (problemPatterns problem) &&
    Data.Map.null (problemConstraints problem) = done
  | all (not . Prelude.null . problemPatterns) probs = tryIntro
  | otherwise = trySplit
  where
    sig :: Signature
    sig = signature st
  
    done :: Either String Tree
    done = Body <$> check st ctx' subst (problemRHS problem) ty where
      ctx' = mkCtx ctx k (problemNames problem)
    
    tryIntro :: Either String Tree
    tryIntro = case reduce sig subst ty of
      Pi name src dst -> do
        when False $ do traceM "intro"
        Lam <$> compileEquations st (src : ctx) (k + 1) subst probs' dst'
        where
          refineProblem :: Problem -> Problem
          refineProblem prob = insertPattern k hd tl where
            hd = head (problemPatterns prob)
            tl = prob {problemPatterns = tail (problemPatterns prob)}
            
          probs' :: [Problem]
          probs' = fmap refineProblem probs
          
          dst' :: Term
          dst' = Substitution.subst (mkDBL k) dst
          
      _ -> trySplit
    
    trySplit :: Either String Tree
    trySplit = Data.List.foldr
      (uncurry split)
      (Left $ showProblem problem ++ "\nEquation compiler stuck")
      (toList (problemConstraints problem)) 
    
    kth :: Int -> Term
    kth n = fromMaybe (error $
      "\nIn Context:" ++
      showContext (mkCtx ctx k (problemNames problem)) ++
      "\nWith Substitution:\n" ++
      showSubst subst ++
      "Out of bounds access: " ++
      show (k - n - 1)) $ nth (k - n - 1) ctx
    
    split :: Int -> Pattern -> Either String Tree -> Either String Tree
    split n pat fail = case reduce sig subst (kth n) of
      i @ (App (Ind obj_id defno _) args) -> do
        when False $ do
          traceM $ "\nsplit on: " ++ show n
          traceM $ "Paramno: " ++ show pno
          traceM $ "Indexno: " ++ show (length indices)
          traceM $ "old context:"
          traceM $ showContext (mkCtx ctx k (problemNames problem))
        trees <- zipWithM specializeCtor ctors [0..]
        tryRefute pat trees
        where
          -- get constructor types
          ind   = fromJust (Data.Map.lookup obj_id (sigInd sig)) !! defno
          pno   = paramno ind
          ctors = introRules ind
          
          (params, indices) = Data.List.splitAt pno args
          
          -- if no constructors remain, expect absurd pattern in first clause and refute
          tryRefute :: Pattern -> [Tree] -> Either String Tree
          tryRefute PAbsurd branches
            | all isRefuted branches = pure (Refuted n)
            | otherwise = Left "cannot refute valid data"
          tryRefute _ branches = pure (Case (k - n - 1) branches)
          
          -- specialize through unification:
          -- eliminate conflicting constructors,
          -- compile equations for remaining constructors,
          -- expect absurd pattern if no constructors remain,
          -- construct case node otherwise
          specializeCtor :: (String,Int,Term) -> Int -> Either String Tree
          specializeCtor (name, ctor_arity, ctor_ty) ctorno = compileBranch unification_result where
          
            ctor_with_params = instantiateCtor params ctor_ty
          
            specializeType :: [Term] -> Int -> Term -> ([Term], Int, Term)
            specializeType acc k (Pi name src dst) =
              specializeType
                (src : acc)
                (k + 1)
                (Substitution.subst (mkDBL k) dst)
            specializeType acc k dst = (acc, k, dst)
            
            ctor_args = params ++ Data.List.take ctor_arity (fmap mkDBL [k..])
            
            applied_ctor = App (Con obj_id defno ctorno pno) ctor_args
            
            (ctx', k', App _ args') = specializeType ctx k ctor_with_params
            
            ctx'' = mkCtx ctx' k' Data.Map.empty
            
            indices' = Data.List.drop pno args'
            
            equations = makeEquations sig ctx'' subst indices indices'
            
            unification_result = {- trace (
              "new context:\n" ++
              showContext ctx'' ++
              "\nequations:\n" ++
              show equations)-}
                unify sig ctx'' subst equations
            
            filterProblem :: Substitution -> Problem -> Maybe (Either String Problem)
            filterProblem subst' prob =
              matchConstraint (fromJust (Data.Map.lookup n (problemConstraints prob))) where

                matchConstraint :: Pattern -> Maybe (Either String Problem)
                matchConstraint (PApp loc qname pats)
                  -- also error if name does not belong to data!
                  | last qname == name && length pats == ctor_arity =
                    pure (pure (
                      Data.List.foldr
                      (uncurry insertPattern)
                      (deletePattern n prob)
                      (zip [k ..] pats)))
                  | last qname == name = Just (Left (show loc ++
                    "constructor expected " ++
                    show ctor_arity ++
                    " arguments, but got " ++
                    show (length pats) ++ "\n"))
                  | otherwise = Nothing
                matchConstraint _ = pure (pure prob)
            
            compileBranch :: Result Substitution -> Either String Tree
            compileBranch (Stuck _)    = {-trace "stuck"   -} fail
            compileBranch No           = {-trace "refuted" -} pure (Refuted n)
            compileBranch (Yes subst') = {-trace "unified" -} branch probs' where
              subst'' = Data.Map.insert n applied_ctor subst'
            
              probs' = sequence (Data.Maybe.mapMaybe (filterProblem subst'') probs)
              
              branch ps = do
                probs' <- ps
                compileEquations st ctx' k' subst'' probs' ty
      _ -> fail
  
