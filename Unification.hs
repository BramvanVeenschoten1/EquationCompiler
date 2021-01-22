module Unification where

import Core
import Normalization
import Substitution
import Typecheck
import Utils

import Data.Map


{- Pattern unification
  Input:
  Signature,
  Context,
  Substitution,
  equality telescope
  
  Output:
  | Success => subst
  | Negative Success
  | Stuck
-}

{-

cons : (n : Nat) -> A -> Vec A n -> Vec A (succ n)

nth : (A : Type) -> (n : Nat) -> Vec A n -> Fin n -> n
nth _ _ (cons m x xs) (fzero k) = x
nth _ _ (cons m x xs) (fsucc k i) = nth a m xs i

tel   = (A : Type)(n : Nat)
goal  : Vec A n -> Fin n -> n
pat   = Cons m x xs : Vec A (succ m)
index = (succ m)
het   : Eq Nat Nat n (succ m), Eq (Vec A n) (Vec A (succ m)) xs' (cons m x xs)
hom   : e  : Eq Nat n (succ m),
        e2 : Eq (Vec A (succ m)) (subst (Vec A) e xs') (cons m x xs)
-}

{- TODO:
  - investigate whether heterogeneous equations can be postponed
  
  hom:
  
  (e : Eq Nat n m)(e1 : Eq (Fin m) (subst Fin e (fzero n)) (fzero m))
  =>
  Refl, e1 : Eq Fin m (fzero m) (fzero m)
  
  het:
  
  Eq Nat Nat n m, Eq (Fin n) (Fin m) (fzero n) (fsucc m)
  =>
  Eq (Fin n) (Fin n) (fzero n) (fzero n)
  
  conjecture : restricting unification to wellFormed heterogeneous equalities is equivalent
  to lay-over equalities + K
  
  if false:
  learn how to use lay-over equalities
  anyway:
  learn how to generate equalities from indices
-}

data Equation = Equation {
  leftType  :: Term,
  rightType :: Term,
  leftTerm  :: Term,
  rightTerm :: Term}
  deriving Show

data Result a
  = Yes a
  | No
  | Stuck Equation

{-
  solution
    if one term is a variable and does not occur in the other
    and types are equal
  deletion
    if types and term are equal
  injection
    only if the types are equal
    and constructors are equal
  conflict
    only if the types are equal,
    constructors are different and fully applied
  cycle
    can only be applied if one term is a de bruijn level and
    the other term is in constructor form, that is,
    a DBL or a constructor applied to constructor forms
    so x = f x is only a cycle if f is a constructor
    both types must be equal
-}

makeEquations :: Signature ->
                 Context ->
                 Substitution ->
                 [Term] ->
                 [Term] ->
                 [Equation]
makeEquations sig ctx subst =
  zipWith makeEquation
    where
      makeEquation x0 x1 =
        Equation
          (typeOf sig ctx subst x0)
          (typeOf sig ctx subst x1)
          x0 x1 

unify :: Signature -> Context -> Substitution -> [Equation] -> Result Substitution
unify sig ctx subst [] = Yes subst
unify sig ctx subst (eq : eqs)
  | not wellFormed = Stuck eq'
  | canDelete      = unify sig ctx subst eqs
  | otherwise      = tryConflictInjectSolveCycle
  where
    eq' :: Equation
    eq' = Equation lt rt l r where
      lt = reduce sig subst ( leftType eq)
      rt = reduce sig subst (rightType eq)
      l  = reduce sig subst ( leftTerm eq)
      r  = reduce sig subst (rightTerm eq)
  
    wellFormed :: Bool
    wellFormed = convertible sig subst (length ctx) (leftType eq') (rightType eq')
    
    canDelete :: Bool
    canDelete = convertible sig subst (length ctx) (leftTerm eq') (rightTerm eq')
    
    tryConflictInjectSolveCycle :: Result Substitution
    tryConflictInjectSolveCycle =
      case (leftType eq', leftTerm eq', rightTerm eq') of
        (App (Ind _ _ _) _, App (Con _ _ c0 _) xs0, App (Con _ _ c1 _) xs1)
                               -> injectOrConflict c0 c1 xs0 xs1
        (_, App (DBL n) [], t) -> cycleOrSolve n t
        (_, t, App (DBL n) []) -> cycleOrSolve n t
        _                      -> Stuck eq'

    injectOrConflict :: Int -> Int -> [Term] -> [Term] -> Result Substitution
    injectOrConflict c0 c1 xs0 xs1
      | c0 == c1 = inject xs0 xs1
      | otherwise = No

    inject :: [Term] -> [Term] -> Result Substitution
    inject xs0 xs1 =
      unify sig ctx subst (makeEquations sig ctx subst xs0 xs1 ++ eqs) 
    
    -- check if reducing terms is useful
    cycleOrSolve :: Int -> Term -> Result Substitution
    cycleOrSolve n t
      | notOccursDBL n t = unify sig ctx (Data.Map.insert n t subst) eqs
      | headOccurs n t   = No
      | otherwise        = Stuck eq'
    
    headOccurs :: Int -> Term -> Bool
    headOccurs n (App (DBL m) _)
      | n == m = True
    headOccurs n (App (Con _ _ _ _) xs) = any (headOccurs n) xs
    headOccurs _ _ = False
  