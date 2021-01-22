module Core where

import Data.Map

{-
  introduce temporary names for fixpoints currently in the
  elaborator? Or just use meta's?
  useful for:
  - having names that are typed but non-reducible
  - termination checks
  - positivity checks
  - lifting local definitions
  - lifting case expressions
  
  distinguish non-recursive definitions?
  
  are inductive blocks necessary for positivity checks?
  are fixpoint blocks necessary for termination checks?
  => both have a notion of uniform parameters
  => yes
  
-}

data Head
  = DBI  Int
  | DBL  Int           
  | Def  Int Int Int     -- obj_id, defno, uniparamno
  | Ind  Int Int Int     -- obj_id, defno, uniparamno
  | Con  Int Int Int Int -- obj_id, defno, ctorno, paramno
  deriving (Eq, Ord)

data Term
  = Type Int
  | App  Head [Term]
  | Pi   String Term Term

data Tree
  = Lam     Tree
  | Body    Term
  | Case    Int [Tree]
  | Refuted Int

data Inductive = Inductive {
  indSort    :: Term,
  paramno    :: Int,                 -- is computable from unroll Pi
  introRules :: [(String,Int,Term)]} -- [(name, arity, ty)]
  
type Definition = (Term,Tree) -- type, body

data Signature = Signature {
  sigInd :: Map Int [Inductive],
  sigDef :: Map Int [Definition]}

type Context = [(String, Term)]

type Substitution = Map Int Term 