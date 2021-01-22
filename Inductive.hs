module Inductive where

import Data.Set
import Data.Map
import Data.List
import Data.Maybe
import Control.Monad
import Control.Applicative hiding (Const)

import qualified Core as C
import Core hiding (Inductive,Fixpoint)
import Elaborator
import Utils
import Substitution
import Parser
import Lexer(Loc)
import Prettyprint
import Normalization
import Debug.Trace

{-
  Cue from LEAN:
  - Parameters must be smaller or equal to arity
  - nested types must be smaller than arity
    => constructor types must be smaller than arity
  Q: does this imply there is a use for non-uniform parameters?
  1. a notion of non-uniform parameters is only of use for
     (mutually) recursive datatypes
  2. a non-uniform parameter does not imply a recursive constructor
     must embed a type, example:
     
     data foo (A : Type): Type where
       nil  : foo A
       cons : A -> foo (Pair A A) -> foo A
  3. With non-uniform parameters, the above type can remain as small
     as its parameter, therefore allowing nesting.
  4. Therefore being useful
  5. QED.
  I:
  now that indices are a thing, extra checks are needed:
  1. An inductive type being defined may not occur in the indices
     of its constructors
  2. semi-important only for compatibility with impredicativity:
     When checking the positivity of a nested data type, 
     the uniform parameter that receives the data type must not occur
     in the parameters.     
-}

assert :: Bool -> String -> Either Error ()
assert True _ = pure ()
assert False msg = Left msg

{-
  check if the constructor embeds inhabitants of Box
  should not include data parameters

  Since data declarations are top-level and do not do any splitting,
  a substitution is not needed
-}

allOccurrencesPositive :: Signature -> Context -> Loc -> Int -> Int -> Int -> Int -> Int -> Term -> Either Error ()
allOccurrencesPositive st ctx loc defcount defno paramno n nn t = f (reduce st noSubst t) where
  f (Pi name ta tb) = do
    let ctx' = (name,ta) : ctx
    
    if doesNotOccur ctx' 0 0 tb
    then strictlyPositive st ctx loc n nn ta
    else assert (doesNotOccur ctx n nn ta) (show loc ++ "Recursive arguments may not be depended upon")
         
    allOccurrencesPositive st ctx' loc defcount defno paramno (n+1)(nn+1) tb
  f (tb @ (App head args)) = h head (g (length ctx) paramno args tb)
  
  g depth 0 args tb = pure ()
  g depth pno (App (DBI n) [] : args) tb
    | n == depth - defcount - paramno + pno - 1 = g depth (pno - 1) args tb
  g depth pno (arg:_) tb = do
    Left (
      show loc ++
      showContext ctx ++ "\n" ++
      "Expected occurrence of parameter:\n" ++
      showTerm ctx (App (DBI (depth - defcount - paramno + pno - 1)) []) ++
      "\nBut got:\n" ++
      showTerm ctx arg)
  
  h (DBI n) c
    | n == length ctx - defno - 1 = c
  h x _ = Left (
    show loc ++ 
    showContext ctx ++
    "Head of constructor return type must be the datatype being defined, but is:\n" ++
    showTerm ctx (App x []))
  

strictlyPositive :: Signature -> Context -> Loc -> Int -> Int -> Term -> Either Error ()
strictlyPositive st ctx loc n nn t = f (reduce st noSubst t) where
  f t | doesNotOccur ctx n nn t = pure ()
  f (Pi name ta tb) = do
    assert (doesNotOccur ctx n nn ta)
           (show loc ++ "Recursive occurrence in negative position")
  
    strictlyPositive st ((name,ta) : ctx) loc (n+1) (nn+1) tb
  f (App (Ind obj_id _ uniparamno) args) = do
    let (left_params,right_params) = Data.List.splitAt uniparamno args
        block = fromJust (Data.Map.lookup obj_id (sigInd st))
        ctors = concat (fmap introRules block)
        ctors' = fmap (\(_,_,ty) -> instantiateCtor left_params ty) ctors

    assert (all (doesNotOccur ctx n nn) right_params)
           (show loc ++ "Recursive occurrence may only be in uniform parameters of a previously defined inductive type")
    
    mapM_ (weaklyPositive st ctx loc n nn obj_id) ctors'
  f (App fun args) = 
    assert (all (doesNotOccur ctx n nn) args)
           (show loc ++ "Cannot determine strict positivity of recursive occurrence in function call")
  f _ = Left (show loc ++ "Strict positivity check wildcard error")
{- 
   why does matita:
   - disallow nesting in mutual types?
   - disallow deeper levels of nesting?
   - add the inspected type to the context?
   => we'll ignore these
-}
weaklyPositive :: Signature -> Context -> Loc -> Int -> Int -> Int -> Term -> Either Error ()
weaklyPositive st ctx loc n nn block_no t = f ctx n nn (substWithDummy block_no t) where
  f :: Context -> Int -> Int -> Term -> Either Error ()
  f ctx n nn te = case reduce st noSubst te of
    App _ args ->
      assert (all (doesNotOccur ctx n nn) args)
             (show loc ++ "Recursive occurrence may only be in uniform parameters of a previously defined inductive type")
    Pi name ta tb -> do
      let ctx' = (name,ta) : ctx
      f ctx' (n+1) (nn+1) tb
      if doesNotOccur ctx' 0 0 tb
      then strictlyPositive st ctx loc n nn ta
      else  assert (doesNotOccur ctx n nn ta)
                   (show loc ++ "Recursive occurrence in negative position")

doesNotOccur :: Context -> Int -> Int -> Term -> Bool
doesNotOccur ctx n nn t = f 0 t True where
  f _ _ False = False
  f k (App (DBI m) _) _
    | m >= n + k && m <= nn + k = False
    | m < k && m > nn + k = True
    | otherwise = True
  f k t _ = Utils.fold (const (+1)) k f t True