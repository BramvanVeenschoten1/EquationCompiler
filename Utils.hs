module Utils where

import Core

import Data.List
import Data.Maybe
import Data.Map hiding (foldr)

{- based on the matita kernel -}
{- here we have utilities for iterating over core terms -}

debug :: Bool
debug = True

nth :: Int -> [a] -> Maybe a
nth 0 (x : _) = Just x
nth n (_ : xs) = nth (n-1) xs
nth _ _ = Nothing

mkDBL k = App (DBL k) []

noSubst :: Substitution
noSubst = Data.Map.empty

notOccursDBL :: Int -> Term -> Bool
notOccursDBL n (Pi name src dst) = notOccursDBL n src && notOccursDBL n dst
notOccursDBL n (App head args) =
  head /= DBL n && all (notOccursDBL n) args

fold :: ((String,Term) -> k -> k) -> k -> (k -> Term -> a -> a) -> Term -> a -> a
fold push ctx f t acc = case t of
  App fun args -> foldr (f ctx) acc args
  Pi  name src dst -> f ctx src (f (push (name,src) ctx) dst acc) 

map :: ((String,Term) -> k -> k) -> k -> (k -> Term -> Term) -> Term -> Term
map push ctx f t = case t of
  App fun args -> App fun (fmap (f ctx) args)
  Pi name src dst -> Pi name (f ctx src) (f (push (name,src) ctx) dst)

{- get the largest number of parameters that are uniformly applied to all recursive occurences -}
{- may be useable for fixpoints as well?
   => must be adapted for nested calls, eg:
      f x (f y)
-}
getUniparamno :: Term -> Int -> Int
getUniparamno = f 0 where
  eatArgs n (App (DBL m) [] : args) acc
    | n == m = eatArgs (n - 1) args (acc + 1)
  eatArgs _ _ acc = acc

  f k (App (DBL m) args) acc
    | m >= k = min acc (eatArgs (k - 1) args 0)
  f k t a = Utils.fold (const (+1)) k f t a