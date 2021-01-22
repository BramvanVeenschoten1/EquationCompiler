module Substitution where

import Utils
import Core
import Data.List
import Data.Map
import Data.Maybe

{- here be substitution and lifting -}

liftFrom :: Int -> Int -> Term -> Term
liftFrom k n = f k where
  f k (App (DBI m) xs)
    | m >= k = App (DBI (m + n)) (fmap (liftFrom k n) xs)
  f k (App head xs) = App head (fmap (liftFrom k n) xs)
  f k (Pi name ta tb) = Pi name (liftFrom k n ta) (liftFrom (k + 1) n tb)
  f k t = t

lift :: Int -> Term -> Term
lift = liftFrom 0

psubst :: [Term] -> Term -> Term
psubst args = f 0 where
  nargs = length args
  
  h k (t @ (DBI n)) args'
    | n >= k + nargs = App (DBI (n - nargs)) args'
    | n < k          = App t args'
    | otherwise      = case lift k (fromMaybe (error "DBI in subst out of range") (nth (n - k) args)) of
      App f args'' -> App f (args'' ++ args')
      pi -> pi
  h _ t args' = App t args'
  
  f k (Type l) = Type l
  f k (App fun args) = h k fun (fmap (f k) args)
  f k (Pi name src dst) = Pi name (f k src) (f (k + 1) dst)

treeSubst :: [Term] -> Tree -> Tree
treeSubst = undefined

subst :: Term -> Term -> Term
subst = psubst . (:[])

instantiateCtor :: [Term] -> Term -> Term
instantiateCtor params t = psubst (reverse params) (dropDomains (length params) t) where
  dropDomains :: Int -> Term -> Term
  dropDomains 0 tb = tb
  dropDomains n (Pi _ _ tb) = dropDomains (n - 1) tb

{- substitute recursive occurrences of inductives or fixpoints for positiviy/termination analysis -}
substWithDummy :: Int -> Term -> Term
substWithDummy block_no = f () where
  f _ (App (Ind obj_id _ upno) args)
    |  obj_id == block_no =
      App (DBL 0) (Data.List.drop upno args)
  f _ (App (Def obj_id _ upno) args)
    | obj_id == block_no =
      App (DBL 0) (fmap (f ()) (Data.List.drop upno args))
  f _ t = Utils.map (const id) () f t