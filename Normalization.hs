module Normalization where

import Data.Map
import Data.List(lookup,intercalate, elemIndex,foldl)
import Data.Maybe
import Data.Function
import Core
import Substitution
import Utils
import Debug.Trace
import Prettyprint

{- here we evalutate terms and test their equality -}

reduce :: Signature -> Substitution -> Term -> Term
reduce sig subst = f [] where
  f stack (App x xs) = g (fmap (f stack) xs ++ stack) x
  f stack p = p

  g stack (t @ (DBL n)) =
    fromMaybe (App t stack) (f stack <$> Data.Map.lookup n subst)
  g stack (t @ (Def n i _)) =
    h [] stack (snd (fromJust (Data.Map.lookup n (sigDef sig)) !! i)) (App t stack)
  g stack t = App t stack

  h env (s : stack) (Lam t)       fail = h (s : env) stack t fail
  h env      stack  (Body t)      fail = f stack (psubst env t)
  h env      stack  (Case n alts) fail = case nth n env of
    Just (App (Con _ _ k pno) ys) ->
      h (reverse (Prelude.drop pno ys) ++ env) stack (alts !! k) fail
    --Just x -> trace (showTerm [] x) fail
    --Nothing -> h' n env stack fail
    _ -> fail
  h _ _ _ fail = fail
    
  h' n env stack fail = trace (
    "\ndepth:\n" ++
    show n ++
    "\nenv:\n" ++
    intercalate "\n" (fmap (showTerm []) env) ++
    "\nstack:\n" ++
    intercalate "\n" (fmap (showTerm []) stack)) fail

{-
  compare DBIs and DBLs directly
-}
convertible :: Signature -> Substitution -> Int -> Term -> Term -> Bool
convertible sig subst k t0 t1 = alpha_t t0 t1 || machine_t t0 t1 where
  alpha_t (Pi n src0 dst0) (Pi _ src1 dst1) =
    convertible sig subst k src0 src1 &&
    convertible sig subst (k + 1) dst0 dst1
  alpha_t (App h0 xs0) (App h1 xs1) =
    (h0 == h1 || varEq h0 h1) &&
    and (zipWith (convertible sig subst k) xs0 xs1)
  alpha_t (Type l0) (Type l1) = l0 == l1
  alpha_t _ _ = False
  
  varEq (DBI n0) (DBL n1) = n0 == k - n1 - 1
  varEq (DBL n1) (DBI n0) = n0 == k - n1 - 1
  varEq _        _        = False

  machine_t t0 t1 = alpha_t
    (reduce sig subst t0)
    (reduce sig subst t1)