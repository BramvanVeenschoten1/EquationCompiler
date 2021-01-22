module Prettyprint where

import Lexer(Loc)
import Parser(Binder(..))
import Core
import Utils

import Data.Maybe
import Data.Map
import Data.List

showMap :: (Show k, Show v) => Map k v -> String
showMap m = intercalate "\n" entries where
  entries = fmap showEntry (toList m)
  showEntry (dbl,val) = show dbl ++ " => " ++ show val

instance Show Term where
  show = showTerm []

showSubst :: Substitution -> String
showSubst subst = intercalate "\n" entries where
  entries = fmap showEntry (toList subst)
  showEntry (dbl,val) = show dbl ++ " <- " ++ showTerm [] val

showCaseTree :: Tree -> String
showCaseTree (Lam body) = '\\' : showCaseTree body
showCaseTree (Body t) = showTerm [] t
showCaseTree (Case n alts) = "case " ++ show n ++ "{" ++ intercalate "; " (zipWith showAlt [0..] alts) ++ "}" where
  showAlt n alt = show n ++ " => " ++ showCaseTree alt
showCaseTree (Refuted n) = '{' : show n ++ "}"

showTerm :: Context -> Term -> String
showTerm ctx x = case x of
  Type _ -> "Type"
  App f xs -> showHead ctx f ++ " " ++ intercalate " " (fmap (showArg ctx) xs)
  Pi "" ta tb -> bracePi ta (showTerm ctx ta) ++ " -> " ++ showTerm (("",ta):ctx) tb where
  Pi s ta tb -> "Pi " ++ s ++ " : " ++ bracePi ta (showTerm ctx ta) ++ ", " ++ showTerm ((s,ta):ctx) tb where

  where
    embrace x = "(" ++ x ++ ")"
    
    bracePi (Pi _ _ _) = embrace
    bracePi _          = id
    
    braceApp (App _ (_:_)) = embrace
    braceApp _         = id
    
    showVar p n m = case nth n ctx of
      Just ((x @ (_:_)),_) -> x -- ++ "_" ++ show m
      _ -> p : show m
    
    showHead ctx (DBI n)       = showVar '$' n n
    showHead ctx (DBL n)       = showVar '#' (length ctx - n - 1) n
    showHead ctx (Def i j _)   = show (i,j)
    showHead ctx (Con i j k _) = show (i,j,k)
    showHead ctx (Ind i j _)   = show (i,j)
    
    showArg ctx t = braceApp t (showTerm ctx t)
    
showContext :: Context -> String
showContext [] = ""
showContext ((name,ty):ctx) = showContext ctx ++ "\n" ++ name ++ " : " ++ showTerm ctx ty

showQName :: [String] -> String
showQName = intercalate "."