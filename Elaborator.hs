module Elaborator where

import Core as C

import Prelude hiding (lookup)
import Data.List hiding (lookup, insert)
import Control.Monad
import Control.Applicative hiding (Const)
import Data.Functor
import Data.Map
import Data.Either
import Data.Maybe

import Prettyprint
import Lexer(Loc)
import Substitution
import Parser
import Core

err = Left

type Error = String

type NameSpace = (Map Name [QName], Map QName (Loc, Head))

type GlobalNames = Map Name NameSpace

mergeNameSpace :: NameSpace -> NameSpace -> NameSpace
mergeNameSpace (n0,q0) (n1,q1) = (Data.Map.unionWith (++) n0 n1, Data.Map.union q0 q1)

emptyNameSpace :: NameSpace
emptyNameSpace = (Data.Map.empty,Data.Map.empty)

emptyObjects = Signature Data.Map.empty Data.Map.empty

lookupQName :: QName -> ElabState -> Maybe (Loc,Head)
lookupQName qname glob = lookup qname (Data.Map.union (snd (internalNames glob)) (snd (importedNames glob)))

lookupName :: Name -> ElabState -> Maybe [QName]
lookupName name glob = lookup name (unionWith (++) (fst (importedNames glob)) (fst (internalNames glob)))

ensureUnique :: ElabState -> QName -> Either Error ()
ensureUnique st qname = case lookupQName qname st of
  Nothing -> pure ()
  Just (info,_) -> Left (showQName qname ++ " is already defined here:\n" ++ show info)

updateNameSpace :: [(QName, Loc, Head)] -> NameSpace -> NameSpace
updateNameSpace names (shorts,longs) = let
  shorts' = Data.List.foldr (\(qname,_,_) -> insertWith (++) (last qname) [qname]) shorts names
  longs' = Data.List.foldr (\(qname,loc,ref) -> Data.Map.insert qname (loc,ref)) longs names
  in (shorts', longs')

data ElabState = ElabState {
  newName       :: Int,
  moduleName    :: Name,
  importedNames :: NameSpace,
  internalNames :: NameSpace,
  signature     :: Signature}