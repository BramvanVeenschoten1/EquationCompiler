module Parser where

import Lexer
import Control.Applicative
import Data.List
import Data.Function
import Data.Array.Unboxed
import Data.Maybe

type Name = String
type QName = [String]

data Binder = Binder {binderLoc :: Loc, binderName :: Name}

instance Eq Binder where
  (==) = on (==) binderName

instance Ord Binder where
  compare = on compare binderName

instance Show Binder where
  show = binderName

type Param = (Binder, Maybe Expr)

type Ctor = (Binder, Expr)

type Inductive = (Loc, Binder, [Param], Expr, [Ctor])

data Pattern
  = PAbsurd
  | PIgnore
  | PVar Loc String
  | PApp Loc [String] [Pattern]

instance Show Pattern where
  show PAbsurd = "()"
  show PIgnore = "_"
  show (PVar _ x) = x
  show (PApp _ x xs) = intercalate "." x ++ " " ++ intercalate " " (fmap showArg xs) where
    showArg (p @ (PApp _ _ _)) = "(" ++ show p ++ ")"
    showArg p = show p

type Clause = ([Pattern], Expr)

type Function = (Loc, Binder, Expr, [Clause])

type Module = (String,[String],[Decl])

type Branch = (Loc,Binder,[Binder],Expr)

data Decl 
  = Inductive [Inductive]
  | Definition [Function]

data EHead
  = EName   Loc [String]
  | EVar    Loc String

data Expr 
  = EType   Loc
  | EApply  Loc EHead [Expr]
  | EPi     Loc (Maybe Binder) Expr Expr

exprLoc (EApply s _ _) = s
exprLoc (EPi s _ _ _) = s
exprLoc (EType s) = s

mkBinder :: (Loc,String) -> Binder
mkBinder = uncurry Binder

isPrimary :: Parser Bool
isPrimary = do
  t <- peek token
  pure $ case t of
    Symbol _     -> True
    Pct "_"      -> True
    Pct "Type"   -> True
    Pct "Pi"     -> True
    Pct "("      -> True
    _            -> False 

parseHead :: Cursor -> String -> Parser EHead
parseHead begin x = do
  t <- peek token
  case t of
    Pct "." -> do
      xs  <- qname
      end <- getCursor
      loc <- makeLoc begin end
      pure (EName loc (x:xs))
      where
        qname = do
          token
          x <- expectSymbol "symbol after '.' in qualified name"
          t <- peek token
          case t of
            Pct "." -> do
              xs <- qname
              pure (x:xs)
            _ -> pure [x]
    _ -> do
      end <- getCursor
      loc <- makeLoc begin end
      pure (EVar loc x)

annot :: Parser (Maybe Expr)
annot = do
  t <- peek token
  case t of
    Pct ":" -> token *> fmap Just expr
    _ -> pure Nothing

annotParam :: Parser [Param]
annotParam = do
  bs <- some (mkBinder <$> spanned (expectSymbol "name in parameter list"))
  ty <- annot
  pure (fmap (\b -> (b,ty)) bs)

param :: Parser [Param]
param = do
  t <- peek token
  case t of
    Pct "(" -> token *> annotParam <* f ")"
    Pct "{" -> token *> annotParam <* f "}"
    _ -> annotParam
  where f close = expect close ("closing '" ++ close ++ "' after parameter")

params :: Parser [Param]
params = do
  t <- peek token
  case t of
    Symbol _ -> someParams 
    Pct "(" -> someParams
    Pct "{" -> someParams
    _ -> pure []
  
someParams :: Parser [Param]
someParams = (++) <$> param <*> params

parseProduct :: Cursor -> Parser Expr
parseProduct begin = do
  ps <- someParams
  expect "," "',' after params in Pi expression"
  body <- expr
  end <- getCursor
  span <- makeLoc begin end
  if all (\(_,ta) -> isJust ta) ps
  then pure ()
  else err2 span "parameters in Pi expressions must have type annotations"
  let f (v,Just ta) = EPi span (Just v) ta
  pure (foldr f body ps)

primary :: Bool -> Parser Expr
primary closed = do
  ws
  begin   <- getCursor
  (loc,t) <- spanned token
  case t of
    Pct "(" -> do
      e <- expr
      expect ")" "closing ')' after expression"
      pure e
    Pct "Type" -> do
      pure (EType loc)
    Pct "Pi" -> do
      parseProduct begin
    Symbol x -> do
      head <- parseHead begin x
      args <- if closed then pure [] else parseArgs
      end  <- getCursor
      loc  <- makeLoc begin end
      pure (EApply loc head args)
      where
      parseArgs = do
        b <- isPrimary
        if b then (:) <$> primary True <*> parseArgs else pure []
    x -> err loc "some expression" (show x)

arrow :: Parser Expr
arrow = do
  ws
  begin <- getCursor
  lhs   <- primary False
  t     <- peek token
  case t of
    Pct "->" -> f begin lhs
    _ -> return lhs
    where
      f begin lhs = do
        token
        rhs <- arrow
        end <- getCursor
        span <- makeLoc begin end
        return (EPi span Nothing lhs rhs)

expr :: Parser Expr
expr = arrow

constructors :: Parser [Ctor]
constructors = do
  t <- peek token
  case t of
    Pct "|" -> do
      token
      name <- mkBinder <$> spanned (expectSymbol "name in constructor definition")
      expect ":" "':' after name in constructor definition"
      ty <- expr
      ctors <- constructors
      pure ((name, ty) : ctors)
    _ -> pure []

inductive :: Cursor -> Parser [Inductive]
inductive begin = do
  name <- mkBinder <$> spanned (expectSymbol "name in inductive definition")
  ps <- params
  expect ":" "':' name after parameters in inductive definition"
  arity <- expr
  ctors <- constructors
  end <- getCursor
  span <- makeLoc begin end
  let res = (span, name, ps, arity, ctors)
  ws
  begin <- getCursor
  t <- peek token
  case t of
    Pct "and" -> (:) res <$> (token *> inductive begin)
    _ -> pure [res]

parseAppPattern :: Parser Pattern
parseAppPattern = do
  begin <- getCursor
  x <- expectSymbol "constructor name in application pattern"
  head <- parseHead begin x
  args <- parsePatterns
  end <- getCursor
  span <- makeLoc begin end
  case (head,args) of
    (EVar loc name, []) -> pure (PVar loc name)
    (EVar loc name,args) -> pure (PApp loc [name] args)
    (EName loc names, args) -> pure (PApp loc names args)
  where
    pats = do
      t <- peek token
      case t of
        Symbol _ -> pat
        Pct "(" -> pat
        _ -> pure []
    
    pat = (:) <$> parseClosedPattern <*> pats
      
parseClosedPattern :: Parser Pattern
parseClosedPattern = do
  begin <- getCursor
  t <- token
  case t of
    Pct "(" -> do
      app <- parseAppPattern
      expect ")" "closing ')' after pattern"
      pure app
    Pct "_" -> pure PIgnore
    Symbol x -> do
      sym <- parseHead begin x
      case sym of
        EVar span x -> pure (PVar span x)
        EName span xs -> pure (PApp span xs [])

parsePatterns :: Parser [Pattern]
parsePatterns = do
  t <- peek token
  case t of
    Symbol _ -> pat
    Pct "("  -> pat
    Pct "_"  -> pat
    _ -> pure []
  where
    pat = (:) <$> parseClosedPattern <*> parsePatterns

parseClauses :: Parser [Clause]
parseClauses = do
  t <- peek token
  case t of
    Pct "|" -> do
      token
      pats <- parsePatterns
      (span,t) <- spanned token
      case t of
        Pct "=" -> expr >>= f pats
        Pct "()" -> f pats (error "rhs of absurd clause may not be inspected")
        _ -> err span "'=' or '()' after patterns in clause" (show t)
    _ -> pure []
  where
    f pats body = do
      clauses <- parseClauses
      pure ((pats, body) : clauses)

parseDefinition :: Parser Function
parseDefinition = do
  begin <- getCursor
  name <- mkBinder <$> spanned (expectSymbol "name in function definition")
  expect ":" "':' after name in function definition"
  ty <- expr
  clauses <- parseClauses
  end <- getCursor
  span <- makeLoc begin end
  pure (span, name, ty, clauses)

parseDefinitions :: Parser [Function]
parseDefinitions = do
  def <- parseDefinition
  t <- peek token
  case t of
    Pct "and" -> do
      token
      defs <- parseDefinitions
      pure (def : defs)
    _ -> pure [def]

parseDecls :: Parser [Decl]
parseDecls = do
  ws
  begin <- getCursor
  (span,t) <- spanned token
  case t of
    Pct ""     -> pure []
    Pct "def"  -> f (Definition <$> parseDefinitions)
    Pct "data" -> f (Inductive <$> inductive begin)
    x -> err span "some declaration" (show x)
    where f p = (:) <$> p <*> parseDecls

parseImports = do
  t <- peek token
  case t of
    Pct "import" -> do
      token
      name <- expectSymbol "name after 'import'"
      names <- parseImports
      pure (name:names)
    _ -> pure []

parseModule :: Parser Module
parseModule = do
  expect "module" "module name declaration"
  name <- expectSymbol "name after 'module'"
  imports <- parseImports
  decls <- parseDecls
  pure (name,imports,decls)

parse :: Filename -> String -> Either ParseError Module
parse name input = fst <$> Lexer.parse parseModule name (listArray (0,length input - 1) input) (Cursor 0 0 0 0)
