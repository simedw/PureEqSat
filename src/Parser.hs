module Parser where

import Expr


import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Prim


tok :: TokenParser st
tok = makeTokenParser LanguageDef
  { commentStart    = "{-"
  , commentEnd      = "-}"
  , commentLine     = "--"
  , nestedComments  = True
  , identStart      = letter   
  , identLetter     = alphaNum <|> oneOf "_'."
  , opStart         = oneOf "+-*/%<>=_"
  , opLetter        = oneOf "+-*/%<>=_"
  , reservedNames   = []
  , reservedOpNames = []
  , caseSensitive   = True
  }

type Var = String
type Program = [Function]

type Function = (Var, Expr)

type P = GenParser Char ()

parseExpr :: String -> Either ParseError Program
parseExpr = runParser program () ""

program :: P Program 
program = do 
    whiteSpace tok
    v <- sepBy scdef (many newline)
    eof
    return v

ident :: P String
ident = identifier tok

scdef :: P Function 
scdef = do
    name <- ident
    reservedOp tok "="
    body <- expr -- object
    return $ (name, body)

expr :: P Expr
expr = buildExpressionParser table expr' 
  where
    table :: OperatorTable Char () Expr
    table = 
       [ [ "*" --> (*.)]
       , [ "+" --> (+.)]
       , [ "&&" --> eAnd]
       , [ "||" --> eOr]
       , [ "==" --> (==.)]
       ]
    name --> op = Infix (reservedOp tok name >> return op) AssocLeft


expr' :: P Expr
expr' = iff <|> expr'2

iff :: P Expr
iff = do
    reserved tok "if"
    a <- expr
    reserved tok "then"
    b <- expr
    reserved tok "else"
    c <- expr
    return $ eIf a b c

expr'2 = parens tok expr <|> ebool <|> literal <|> var

ebool = ebool' True <|> ebool' False
  where ebool' b = reserved tok (show b) >> return (eBool b)

literal = eInt `fmap` natural tok

var = eVar `fmap` ident
 
