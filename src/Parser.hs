module Parser where

import Formula (Formula (..), Term (..))
import Text.Parsec (alphaNum, letter, oneOf, parse, (<|>))
import Text.ParserCombinators.Parsec (Parser)
import qualified Text.ParserCombinators.Parsec as Parsec
import Text.ParserCombinators.Parsec.Language (emptyDef)
import qualified Text.ParserCombinators.Parsec.Token as Token

languageDef =
  emptyDef
    { Token.commentStart = "(-",
      Token.commentEnd = "-)",
      Token.commentLine = "--",
      Token.identStart = letter <|> oneOf "_",
      Token.identLetter = alphaNum <|> oneOf "_",
      Token.reservedNames =
        [ "Var",
          "Fun",
          "Rel",
          "Prop",
          "And",
          "Not",
          "Or",
          "Implies",
          "Iff",
          -- , "T"
          -- , "F"
          "Exists",
          "Forall"
        ],
      Token.reservedOpNames = ["\"", ",", "[", "]"]
    }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer -- parses an identifier

reserved = Token.reserved lexer -- parses a reserved name

reservedOp = Token.reservedOp lexer -- parses an operator

parens = Token.parens lexer -- parses surrounding parenthesis:
--   parens p
-- takes care of the parenthesis and
-- uses p to parse what's inside them

integer = Token.integer lexer -- parses an integer

semi = Token.semi lexer -- parses a semicolon

whiteSpace = Token.whiteSpace lexer -- parses whitespace

formulaParser :: Parser Formula
formulaParser = whiteSpace >> formula

term :: Parser Term
term =
  parens term
    <|> varTerm
    <|> funTerm

varTerm :: Parser Term
varTerm = do
  reserved "Var"
  reservedOp "\""
  name <- identifier
  reservedOp "\""
  return $ Var name

funTerm :: Parser Term
funTerm = do
  reserved "Fun"
  reservedOp "\""
  f <- identifier
  reservedOp "\""
  ts <- list term
  return $ Fun f ts

list :: Parser a -> Parser [a]
list parser = do
  reservedOp "["
  list <- oneOrMore parser <|> zero
  reservedOp "]"
  return list

zero :: Parser [a]
zero = return []

oneOrMore :: Parser a -> Parser [a]
oneOrMore parser = Parsec.try (more parser) <|> one parser

one :: Parser a -> Parser [a]
one parser = do
  a <- parser
  return [a]

more :: Parser a -> Parser [a]
more parser = do
  a <- parser
  reservedOp ","
  as <- oneOrMore parser
  return $ a : as

relFormula :: Parser Formula
relFormula = do
  reserved "Rel"
  reservedOp "\""
  r <- identifier
  reservedOp "\""
  ts <- list term
  return $ Rel r ts

-- a proposition is just a 0-ary relation
propFormula :: Parser Formula
propFormula = do
  reserved "Prop"
  reservedOp "\""
  r <- identifier
  reservedOp "\""
  return $ Rel r []

formula :: Parser Formula
formula =
  parens formula
    <|> trueFormula
    <|> falseFormula
    <|> relFormula
    <|> propFormula
    <|> notFormula
    <|> andFormula
    <|> orFormula
    <|> impliesFormula
    <|> iffFormula
    <|> existsFormula
    <|> forallFormula

trueFormula :: Parser Formula
trueFormula = do
  reserved "T"
  return T

falseFormula :: Parser Formula
falseFormula = do
  reserved "F"
  return F

notFormula :: Parser Formula
notFormula = do
  reserved "Not"
  Not <$> formula

andFormula :: Parser Formula
andFormula = do
  reserved "And"
  phi <- formula
  And phi <$> formula

orFormula :: Parser Formula
orFormula = do
  reserved "Or"
  phi <- formula
  Or phi <$> formula

impliesFormula :: Parser Formula
impliesFormula = do
  reserved "Implies"
  phi <- formula
  Implies phi <$> formula

iffFormula :: Parser Formula
iffFormula = do
  reserved "Iff"
  phi <- formula
  Iff phi <$> formula

existsFormula :: Parser Formula
existsFormula = do
  reserved "Exists"
  reservedOp "\""
  x <- identifier
  reservedOp "\""
  Exists x <$> formula

forallFormula :: Parser Formula
forallFormula = do
  reserved "Forall"
  reservedOp "\""
  x <- identifier
  reservedOp "\""
  Forall x <$> formula

parseString :: String -> Formula
parseString str =
  case parse formulaParser "" str of
    Left e -> error $ show e
    Right r -> r

parseIntegers :: String -> [Integer]
parseIntegers str =
  case parse (list integer) "" str of
    Left e -> error $ show e
    Right r -> r
