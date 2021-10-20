{-# LANGUAGE PartialTypeSignatures #-}


module TerminationChecking.Parser
  (parse_program)
where

import Control.Monad
import Data.Functor.Identity
import qualified Data.Map as M

import Text.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P

import TerminationChecking.Lang

--
-- Parsec provided language parsing
--

lexer :: Monad m => P.GenTokenParser String st m
lexer =
  P.makeTokenParser
    P.LanguageDef
    { P.commentStart = "{-"
    , P.commentEnd = "-}"
    , P.commentLine = "--"
    , P.nestedComments = True
    , P.identStart = lower
    , P.identLetter = alphaNum
    , P.opStart = oneOf "+-*/&|~<=>"
    , P.opLetter = oneOf "="
    , P.reservedNames = [
      "Left",
      "Right",
      "True",
      "False"
    ]
    , P.reservedOpNames =
        [ "<"
        , "<="
        , ">="
        , "="
        , "+"
        , "-"
        , "*"
        , "/"
        , "~"
        ]
    , P.caseSensitive = True
    }

parens :: Monad m => ParsecT String u m a -> ParsecT String u m a
parens = P.parens lexer

braces :: Monad m => ParsecT String u m a -> ParsecT String u m a
braces = P.braces lexer

identifier :: Monad m => ParsecT String u m String
identifier = P.identifier lexer

reserved :: Monad m => String -> ParsecT String u m ()
reserved = P.reserved lexer

symbol :: Monad m => String -> ParsecT String u m String
symbol = P.symbol lexer

natural :: Monad m => ParsecT String u m Integer
natural = P.natural lexer

comma :: Monad m => ParsecT String u m String
comma = P.comma lexer

--
-- The actual parser
--

parse_program :: String -> Either _ _
parse_program s =
  let ls = lines s
      epats = traverse (parse function_line_parser "") ls
   in 
    collapse_fnlines <$> epats

collapse_fnlines :: [(_, b)] -> M.Map _ [b]
collapse_fnlines =
  foldl
    (\m (fnname, line) -> M.insertWith (\a b -> a ++ b) fnname [line] m)
    M.empty

function_line_parser :: Monad m => ParsecT String u m (String, (Pattern String, Term String))
function_line_parser =
  do
    fnname <- fnname_parser
    args   <- pattern_parser
    _      <- symbol "="
    rest   <- term_parser
    return (fnname, (args, rest))

fnname_parser :: Monad m => ParsecT String u m String
fnname_parser = identifier <?> "fnname"

pattern_parser :: Monad m => ParsecT String u m (Pattern String)
pattern_parser =
  (   (symbol "()" *> return PUnit <?> "pattern unit")
  <|> (parens (
    do
      pa <- pattern_parser
      r <-
        ((do
          _ <- comma
          pb <- pattern_parser
          return $ PPair pa pb) <?> "pattern tuple")
        <|> (return pa <?> "pattern parens")
      return r
  ))
  <|> (parens pattern_parser <?> "pattern parens")
  <|> (symbol "True"  *> return (PBoolLit True)  <?> "pattern True literal")
  <|> (symbol "False" *> return (PBoolLit False) <?> "pattern False literal")
  <|> (symbol "Left"  *> pattern_parser <?> "pattern left sum")
  <|> (symbol "Right"  *> pattern_parser <?> "pattern right sum")
  <|> (symbol "Box"  *> pattern_parser <?> "pattern box")
  <|> ((PNatLit <$> natural) <?> "pattern natural literal")
  <|> (PVar <$> identifier <?> "pattern var")
  ) <?> "pattern"

term_parser :: Monad m => ParsecT String u m (Term String)
term_parser =
  (   (symbol "()" *> return TUnit <?> "term unit")
  <|> (parens (
    do
      pa <- term_parser
      r <-
        ((do
          _ <- comma
          pb <- term_parser
          return $ TPair pa pb) <?> "term tuple")
        <|> (return pa <?> "term parens")
      return r
  ))
  <|> (parens term_parser <?> "term parens")
  <|> (symbol "True"  *> return (TBoolLit True)  <?> "term True literal")
  <|> (symbol "False" *> return (TBoolLit False) <?> "term False literal")
  <|> (symbol "Left"  *> term_parser <?> "term left sum")
  <|> (symbol "Right" *> term_parser <?> "term right sum")
  <|> (symbol "Box"   *> term_parser <?> "term box")
  <|> ((TNatLit <$> natural) <?> "term natural literal")
  <|> (TVar <$> identifier <?> "term var")
  ) <?> "term"
