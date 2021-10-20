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
    , P.reservedNames =
      [ "Left"
      , "Right"
      , "True"
      , "False"
      , "Box"
      , "if"
      , "then"
      , "else"
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
    args   <- toplevel_pattern_parser
    _      <- symbol "="
    rest   <- term_parser
    return (fnname, (args, rest))

fnname_parser :: Monad m => ParsecT String u m String
fnname_parser = identifier <?> "fnname"

toplevel_pattern_parser :: Monad m => ParsecT String u m (Pattern String)
toplevel_pattern_parser =
  (do
    ps <- many1 pattern_parser
    return (case ps of
              p:[] -> p
              p:ps -> foldr PPair p ps)
  ) <?> "term"

pattern_parser :: Monad m => ParsecT String u m (Pattern String)
pattern_parser =
  (   try ((symbol "()" *> return PUnit) <?> "pattern unit")
  <|> (do
        _ <- symbol "("
        ps <- sepBy1 pattern_parser comma
        _ <- symbol ")"
        return
          (case ps of
            p:[] -> p -- parens
            p:ps -> foldr PPair p ps)) -- tuple
  <|> try (symbol "True"  *> return (PBoolLit True)  <?> "pattern True literal")
  <|> try (symbol "False" *> return (PBoolLit False) <?> "pattern False literal")
  <|> try (symbol "Left"  *> pattern_parser <?> "pattern left sum")
  <|> try (symbol "Right" *> pattern_parser <?> "pattern right sum")
  <|> try (symbol "Box"   *> pattern_parser <?> "pattern box")
  <|> ((PNatLit <$> natural) <?> "pattern natural literal")
  <|> (PVar <$> identifier <?> "pattern var")
  ) <?> "pattern"

term_parser :: Monad m => ParsecT String u m (Term String)
term_parser =
  (do
    ts <- many1 single_term_parser
    return (case ts of
              t:[] -> t
              t:ts -> foldl TApp t ts)
  ) <?> "term"

single_term_parser :: Monad m => ParsecT String u m (Term String)
single_term_parser =
  (   try ((symbol "()" *> return TUnit) <?> "term unit")
  <|> (do
        _ <- symbol "("
        ts <- sepBy1 term_parser comma
        _ <- symbol ")"
        return
          (case ts of
            t:[] -> t -- parens
            t:ts -> foldr TPair t ts)) -- tuple
  <|> ((TIf <$>
        try (symbol "if"   *> term_parser) <*>
        try (symbol "then" *> term_parser) <*>
        try (symbol "else" *> term_parser)) <?> "term if-then-else")
  <|> try (TBoolLit <$> (symbol "False" *> return False) <?> "term False literal")
  <|> try (TBoolLit <$> (symbol "True"  *> return True) <?> "term True literal")
  <|> try (TSumL    <$> (symbol "Left"  *> term_parser) <?> "term left sum")
  <|> try (TSumR    <$> (symbol "Right" *> term_parser) <?> "term right sum")
  <|> try (TBox     <$> (symbol "Box"   *> term_parser) <?> "term box")
  <|> try (TUnbox   <$> (symbol "Unbox" *> term_parser) <?> "term unbox")
  <|> (TNatLit  <$> natural <?> "term natural literal")
  <|> (TVar     <$> identifier <?> "term var")
  <|> (TLambda  <$> try (symbol "\\" *> identifier) <*> try (symbol "->" *> term_parser) <?> "term lambda")
  ) <?> "term single"