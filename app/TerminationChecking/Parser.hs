
module TerminationChecking.Parser
  (Prog, parse_program)
where

import Control.Monad
import Control.Applicative
import Data.Bifunctor (first, second)
import Data.Functor.Identity
import qualified Data.Map as M
import Text.Parsec (ParsecT, (<?>), try, many1, sepBy1, oneOf, parse, alphaNum, lower)
import qualified Text.ParserCombinators.Parsec.Token as P

import Debug.Trace (traceShowId)

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
    , P.opLetter = oneOf "+-*/&|~<=>"
    , P.reservedNames =
      [ "Left"
      , "Right"
      , "True"
      , "False"
      , "Roll"
      , "if"
      , "then"
      , "else"
      ]
    , P.reservedOpNames = []
    , P.caseSensitive = True
    }

parens :: Monad m => ParsecT String u m a -> ParsecT String u m a
parens = P.parens lexer

braces :: Monad m => ParsecT String u m a -> ParsecT String u m a
braces = P.braces lexer

float :: Monad m => ParsecT String u m Double
float = P.float lexer

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

operator :: Monad m => ParsecT String u m String
operator = P.operator lexer

--
-- The actual parser
--

type Prog = M.Map String (FunDef String)

parse_program :: String -> Either String Prog
parse_program s =
  lines s
  |> filter (\s -> s /= "" && not (s !! 0 == '-' && s !! 1 == '-'))
  |> traverse (parse function_line_parser "")
  |> first show
  |> (>>= (traverse (\(n,(pat,t)) ->
        case pattern_dup_vars pat of
          [] -> Right (n,(pat,t))
          vs -> Left ("Repeated vars in function \""++n++"\": "++show vs))))
  |> second collapse_fnlines

collapse_fnlines :: Ord v => [(v, b)] -> M.Map v [b]
collapse_fnlines =
  foldl
    (\m (fnname, line) -> M.insertWith (\a b -> a ++ b) fnname [line] m)
    M.empty

function_line_parser :: Monad m => ParsecT String u m (String, (Pattern String, Term String))
function_line_parser =
  do
    fnname <- fnname_parser
    args   <- (foldr1 PPair <$> many1 pattern_parser) <?> "patterns"
    _      <- symbol "="
    rest   <- term_parser
    return (fnname, (args, rest))

fnname_parser :: Monad m => ParsecT String u m String
fnname_parser = identifier <?> "fnname"

pattern_parser :: Monad m => ParsecT String u m (Pattern String)
pattern_parser =
  (  try (symbol "()" *> return PUnit <?> "pattern unit")
  <|> (do
        _ <- symbol "("
        ts <- sepBy1 pattern_parser comma
        _ <- symbol ")"
        return $ foldr1 PPair ts)
  <|> (symbol "True"  *> return (PBoolLit True)  <?> "pattern True literal")
  <|> (symbol "False" *> return (PBoolLit False) <?> "pattern False literal")
  <|> (symbol "Left"  *> (PSumL <$> pattern_parser) <?> "pattern left sum")
  <|> (try (symbol "Right" *> (PSumR <$> pattern_parser) <?> "pattern right sum"))
  <|> (symbol "Roll"   *> (PRoll <$> pattern_parser) <?> "pattern box")
  <|> ((PNatLit <$> natural) <?> "pattern natural literal")
  <|> (PVar <$> identifier <?> "pattern var")
  ) <?> "pattern"

term_parser :: Monad m => ParsecT String u m (Term String)
term_parser =
  (do
    ts <- many1 single_term_parser
    return (case ts of
              t:[] -> t
              t:ts -> TApp t (foldr1 TPair ts))
  ) <?> "term"

single_term_parser :: Monad m => ParsecT String u m (Term String)
single_term_parser =
  (   try ((symbol "()" *> return TUnit) <?> "term unit")
  <|> (do
        _ <- symbol "("
        ts <- sepBy1 term_parser comma
        _ <- symbol ")"
        return $ foldr1 TPair ts)
  <|> ((TIf <$>
        try (symbol "if"   *> term_parser) <*>
        try (symbol "then" *> term_parser) <*>
        try (symbol "else" *> term_parser)) <?> "term if-then-else")
  <|> ((TPChoice . toRational <$>
        try (symbol "pchoice" *> braces float) <*>
        try (symbol "then"    *> term_parser) <*>
        try (symbol "else"    *> term_parser)) <?> "term pchoice")
  <|> try (TBoolLit <$> (symbol "False" *> return False) <?> "term False literal")
  <|> try (TBoolLit <$> (symbol "True"  *> return True) <?> "term True literal")
  <|> try (TSumL    <$> (symbol "Left"  *> term_parser) <?> "term left sum")
  <|> try (TSumR    <$> (symbol "Right" *> term_parser) <?> "term right sum")
  <|> try (TRoll    <$> (symbol "Roll"   *> term_parser) <?> "term roll")
  <|> (TNatLit <$> natural <?> "term natural literal")
  <|> (TVar    <$> identifier <?> "term var")
  <|> (TOp     <$> operator <?> "term operator")
  -- <|> (TLambda <$> try (symbol "\\" *> identifier) <*> try (symbol "->" *> term_parser) <?> "term lambda")
  ) <?> "term single"