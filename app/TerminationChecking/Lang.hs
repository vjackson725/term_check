
module TerminationChecking.Lang where

import qualified Data.Map as M

import Debug.Trace

(|>) x f = f x
infixl 1 |>

data Term v =
  TVar v |
  TOp v |
  TUnit |
  TBoolLit Bool |
  TNatLit Integer |
  TPair (Term v) (Term v) |
  TIf (Term v) (Term v) (Term v) |
  TLambda v (Term v) |
  TApp (Term v) (Term v) |
  TSumL (Term v) |
  TSumR (Term v) |
  TBox (Term v) |
  TUnbox (Term v)
  deriving (Eq, Show)

tlet :: v -> (Term v) -> (Term v) -> (Term v)
tlet x s t = TApp (TLambda x t) s

data Pattern v =
  PVar v |
  PUnit |
  PBoolLit Bool |
  PNatLit Integer |
  PPair (Pattern v) (Pattern v) |
  PSumL (Pattern v) |
  PSumR (Pattern v) |
  PBox (Pattern v)
  deriving (Eq, Show)

{-
  Functions are a name paired with a pattern/body list.
  Patterns will be evaluated in order.
-}
type FunDef v = [(Pattern v, Term v)]

pattern_count_vars :: Ord v => Pattern v -> M.Map v Int -> M.Map v Int
pattern_count_vars (PVar x) m = M.insertWith (\_ -> (+1)) x 0 m
pattern_count_vars PUnit m = m
pattern_count_vars (PPair p0 p1) m =
  m |> pattern_count_vars p0 |> pattern_count_vars p1
pattern_count_vars (PNatLit n)  m = m
pattern_count_vars (PBoolLit n) m = m
pattern_count_vars (PSumL p) m = pattern_count_vars p m
pattern_count_vars (PSumR p) m = pattern_count_vars p m
pattern_count_vars (PBox p)  m = pattern_count_vars p m

pattern_dup_vars :: (Show v, Ord v) => Pattern v -> [v]
pattern_dup_vars p = pattern_count_vars p M.empty |> M.filter (>0) |> M.keys
