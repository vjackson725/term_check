
module TerminationChecking.Lang where

(|>) x f = f x
infixl 1 |>

data Term v =
  TVar v |
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
