
module PatternLambda where

import Data.List (find)

(|>) x f = f x
infixl 1 |>

data Term v =
  TVar v |
  TUndefined |
  TUnit |
  TPair (Term v) (Term v) |
  TNatLit Int |
  TIf (Term v) (Term v) (Term v) |
  TLambda v (Term v) |
  TApp (Term v) (Term v)
  deriving (Eq, Show)

tlet :: v -> (Term v) -> (Term v) -> (Term v)
tlet x s t = TApp (TLambda x t) s

data Pattern v =
  PVar v | PUnit | PPair (Pattern v) (Pattern v) | PNatLit Int
  deriving (Eq, Show)

type FunDef v = [(Pattern v, Term v)]

type Binding v = [(v, Term v)]


subst_term :: Eq v => Binding v -> Term v -> Term v
subst_term b (TVar x) = b |> find ((==) x . fst)
                          |> maybe (TVar x) snd
subst_term b TUndefined = TUndefined
subst_term b TUnit = TUnit
subst_term b (TPair s t) = TPair (subst_term b s) (subst_term b t)
subst_term b (TNatLit n) = TNatLit n
subst_term b (TIf sb stt sff) = TIf (subst_term b sb) (subst_term b stt) (subst_term b sff)
subst_term b (TLambda x s) = TLambda x (subst_term (b |> filter ((/=) x . fst)) s)
subst_term b (TApp s0 s1) = TApp (subst_term b s0) (subst_term b s1)

pattern_match :: Pattern v -> Term v -> Maybe (Binding v)
pattern_match (PVar x) t = Just [(x,t)]
pattern_match PUnit TUnit = Just []
pattern_match (PPair p0 p1) (TPair s0 s1) =
  do
    b0 <- pattern_match p0 s0
    b1 <- pattern_match p1 s1
    return (b0 ++ b1)
pattern_match (PNatLit n) (TNatLit m) | n == m = Just []
pattern_match _ _ = Nothing

fun_apply :: Eq v => FunDef v -> Term v -> Maybe (Term v)
fun_apply ((p,s_body):fs) s_arg =
  case pattern_match p s_arg of
    Just bnd -> Just $ subst_term bnd s_body
    Nothing  -> fun_apply fs s_body
fun_apply [] t = Nothing
