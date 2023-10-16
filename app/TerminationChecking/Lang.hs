
module TerminationChecking.Lang
  ( (|>)
  , Term(..)
  , Pattern(..)
  , FunDef
  , patternToTerm
  , pattern_dup_vars
  , pattern_match
  , subst_term
  )
where

import qualified Data.Map as M
import Data.List (nub, find)

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
  TApp (Term v) (Term v) |
  TSumL (Term v) |
  TSumR (Term v) |
  TRoll (Term v)
  deriving (Eq, Show)

data Pattern v =
  PVar v |
  PUnit |
  PBoolLit Bool |
  PNatLit Integer |
  PPair (Pattern v) (Pattern v) |
  PSumL (Pattern v) |
  PSumR (Pattern v) |
  PRoll (Pattern v)
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
pattern_count_vars (PRoll p)  m = pattern_count_vars p m

pattern_dup_vars :: (Show v, Ord v) => Pattern v -> [v]
pattern_dup_vars p = pattern_count_vars p M.empty |> M.filter (>0) |> M.keys


type Binding v = [(v, Term v)]

subst_term :: Eq v => Binding v -> Term v -> Term v
subst_term b (TVar x) = b |> find ((==) x . fst)
                          |> maybe (TVar x) snd
subst_term b TUnit = TUnit
subst_term b (TPair s t) = TPair (subst_term b s) (subst_term b t)
subst_term b (TNatLit n) = TNatLit n
subst_term b (TBoolLit n) = TBoolLit n
subst_term b (TIf sb stt sff) = TIf (subst_term b sb) (subst_term b stt) (subst_term b sff)
subst_term b (TApp s0 s1) = TApp (subst_term b s0) (subst_term b s1)
subst_term b (TSumL s) = TSumL (subst_term b s)
subst_term b (TSumR s) = TSumR (subst_term b s)
subst_term b (TRoll s) = TRoll (subst_term b s)

pattern_match :: Eq v => Pattern v -> Term v -> Maybe (Binding v)
pattern_match (PVar x) t = Just [(x,t)]
pattern_match PUnit TUnit = Just []
pattern_match (PPair p0 p1) (TPair s0 s1) =
  do
    b0 <- pattern_match p0 s0
    b1 <- pattern_match p1 s1
    let conflicts = [ x | (x,t0) <- b0, (y,t1) <- b1, x == y, t0 /= t1 ]
    if not.null $ conflicts
      then Nothing
      else return $ nub (b0 ++ b1)
pattern_match (PNatLit n) (TNatLit m) | n == m = Just []
pattern_match (PBoolLit n) (TBoolLit m) | n == m = Just []
pattern_match (PSumL p) (TSumL s) = pattern_match p s
pattern_match (PSumR p) (TSumR s) = pattern_match p s
pattern_match (PRoll p) (TRoll s) = pattern_match p s
pattern_match _ _ = Nothing

{- A function to construct
  let x = s
   in t
  expressions.
-}
tlet :: Eq v => v -> Term v -> Term v -> Term v
tlet x s t = subst_term [(x,s)] t

patternToTerm :: Pattern v -> Term v
patternToTerm (PVar x) = TVar x
patternToTerm PUnit = TUnit
patternToTerm (PPair p0 p1) =
  TPair (patternToTerm p0) (patternToTerm p1)
patternToTerm (PNatLit n) = TNatLit n
patternToTerm (PBoolLit b) = TBoolLit b
patternToTerm (PSumL p) = TSumL $ patternToTerm p
patternToTerm (PSumR p) = TSumR $ patternToTerm p
patternToTerm (PRoll p) = TRoll $ patternToTerm p
