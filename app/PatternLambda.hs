
module PatternLambda where

import Data.List (find)
import Data.Map (Map) 
import qualified Data.Map as Map

(|>) x f = f x
infixl 1 |>

data Term v =
  TVar v |
  TUndefined |
  TUnit |
  TBool Bool |
  TNatLit Int |
  TPair (Term v) (Term v) |
  TIf (Term v) (Term v) (Term v) |
  TLambda v (Term v) |
  TApp (Term v) (Term v)
  deriving (Eq, Show)

tlet :: v -> (Term v) -> (Term v) -> (Term v)
tlet x s t = TApp (TLambda x t) s

data Pattern v =
  PVar v |
  PUnit |
  PNatLit Int |
  PBool Bool |
  PPair (Pattern v) (Pattern v)
  deriving (Eq, Show)

{-
  Functions are a name paried with a pattern/body list.
  Patterns will be evaluated in order.
-}
type FunDef v = [(Pattern v, Term v)]

data Value v =
  VFunDef (FunDef v) |
  VUnit |
  VUndefined |
  VNat Int |
  VBool Bool |
  VPair (Value v) (Value v) |
  VContinuation (State v) v (Term v)
  deriving (Eq, Show)

type State v = Map v (Value v)

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

-- big step; will loop on a non-terminating recursive definition
eval :: (Eq v, Ord v) => State v -> Term v -> Value v
eval st (TVar x) = Map.lookup x st |> maybe VUndefined id
eval st TUndefined = VUndefined
eval st TUnit = VUnit
eval st (TPair t0 t1) = VPair (eval st t0) (eval st t1)
eval st (TNatLit n) = VNat n
eval st (TIf tb tt tf) =
  case eval st tb of
    VBool True  -> eval st tt
    VBool False -> eval st tf
    _ -> VUndefined
eval st (TLambda x t) = VContinuation st x t
eval st (TApp (TLambda x t0) t1) =
  eval st (subst_term [(x, t1)] t0)
eval st (TApp (TVar xfn) t) =
  case Map.lookup xfn st of
    Just (VFunDef fdefn) ->
      case fun_apply fdefn t of
        Just t' -> eval st t'
        Nothing -> VUndefined
    Nothing -> VUndefined
eval st (TApp _ _) = VUndefined