
module PatternLambda where

import Data.List (find)
import Data.Map (Map) 
import qualified Data.Map as Map
import Data.Bifunctor (second)

(|>) x f = f x
infixl 1 |>

data Term v =
  TVar v |
  TUnit |
  TBoolLit Bool |
  TNatLit Int |
  TPair (Term v) (Term v) |
  TIf (Term v) (Term v) (Term v) |
  TLambda v (Term v) |
  TApp (Term v) (Term v) |
  TSumL (Term v) |
  TSumR (Term v) |
  TBox v (Term v) |
  TUnbox (Term v)
  deriving (Eq, Show)

tlet :: v -> (Term v) -> (Term v) -> (Term v)
tlet x s t = TApp (TLambda x t) s

data Pattern v =
  PVar v |
  PUnit |
  PBoolLit Bool |
  PNatLit Int |
  PPair (Pattern v) (Pattern v) |
  PSumL (Pattern v) |
  PSumR (Pattern v) |
  PBox v (Pattern v)
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
  VContinuation (State v) v (Term v) |
  VSumL (Value v) |
  VSumR (Value v)
  deriving (Eq, Show)

type State v = Map v (Value v)

type Binding v = [(v, Term v)]

subst_term :: Eq v => Binding v -> Term v -> Term v
subst_term b (TVar x) = b |> find ((==) x . fst)
                          |> maybe (TVar x) snd
subst_term b TUnit = TUnit
subst_term b (TPair s t) = TPair (subst_term b s) (subst_term b t)
subst_term b (TNatLit n) = TNatLit n
subst_term b (TBoolLit n) = TBoolLit n
subst_term b (TIf sb stt sff) = TIf (subst_term b sb) (subst_term b stt) (subst_term b sff)
subst_term b (TLambda x s) = TLambda x (subst_term (b |> filter ((/=) x . fst)) s)
subst_term b (TApp s0 s1) = TApp (subst_term b s0) (subst_term b s1)
subst_term b (TSumL s) = TSumL (subst_term b s)
subst_term b (TSumR s) = TSumR (subst_term b s)
subst_term b (TBox r s) = TBox r (subst_term (b |> filter ((/=) r . fst)) s)
subst_term b (TUnbox s) = TUnbox (subst_term b s)

pattern_match :: Eq v => Pattern v -> Term v -> Maybe (Binding v)
pattern_match (PVar x) t = Just [(x,t)]
pattern_match PUnit TUnit = Just []
pattern_match (PPair p0 p1) (TPair s0 s1) =
  do
    b0 <- pattern_match p0 s0
    b1 <- pattern_match p1 s1
    return (b0 ++ b1)
pattern_match (PNatLit n) (TNatLit m) | n == m = Just []
pattern_match (PBoolLit n) (TBoolLit m) | n == m = Just []
pattern_match (PSumL p) (TSumL s) = pattern_match p s
pattern_match (PSumR p) (TSumR s) = pattern_match p s
pattern_match (PBox rp p) (TBox rt s) | rp == rt =
  do
    b <- pattern_match p s
    if any (\(x,_) -> rp == x) b
    then Nothing
    else return b
pattern_match _ _ = Nothing


pattern_var_depths :: Eq v => Int -> Pattern v -> [(v,Int)]
pattern_var_depths n (PVar x) = [(x,n)]
pattern_var_depths n PUnit = []
pattern_var_depths n (PPair p0 p1) = pattern_var_depths n p0 ++ pattern_var_depths n p1
pattern_var_depths n PNatLit{} = []
pattern_var_depths n PBoolLit{} = []
pattern_var_depths n (PSumL p) = pattern_var_depths n p
pattern_var_depths n (PSumR p) = pattern_var_depths n p
pattern_var_depths n (PBox r p) =
  filter ((/=) r . fst) $
    pattern_var_depths (n+1) p

app_primary_term :: Term v -> Term v
app_primary_term (TApp s _) = app_primary_term s
app_primary_term s = s

term_find_rec :: Eq v => v -> Term v -> [Term v]
term_find_rec rn (TPair s0 s1) = term_find_rec rn s0 ++ term_find_rec rn s1
term_find_rec rn (TSumL s) = term_find_rec rn s
term_find_rec rn (TSumR s) = term_find_rec rn s
term_find_rec rn (TBox r s) | r /= rn = term_find_rec rn s
term_find_rec rn (TIf sb st sf) =
  term_find_rec rn sb ++ term_find_rec rn st ++ term_find_rec rn sf
term_find_rec rn (TLambda x s) | x /= rn = term_find_rec rn s
term_find_rec rn (TApp (TVar x) s1) | rn == x = [s1]
term_find_rec rn (TApp s0 s1) = term_find_rec rn s0 ++ term_find_rec rn s1
term_find_rec rn (TUnbox s) = term_find_rec rn s
term_find_rec _ _ = []

fun_apply :: Eq v => FunDef v -> Term v -> Maybe (Term v)
fun_apply ((p,s_body):fs) s_arg =
  case pattern_match p s_arg of
    Just bnd -> Just $ subst_term bnd s_body
    Nothing  -> fun_apply fs s_body
fun_apply [] t = Nothing

-- big step; will loop on a non-terminating recursive definition
eval :: (Eq v, Ord v) => State v -> Term v -> Value v
eval st (TVar x) = Map.lookup x st |> maybe VUndefined id
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

matrixify :: Eq v => v -> FunDef v -> [([(v,Int)], [Term v])]
matrixify name =
  map
    (\(p, s) ->
      ( pattern_var_depths 0 p
      , term_find_rec name s
      )
    )