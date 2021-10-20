
module TerminationChecking.Exec where

import Data.List (find, permutations)
import Control.Monad (join)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Bifunctor (second)

import Debug.Trace

import TerminationChecking.Lang


type State v = Map v (Value v)

data Value v =
  VFunDef (FunDef v) |
  VUnit |
  VUndefined |
  VNat Integer |
  VBool Bool |
  VPair (Value v) (Value v) |
  VContinuation (State v) v (Term v) |
  VSumL (Value v) |
  VSumR (Value v)
  deriving (Eq, Show)


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
subst_term b (TBox s) = TBox (subst_term b s)
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
pattern_match (PBox p) (TBox s) = pattern_match p s
  {-do
    b <- pattern_match p s
    if any (\(x,_) -> rp == x) b
    then Nothing
    else return b-}
pattern_match _ _ = Nothing


data PathToken = La | Ra | Ld | Rd deriving (Eq, Show, Ord)

type Path = [PathToken]

fst' (a, b, c) = a
--pattern_var_depths :: Eq v => Int -> Pattern v -> Path -> [(v,Int,Path)]
pattern_var_depths n (PVar x) s a b = [(x,(fromIntegral n) :: Double, reverse s, reverse a)]
pattern_var_depths n PUnit s a b = []
pattern_var_depths n (PPair p0 p1) s a b = if b then pattern_var_depths n p0 s (La:a) b ++ pattern_var_depths n p1 s (Ra:a) b else pattern_var_depths n p0 s a b ++ pattern_var_depths n p1 s a b
pattern_var_depths n PNatLit{} s a b = []
pattern_var_depths n PBoolLit{} s a b = []
pattern_var_depths n (PSumL p) s a b = pattern_var_depths n p (Ld:s) a b
pattern_var_depths n (PSumR p) s a b = pattern_var_depths n p (Rd:s) a b
pattern_var_depths n (PBox p) s a b = pattern_var_depths (n+1) p s a False

--term_var_depths :: Eq v => Int -> Term v -> Path -> [(v,Int,Path)]
term_var_depths n (TVar x) s a b = [(x,(fromIntegral n) :: Double, reverse s, reverse a)]
term_var_depths n TUnit s a b = []
term_var_depths n (TPair p0 p1) s a b = if b then term_var_depths n p0 s (La:a) b ++ term_var_depths n p1 s (Ra:a) b else term_var_depths n p0 s a b ++ term_var_depths n p1 s a b
term_var_depths n TNatLit{} s a b = []
term_var_depths n TBoolLit{} s a b = []
term_var_depths n (TSumL p) s a b = term_var_depths n p (Ld:s) a b
term_var_depths n (TSumR p) s a b = term_var_depths n p (Rd:s) a b
term_var_depths n (TBox p) s a b = term_var_depths (n+1) p s a False
term_var_depths n (TUnbox p) s a b = term_var_depths (n-1) p s a b
term_var_depths n (TApp p r) s a b = []


app_primary_term :: Term v -> Term v
app_primary_term (TApp s _) = app_primary_term s
app_primary_term s = s

term_find_rec :: Eq v => v -> Term v -> [Term v]
term_find_rec rn (TPair s0 s1) = term_find_rec rn s0 ++ term_find_rec rn s1
term_find_rec rn (TSumL s) = term_find_rec rn s
term_find_rec rn (TSumR s) = term_find_rec rn s
term_find_rec rn (TBox s) = term_find_rec rn s
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

--matrixify :: Eq v => v -> FunDef v -> [([(v,Int,Path)], [Term v])]
data Val = Na | Leq | Le deriving Eq

instance Show Val where
    show Na  = "?"
    show Leq = "<="
    show Le  = "<"
-- Final Path is the argument in all disjuncts,
-- P takes disjunct path from, disjunct path to and argument
data PreMatrixEntry = S Val Path | N Double Path | P Path Path Path deriving (Eq, Show)
data Entry = Num Double | Sym Val deriving (Eq, Show)

matrixify :: Ord v => v -> FunDef v -> [[Entry]]
matrixify name fun = matrixified
    where

        m = map
            (\(p, s) ->
              ( pattern_var_depths 0 p [] [] True
              , join (map (\x -> term_var_depths 0 x [] [] True) (term_find_rec name s))
              )
            ) fun

        filtM = filter (\x -> snd x /= []) m

        m' = map (\(xs, ys) -> (list_convert xs, list_convert ys)) filtM

        mat = map recCall m' --is our temp matrix, then we do some processing on this
        --etc for other kinds of args

        ads = argsAndDisjs matWithDisjArgs
        arguments = Set.toList $ fst ads

        disjs = Set.toList $ snd (argsAndDisjs mat)

        matrixified = map (\a -> sortByArg a matWithDisjArgs) arguments

        matWithDisjArgs = map (makeDisjArgsAllDisjs disjs) mat


argsAndDisjs matr = let r    = map (getArgsAndDisjs Set.empty Set.empty) matr
                        args = map fst r
                        dsjs = map snd r
                    in (foldl Set.union Set.empty args, foldl Set.union Set.empty dsjs)

same_path [] _ = True
same_path _ [] = True
same_path (p:ps) (q:qs) | p == q    = same_path ps qs
                        | otherwise = False

mkUniq :: Eq a => [a] -> [a]
mkUniq = rdHelper []
    where
        rdHelper seen [] = seen
        rdHelper seen (x:xs) | x `elem` seen = rdHelper seen xs
                                | otherwise = rdHelper (seen ++ [x]) xs

-- Checks if any arguments appear on the rhs that aren't on the lhs and puts a ? in that matrix entry
gain_check xs ys = [S Na arg | (v, n, from, arg) <- ys, (filter (\(_, _, _, a) -> a == arg) xs) == []]

-- Takes in a lhs, finds its corresponding argument on the rhs and compares the depths, producing a prematrix entry
--depth_compare :: Ord v => ((Set v,Double,Path, Path), [(Set v,Double,Path, Path)]) -> PreMatrixEntry
depth_compare ((_, _, _, a), []) = N 0 a
depth_compare ((v, n, from, argFrom), ((v', n', to, argTo):xs)) | (argFrom == argTo) && (v' `Set.isSubsetOf` v) && (n /= n') = N (n' - n) argFrom
                                                                | (argFrom == argTo) && (v' `Set.isSubsetOf` v)              = if same_path from to then N 0 argFrom else P from to argFrom
                                                                | otherwise              = depth_compare ((v, n, from, argFrom), xs)
pair_map :: (a -> b -> c) -> ([a] -> [b] -> [c])
pair_map f [] ys = []
pair_map f (x:xs) ys = (map (f x) ys) ++ (pair_map f xs ys)

--matrix_temp = map (\(ps, qs) -> map (\p -> depth_compare p qs) ps ++ (gain_check ps qs)) m'


--Gets the argument of a particular preMatrixEntry by just extracting the argument component
argOf (P f t p) = p
argOf (S v p) = p
argOf (N n p) = p

toEntry (P f t p) = Num 0
toEntry (S v p)   = Sym v
toEntry (N n p)   = Num n

-- Extracts all of the pre-matrix entries in a particular argument for all the recursive calls.
sortByArg a [] = []
sortByArg a (x:xs) = let l = [y | y <- x, argOf y == a]
                     in if l == [] then (Num 0):(sortByArg a xs) else (map toEntry l) ++ sortByArg a xs


makeDisjArgsAllDisjs ds call = call ++ (map (makeDisjArgs call) ds)

makeDisjArgs call d = makeDisjArgs' 0 d call

makeDisjArgs' ret d [] = N ret d
makeDisjArgs' ret d ((P f t p):rs)  | f == t = makeDisjArgs' ret d rs
                                    | f == d = makeDisjArgs' (ret - 1) d rs
                                    | t == d = makeDisjArgs' (ret + 1) d rs
                                    | otherwise = makeDisjArgs' ret d rs
makeDisjArgs' ret d (r:rs) = makeDisjArgs' ret d rs



--Gets a set of all the arguments and disjuncts that appear in a recursive call
getArgsAndDisjs args disjs [] = (args, disjs)
getArgsAndDisjs args disjs ((P t f p):xs) = let args'  = (Set.insert p args)
                                                disjs' = Set.insert t (Set.insert f disjs)
                                            in getArgsAndDisjs args' disjs' xs
getArgsAndDisjs args disjs ((S v p):xs) = getArgsAndDisjs (Set.insert p args) disjs xs
getArgsAndDisjs args disjs ((N n p):xs) = getArgsAndDisjs (Set.insert p args) disjs xs

-- Processes a single recursive call
--recCall :: Eq v => ([(Set v,Double,Path, Path)], [(Set v,Double,Path, Path)]) -> [PreMatrixEntry]
recCall (ps, qs) = (map (\p -> depth_compare (p, qs)) ps) ++ (gain_check ps qs)

pair_list :: (a, [b]) -> [(a, b)]
pair_list (a, [])     = []
pair_list (a, (b:bs)) = (a, b) : (pair_list (a, bs))

-- Want to go through both lists in m, process them into lists of (vars, depth, path, arg) where
-- we remove non-max depth variables within a particular argument


setify (v, n, disj, arg) = ((Set.singleton v), n, disj, arg)
list_convert xs = mkUniq $ map (\y -> process_depths (setify y) xs) xs --mkUniq $ (process_depths (setify x) xs):(list_convert xs)

-- Gets max depth variables and puts them all in a set so we only have 1 entry per arg
process_depths ret [] = ret
process_depths (vs, n, disj, arg) ((v', n', disj', arg'):xs)    | (arg == arg') && (n' > n)  = process_depths ((Set.singleton v'), n', disj', arg') xs
                                                                | (arg == arg') && (n' == n) = process_depths ((Set.insert v' vs), n, disj, arg) xs
                                                                | otherwise                  = process_depths (vs, n, disj, arg) xs


mat' name fun = map
                (\(p, s) ->
                  ( pattern_var_depths 0 p [] [] True
                  , join (map (\x -> term_var_depths 0 x [] [] True) (term_find_rec name s))
                  )
                ) fun
