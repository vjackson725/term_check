
module PatternLambda where

import Data.List (find, permutations)
import Control.Monad (join)
import Data.Set (Set)
import qualified Data.Set as Set
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
  TBox (Term v) |
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
  PBox (Pattern v)
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


data PathToken = L | R deriving (Eq, Show, Ord)

type Path = [PathToken]

fst' (a, b, c) = a
--pattern_var_depths :: Eq v => Int -> Pattern v -> Path -> [(v,Int,Path)]
pattern_var_depths n (PVar x) s a b = [(x,(fromIntegral n) :: Double, reverse s, reverse a)]
pattern_var_depths n PUnit s a b = []
pattern_var_depths n (PPair p0 p1) s a b = if b then pattern_var_depths n p0 s (L:a) b ++ pattern_var_depths n p1 s (R:a) b else pattern_var_depths n p0 s a b ++ pattern_var_depths n p1 s a b
pattern_var_depths n PNatLit{} s a b = []
pattern_var_depths n PBoolLit{} s a b = []
pattern_var_depths n (PSumL p) s a b = pattern_var_depths n p (L:s) a b 
pattern_var_depths n (PSumR p) s = pattern_var_depths n p (R:s) a b 
pattern_var_depths n (PBox p) s = pattern_var_depths (n+1) p s a False

--term_var_depths :: Eq v => Int -> Term v -> Path -> [(v,Int,Path)]
term_var_depths n (TVar x) s a b = [(x,(fromIntegral n) :: Double, reverse s, reverse a)]
term_var_depths n TUnit s a b = []
term_var_depths n (TPair p0 p1) s a b = term_var_depths n p0 s (L:a) b ++ term_var_depths n p1 s (R:a) b
term_var_depths n TNatLit{} s a b = []
term_var_depths n TBoolLit{} s a b = []
term_var_depths n (TSumL p) s a b = term_var_depths n p (L:s) a b 
term_var_depths n (TSumR p) s a b = term_var_depths n p (R:s) a b 
term_var_depths n (TBox p) s a b = term_var_depths (n+1) p s a False
term_var_depths n (TUnbox p) s a b = term_var_depths (n-1) p s b
term_var_depths n (TApp p r) s = []


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
data Val = Na | Leq | Le deriving (Eq, Show)
data PreMatrixEntry = S Val Path | N Double Path | P Path Path Path deriving (Eq, Show)
data Entry = Num Double | Sym Val deriving (Eq, Show)
matrixify name fun = pair_map make_matrix paths_taken matrix_temp
    where

        toSym x a b    | x == a    = Sym Le
                       | otherwise = Sym Na
        
        --make_matrix :: Path -> [Maybe PreMatrixEntry] -> [Entry]
        make_matrix x ((P a b):ys) = (toSym x a b):(make_matrix x ys)
        make_matrix x ((N a):ys)   = (Num a):(make_matrix x ys)
        --make_matrix x (Nothing:ys)        = make_matrix x ys

        paths_taken = mkUniq $ join $ map (extract_ambig []) matrix_temp
        

        extract_ambig ret []                  = ret
        extract_ambig ret ((Just (P a b)):xs) = extract_ambig (a:b:ret) xs
        extract_ambig ret (x:xs)              = extract_ambig ret xs
        
        same_path [] _ = True
        same_path _ [] = True
        same_path (p:ps) (q:qs) | p == q    = same_path ps qs
                                | otherwise = False
        
        mkUniq :: Ord a => [a] -> [a]
        mkUniq = Set.toList . Set.fromList

        --depth_compare :: Eq v => ((v,Int,Path), (v,Int,Path)) -> Maybe PreMatrixEntry

        gain_check xs ys = [S Na arg | (v, n, from, arg) <- ys, (filter (\(_, _, _, a) -> a == arg) xs) == []]
        depth_compare ((_, _, _, a), []) = N 0 a
        depth_compare ((v, n, from, argFrom), ((v', n', to, argTo):xs)) | (argFrom == argTo) && (v' Set.isSubsetOf v) && (n /= n') = N (n' - n) argFrom
                                                                        | (argFrom == argTo) && (v' Set.isSubsetOf v)              = if same_path from to then N 0 argFrom else P from to argFrom
                                                                        | otherwise              = depth_compare (v', n', to, argFrom) xs
        pair_map :: (a -> b -> c) -> ([a] -> [b] -> [c]) 
        pair_map f [] ys = []
        pair_map f (x:xs) ys = (map (f x) ys) ++ (pair_map f xs ys)
        
        --Gives us a list of rows
        --matrix_temp :: [[Maybe PreMatrixEntry]]
        --([(v,Int,Path)], [(v,Int,Path)]) -> [Maybe PreMatrixEntry]
        --matrix_temp = map (uncurry (pair_map (curry depth_compare))) m'


        matrix_temp = map (\(ps, qs) -> map (\p -> depth_compare p qs) ps ++ (gain_check ps qs)) m'
            where
                argOf (P t f p) = p
                argOf (S v p) = p
                argOF (N n p) = p
                sortByArg a (x:xs) = let (l:ls) = [y | y <- x, argOF y == a]
                                     in if (l:ls) == [] then 
 
                args = map union (map getArgs mat)
                mat = map recCall m' --is our temp matrix, then we do some processing on this
                --etc for other kinds of args
                getArgs ret [] = ret
                getArgs ret ((P t f p):xs) = Set.union (Set.insert p ret) (getArgs xs)
                getArgs ret ((S v p):xs) = Set.union (Set.insert p ret) (getArgs xs)
                getArgs ret ((N n p):xs) = Set.union (Set.insert p ret) (getArgs xs)
                
                recCall (ps, qs) = map (\p -> depth_compare p qs) ps ++ (gain_check ps qs) 


        --go (v, n, p) t | term_var_depths 0 t []

        --m :: Eq v => v -> FunDef v -> [([(v,Int,Path)], [Term v])]

        pair_list :: (a, [b]) -> [(a, b)]
        pair_list (a, [])     = []
        pair_list (a, (b:bs)) = (a, b) : (pair_list (a, bs)) 
        {-all_pairs :: [(a, b)] -> (b -> [c]) -> [(a, c)]
        all_pairs ((a, b):xs) f = pair_list (a, f b) ++ all_pairs xs-}

        -- Want to go through both lists in m, process them into lists of (vars, depth, path, arg) where
        -- we remove non-max depth variables within a particular argument
        
        m' = map (\(xs, ys) -> (list_convert xs, list_convert ys)) m

        list_convert (x:xs) = mkUniq $ (process_depths x xs):(list_convert xs)
        
        process_depths ret [] = ret
        process_depths (vs, n, disj, arg) ((v', n', disj', arg'):xs) | (arg == arg') && (n' > n)  = process_depths (singleton v', n', disj', arg') xs
                                                                     | (arg == arg') && (n' == n) = process_depths (insert v' vs, n, disj, arg) xs
                                                                     | otherwise                  = process_depths (vs, n, disj, arg) xs
        

        m = map
            (\(p, s) ->
              ( pattern_var_depths 0 p [] [] True
              , join (map (\x -> term_var_depths 0 x [] [] True) (term_find_rec name s))
              )
            ) fun 
        
mat' name fun = map
                (\(p, s) ->
                  ( pattern_var_depths 0 p [] [] True
                  , join (map (\x -> term_var_depths 0 x [] [] True) (term_find_rec name s))
                  )
                ) fun 