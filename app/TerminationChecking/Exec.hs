{-# LANGUAGE TupleSections #-}

module TerminationChecking.Exec where

import Data.Bifunctor (bimap, first)
import Data.Maybe (mapMaybe, maybeToList, fromMaybe)
import Data.List (nub, permutations)
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
  VSumR (Value v) |
  VRoll (Value v)
  deriving (Eq, Show)


pattern_to_term :: Pattern v -> Term v
pattern_to_term (PVar x) = TVar x
pattern_to_term PUnit = TUnit
pattern_to_term (PPair p0 p1) =
  TPair (pattern_to_term p0) (pattern_to_term p1)
pattern_to_term (PNatLit n) = TNatLit n
pattern_to_term (PBoolLit b) = TBoolLit b
pattern_to_term (PSumL p) = TSumL $ pattern_to_term p
pattern_to_term (PSumR p) = TSumR $ pattern_to_term p
pattern_to_term (PRoll p) = TRoll $ pattern_to_term p

term_to_callterms :: Term v -> [(v, Term v)]
term_to_callterms = snd . term_to_callterms_aux
  where
    term_to_callterms_aux :: Term v -> (Term v, [(v, Term v)])
    term_to_callterms_aux a@(TVar x)   = (a, [])
    term_to_callterms_aux a@TUnit      = (a, [])
    term_to_callterms_aux a@TNatLit{}  = (a, [])
    term_to_callterms_aux a@TBoolLit{} = (a, [])
    term_to_callterms_aux (TPair t0 t1) =
      let (a0, a0s) = term_to_callterms_aux t0
          (a1, a1s) = term_to_callterms_aux t1
      in (TPair a0 a1, a0s ++ a1s)
    term_to_callterms_aux (TSumL t) = first TSumL $ term_to_callterms_aux t
    term_to_callterms_aux (TSumR t) = first TSumR $ term_to_callterms_aux t
    term_to_callterms_aux (TRoll t) = first TRoll $ term_to_callterms_aux t
    term_to_callterms_aux (TApp (TVar f) t) =
      (TUnit, uncurry (:) $ first (f,) $ term_to_callterms_aux t)
    term_to_callterms_aux (TApp t0 t1) =
      let (_, as) = term_to_callterms_aux t0
          (_, bs) = term_to_callterms_aux t1
      in (TUnit, as ++ bs)
    -- TODO: in the TApp cases, the value is not actually TUnit, though it might
    --       be fine.

data MeasureStep =
  MNat |
  MPairL |
  MPairR |
  MSumL |
  MSumR |
  MRoll |
  MLLtR |
  MRLtL
  deriving (Show, Eq)

type Measure = [MeasureStep]

measure_recursive :: Eq v => v -> Term v -> [Measure]
measure_recursive x t = measure_recursive_aux [] x t
  where
    measure_recursive_aux :: Eq v => [MeasureStep] -> v -> Term v -> [Measure]
    measure_recursive_aux m x (TVar y) = (if x == y then [reverse m] else [])
    measure_recursive_aux m x TUnit = []
    measure_recursive_aux m x (TBoolLit b0) = []
    measure_recursive_aux m x (TNatLit n0) = []
    measure_recursive_aux m x (TPair a b) =
      measure_recursive_aux (MPairL:m) x a ++ measure_recursive_aux (MPairR:m) x b
    measure_recursive_aux m x (TSumL a) = measure_recursive_aux (MSumL:m) x a
    measure_recursive_aux m x (TSumR a) = measure_recursive_aux (MSumR:m) x a
    measure_recursive_aux m x (TRoll a) = measure_recursive_aux (MRoll:m) x a

make_measures :: Eq v => Term v -> Term v -> [(Measure, Measure)]
make_measures = make_measures_aux []
  where
    make_measures_aux :: Eq v => [MeasureStep] -> Term v -> Term v -> [(Measure, Measure)]
    make_measures_aux m t (TVar x) = map (reverse m,) $ measure_recursive x t
    make_measures_aux m (TVar x) t = map (reverse m,) $ measure_recursive x t
    make_measures_aux _ TUnit TUnit = []
    make_measures_aux _ (TBoolLit b0) (TBoolLit b1) = []
    make_measures_aux _ (TNatLit n0) (TNatLit n1) = []
    make_measures_aux m (TPair a0 a1) (TPair b0 b1) =
      make_measures_aux (MPairL:m) a0 b0 ++ make_measures_aux (MPairR:m) a1 b1
    make_measures_aux m (TSumL a) (TSumL b) = make_measures_aux (MSumL:m) a b
    make_measures_aux m (TSumR a) (TSumR b) = make_measures_aux (MSumR:m) a b
    make_measures_aux m (TRoll a) (TRoll b) = make_measures_aux (MRoll:m) a b
    -- different sum conflict
    make_measures_aux m (TSumL a) (TSumR b) = [(reverse (MRLtL:m), [])]
    make_measures_aux m (TSumR a) (TSumL b) = [(reverse (MLLtR:m), [])]
    -- conflict case
    make_measures_aux m _ _ = []


data PathToken = La | Ra | Ld | Rd deriving (Eq, Show, Ord)

type Path = [PathToken]

data SizeChange v = Var v | NatLit Integer | BoolLit Bool | Unit () deriving (Show, Eq, Ord)

pattern_var_depths :: Eq v => Int -> Path -> Path -> Bool -> Pattern v -> [(SizeChange v, Double, Path, Path)]
pattern_var_depths n s a b (PVar x) = [(Var x, (fromIntegral n) :: Double, reverse s, reverse a)]
pattern_var_depths n s a b PUnit = [(Unit (), (fromIntegral n), reverse s, reverse a)]
pattern_var_depths n s a b (PPair p0 p1) =
  if b
    then pattern_var_depths n s (La:a) b p0 ++ pattern_var_depths n s (Ra:a) b p1
    else pattern_var_depths n s a b p0 ++ pattern_var_depths n  s a b p1
pattern_var_depths n s a b (PNatLit num) = [(NatLit num, (fromIntegral n), reverse s, reverse a)]
pattern_var_depths n s a b (PBoolLit bool) = [(BoolLit bool, (fromIntegral n), reverse s, reverse a)]
pattern_var_depths n s a b (PSumL p) = if b then pattern_var_depths n (Ld:s) a b p else pattern_var_depths n s a b p
pattern_var_depths n s a b (PSumR p) = if b then pattern_var_depths n (Rd:s) a b p else pattern_var_depths n s a b p
pattern_var_depths n s a b (PRoll p) = pattern_var_depths (n+1) s a False p

term_var_depths :: Eq v => Maybe Int -> Path -> Path -> Bool -> Term v -> [(SizeChange v, Maybe Double, Path, Path)]
term_var_depths n s a b (TVar x) = [(Var x, (fmap fromIntegral n), reverse s, reverse a)]
term_var_depths n s a b TUnit = [(Unit (), (fmap fromIntegral n), reverse s, reverse a)]
term_var_depths n s a b (TPair p0 p1) =
  if b
    then term_var_depths n s (La:a) b p0 ++ term_var_depths n s (Ra:a) b p1
    else term_var_depths n s a b p0 ++ term_var_depths n s a b p1
term_var_depths n s a b (TNatLit num) = [(NatLit num, (fmap fromIntegral n), reverse s, reverse a)]
term_var_depths n s a b (TBoolLit bool) = [(BoolLit bool, (fmap fromIntegral n), reverse s, reverse a)]
term_var_depths n s a b (TSumL p) = if b then term_var_depths n (Ld:s) a b p else term_var_depths n s a b p
term_var_depths n s a b (TSumR p) = if b then term_var_depths n (Rd:s) a b p else term_var_depths n s a b p
term_var_depths n s a b (TRoll p) = term_var_depths ((+) <$> n <*> (Just 1)) s a False p
term_var_depths n s a b (TApp p r) = term_var_depths n s a False p ++ term_var_depths Nothing s a False r
-- TODO: add if-then-else?

term_find_rec :: Eq v => v -> Term v -> [Term v]
term_find_rec rn (TPair s0 s1) = term_find_rec rn s0 ++ term_find_rec rn s1
term_find_rec rn (TSumL s) = term_find_rec rn s
term_find_rec rn (TSumR s) = term_find_rec rn s
term_find_rec rn (TRoll s) = term_find_rec rn s
term_find_rec rn (TIf sb st sf) =
  term_find_rec rn sb ++ term_find_rec rn st ++ term_find_rec rn sf
term_find_rec rn (TApp (TVar x) s1) | rn == x = s1 : term_find_rec rn s1
term_find_rec rn (TApp s0 s1) = term_find_rec rn s0 ++ term_find_rec rn s1
term_find_rec _ _ = []

fun_apply :: Eq v => FunDef v -> Term v -> Maybe (Term v)
fun_apply ((p,s_body):fs) s_arg =
  case pattern_match p s_arg of
    Just bnd -> Just $ subst_term bnd s_body
    Nothing  -> fun_apply fs s_arg
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
eval st (TApp (TVar xfn) t) =
  case Map.lookup xfn st of
    Just (VFunDef fdefn) ->
      case fun_apply fdefn t of
        Just t' -> eval st t'
        Nothing -> VUndefined
    Nothing -> VUndefined
eval st (TRoll e) = VRoll (eval st e)
eval st (TSumL e) = VSumL (eval st e)
eval st (TSumR e) = VSumR (eval st e)
eval st (TApp _ _) = VUndefined

--matrixify :: Eq v => v -> FunDef v -> [([(v,Int,Path)], [Term v])]
data Val = Na | Leq | Le deriving Eq

instance Show Val where
    show Na  = "?"
    show Leq = "<="
    show Le  = "<"
-- Final Path is the argument in all disjuncts,
-- P takes disjunct path from, disjunct path to and argument
--data PreMatrixEntry = S Val Path | N Double Path | P Double Path Path Path deriving (Eq, Show)

data PreMatrixEntry = P (Either Double Val) Path Path Path deriving (Eq, Show)
data Entry = Num Double | Sym Val deriving (Eq, Show)

matrixify :: (Ord v, Show v) => v -> FunDef v -> [[Entry]]
matrixify name fun =
  traceShow measures $ matrixified
    where
      fundef = fun

      measures =
        fundef
        |> concatMap
          (\(p,t) ->
            let argterm = pattern_to_term p 
                callterms = mapMaybe
                              (\(fn, t) -> if fn == name then Just t else Nothing)
                              (term_to_callterms t)
            in concatMap (make_measures argterm) callterms)
        |> nub

      {-
      Takes in a function definition and turns it into a list of pairs of depths of variables in
      the pattern and depths of variables in the term in each recursive call
      -}
      {-m = map
          (\(p, s) ->
            ( pattern_var_depths 0 p [] [] True
            , join (map (\x -> term_var_depths 0 x [] [] True) (term_find_rec name s))
            )
          ) fun
      -}
      m = do
            (p, s) <- fun
            let a = map (\(a, b, c, d) -> (a, Just b, c, d)) (pattern_var_depths 0 [] [] True p)
            map ((a,) . term_var_depths (Just 0) [] [] True) (term_find_rec name s)

      -- [] in the term_depth corresponds to having a constant in there
      -- so we filter out by it so as to not consider things like f(x) = f(3) etc.
      -- Currently not working quite as intended as function calls are assigned [] depth
      -- as a placeholder, meaning we assume all auxilliary functions terminate (the intention
      -- was to make the opposite assumption for now)
      filtM = filter (not.null.snd) m

      {-
      m' is a further filtration of filtM which removes non-max depth variables and collectes
      max-depth variables into a single set such that there is only one max-depth variable for
      each argument.

      For example, if we consider a type data BTree = Leaf | BNode Integer BTree BTree
      we might have f (BNode n t1 t2, BNode n' t1' t2') = f (t1, t2) + f(BNode n' t1 t1', t2'). Here,
      we would want to convert this to:
      [({n, t1, t2}, t1), ({n', t1', t2'}, t2), ({n, t1, t2}, {n', t1, t1'}), ({n', t1', t2'}, t2')]

      -}
      m' = map (bimap list_convert list_convert) filtM

      {-
      This turns our pairs of depths and arguments etc. into something resembling our final matrix; a matrix of
      pre-matrix entries. These are just like regular matrix entries, but they keep track explicitly of which
      argument and disjunct each entry is coming from. This is because our matrix will not be sorted yet. This is
      more or less just a way of rephrasing the information stored in the pairs, but we've now explicitly calculated
      which entry will go in that arg-disj spot.

      -}
      mat = map recCall m' --is our temp matrix, then we do some processing on this
      --etc for other kinds of args

      {-
      We now add in columns to our matrix to take account of different disjuncts.
      -}
      disjs = filter (\x -> x /= []) (Set.toList $ snd (argsAndDisjs mat))
      matWithDisjArgs = map (makeDisjArgsAllDisjs disjs) mat

      -- This just givs a set of all the different aguments and disjuncts in our function
      ads = argsAndDisjs matWithDisjArgs
      arguments = Set.toList $ fst ads

      {-
      Now that all of the disjuncts are codefied with arguments, we just have to sort all of
          the entries by their argument by placing them in a unique column associated with their
          argument (of course, the row is already taken care of)
      -}
      matrixified = map (flip sortByArg matWithDisjArgs) arguments



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
gain_check xs ys = [P (Right Na) from [] arg | (v, n, from, arg) <- ys, (filter (\(_, _, _, a) -> a == arg) xs) == []]

-- Takes in a lhs, finds its corresponding argument on the rhs and compares the depths, producing a prematrix entry
--depth_compare :: Ord v => ((Set v,Double,Path, Path), [(Set v,Double,Path, Path)]) -> PreMatrixEntry
-- (v' `Set.isSubsetOf` v)

-- | (argFrom == argTo) && (Set.size (v' `Set.intersection` v) /= 0) && (n > n') = N (n' - n) argFrom
depth_compare ((_, _, from, a), []) = P (Left 0) from [] a
depth_compare ((v, (Just n), from, argFrom), ((v', (Just n'), to, argTo):xs)) | (argFrom == argTo) && (Set.size (v' `Set.intersection` v) /= 0)             = P (Left (n' - n)) from to argFrom--if same_path from to then N 0 argFrom else P from to argFrom
                                                                              | otherwise              = depth_compare ((v, (Just n), from, argFrom), xs)
depth_compare ((v, n, from, argFrom), ((v', Nothing, to, argTo):xs)) = P (Right Na) from to argFrom
depth_compare ((v, Nothing, from, argFrom), ((v', n, to, argTo):xs)) = P (Right Na) from to argFrom

pair_map :: (a -> b -> c) -> ([a] -> [b] -> [c])
pair_map f [] ys = []
pair_map f (x:xs) ys = (map (f x) ys) ++ (pair_map f xs ys)

--matrix_temp = map (\(ps, qs) -> map (\p -> depth_compare p qs) ps ++ (gain_check ps qs)) m'


--Gets the argument of a particular preMatrixEntry by just extracting the argument component
argOf (P n f t p) = p
--argOf (S v p)     = p
--argOf (N n p)     = p

toEntry (P (Left n) f t p) = Num n
toEntry (P (Right v) f t p) = Sym v
--toEntry (S v p)     = Sym v
--toEntry (N n p)     = Num n

-- Extracts all of the pre-matrix entries in a particular argument for all the recursive calls.
sortByArg a [] = []
sortByArg a (x:xs) =
  let l = [y | y <- x, argOf y == a]
  in if l == [] then (Num 0):(sortByArg a xs) else (map toEntry l) ++ sortByArg a xs


makeDisjArgsAllDisjs ds call = call ++ (map (makeDisjArgs call) ds)

makeDisjArgs call d = makeDisjArgs' 0 d call


{-
Idea is if the argument is decreasing we don't need to care about the disjunct, so we only put non-trivial
entries in the disjunct columns if there's an entry which increases
-}
makeDisjArgs' ret d [] = P (Left ret) [] [] d
makeDisjArgs' ret d ((P n f t p):rs) | f == t = makeDisjArgs' ret d rs
                                     | f == d = makeDisjArgs' (ret - 1) d rs
                                     | t == d = makeDisjArgs' (ret + 1) d rs
                                     | otherwise = makeDisjArgs' ret d rs
--makeDisjArgs' ret d (r:rs) = makeDisjArgs' ret d rs



--Gets a set of all the arguments and disjuncts that appear in a recursive call
getArgsAndDisjs args disjs [] = (args, disjs)
getArgsAndDisjs args disjs ((P n t f p):xs) = let args'  = (Set.insert p args)
                                                  disjs' = Set.insert t (Set.insert f disjs)
                                              in getArgsAndDisjs args' disjs' xs
--getArgsAndDisjs args disjs ((S v p):xs) = getArgsAndDisjs (Set.insert p args) disjs xs
--getArgsAndDisjs args disjs ((N n p):xs) = getArgsAndDisjs (Set.insert p args) disjs xs

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

Nothing >>> a = True
a >>> Nothing = False
a >>> b = a > b

-- Gets max depth variables and puts them all in a set so we only have 1 entry per arg
process_depths ret [] = ret
process_depths (vs, n, disj, arg) ((v', n', disj', arg'):xs)    | (arg == arg') && (n' >>> n)  = process_depths ((Set.singleton v'), n', disj', arg') xs
                                                                | (arg == arg') && (n' == n)   = process_depths ((Set.insert v' vs), n, disj, arg) xs
                                                                | otherwise                    = process_depths (vs, n, disj, arg) xs

mat' name fun =
  do
    (p,s) <- fun
    let a = map (\(a, b, c, d) -> (a, Just b, c, d)) (pattern_var_depths 0 [] [] True p)
    map ((a,) . (term_var_depths (Just 0) [] [] True)) (term_find_rec name s)

