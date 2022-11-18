{-# LANGUAGE TupleSections #-}

module TerminationChecking.Exec
  (
    Entry(..),
    Val(..),
    matrixify,
  )
where

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

--
-- Execution Semantics
--

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

--
-- Term decrease matrix construction algorithm
--

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
  MBool |
  MPairL |
  MPairR |
  MSumL |
  MSumR |
  MRoll |
  MLLtR |
  MRLtL
  deriving (Show, Eq)

type Measure = ([MeasureStep], [MeasureStep])

measure_recursive :: Eq v => v -> Term v -> [[MeasureStep]]
measure_recursive x t = measure_recursive_aux [] x t
  where
    measure_recursive_aux :: Eq v => [MeasureStep] -> v -> Term v -> [[MeasureStep]]
    measure_recursive_aux m x (TVar y) = (if x == y then [reverse m] else [])
    measure_recursive_aux m x TUnit = []
    measure_recursive_aux m x (TBoolLit b0) = []
    measure_recursive_aux m x (TNatLit n0) = []
    measure_recursive_aux m x (TPair a b) =
      measure_recursive_aux (MPairL:m) x a ++ measure_recursive_aux (MPairR:m) x b
    measure_recursive_aux m x (TSumL a) = measure_recursive_aux (MSumL:m) x a
    measure_recursive_aux m x (TSumR a) = measure_recursive_aux (MSumR:m) x a
    measure_recursive_aux m x (TRoll a) = measure_recursive_aux (MRoll:m) x a

make_measures :: Eq v => Term v -> Term v -> [Measure]
make_measures = make_measures_aux []
  where
    make_measures_aux :: Eq v => [MeasureStep] -> Term v -> Term v -> [Measure]
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

tryfoldl :: (b -> a -> Maybe b) -> b -> [a] -> (b, [a])
tryfoldl f b [] = (b, [])
tryfoldl f b as@(a:as') =
  case f b a of
    Nothing -> (b, as)
    Just b' -> tryfoldl f b' as'

tryfoldl' :: (b -> a -> Maybe b) -> b -> [a] -> (b, [a])
tryfoldl' f b [] = (b, [])
tryfoldl' f b as@(a:as') =
  let mb' = f b a
   in mb' `seq` (case mb' of
                  Nothing -> (b, as)
                  Just b' -> tryfoldl' f b' as')

iterateFixp :: Eq a => (a -> a) -> a -> a
iterateFixp f a =
  let a' = f a
   in a' `seq` (if a == a' then a else iterateFixp f a')

run_measure :: (Show v, Eq v) => Measure -> Term v -> (Int, Measure, Maybe (Term v))
run_measure (base, rpath) tinit =
  let (k, m, mt) = iterateFixp
                    (\(k, m, mt) ->
                      case mt of
                        Nothing -> (k, m, mt)
                        Just t ->
                          let ((j, mt'), m') = run_measure_steps m t
                           in if null m'
                                then (k+j, rpath, mt')
                              else if m == m'
                                then (k, m, mt) -- ASSERT: j == 0 && mt == mt'
                              else (k+j, m', mt'))
                    (0, base, Just tinit)
   in (k, (m, rpath), mt)
  where
    run_measure_steps :: [MeasureStep] -> Term v -> ((Int, Maybe (Term v)), [MeasureStep])
    run_measure_steps msteps t =
      tryfoldl'
        (\(k,mt) mstep ->
          do
            t <- mt
            (j, mt') <- run_measure_step mstep t
            return (k+j, mt'))
        (0, Just t)
        msteps

    run_measure_step :: MeasureStep -> Term v -> Maybe (Int, Maybe (Term v))
    run_measure_step MPairL (TPair a _) = Just (0, Just a)
    run_measure_step MPairR (TPair _ b) = Just (0, Just b)
    run_measure_step MSumL  (TSumL a) = Just (0, Just a)
    run_measure_step MSumR  (TSumR a) = Just (0, Just a)
    run_measure_step MRoll  (TRoll a) = Just (1, Just a)
    run_measure_step MNat   (TNatLit k) = Just (0, Nothing)
    run_measure_step MBool  (TBoolLit k) = Just (0, Nothing)
    run_measure_step MSumR  TSumL{} = Just (0, Nothing)
    run_measure_step MSumL  TSumR{} = Just (0, Nothing)
    run_measure_step MLLtR  TSumL{} = Just (0, Nothing)
    run_measure_step MRLtL  TSumR{} = Just (0, Nothing)
    run_measure_step MLLtR  TSumR{} = Just (1, Nothing)
    run_measure_step MRLtL  TSumL{} = Just (1, Nothing)
    run_measure_step _ _ = Nothing

data Val = Na | Le | Leq
  deriving (Show, Eq)

data Entry = Num Double | Sym Val
  deriving (Show, Eq)

matrixify :: (Show v, Eq v) => v -> FunDef v -> [[Entry]]
matrixify name fundef = matrix
  where
    argpairs =
      fundef
      |> concatMap
        (\(p,t) ->
          let argterm = pattern_to_term p 
              callterms = mapMaybe
                            (\(fn, t) -> if fn == name then Just t else Nothing)
                            (term_to_callterms t)
          in map (argterm,) callterms)
    measures = nub . concatMap (uncurry make_measures) $ argpairs
    reduced =
      map
        (\m ->
          (m, map
            (\(a, b) ->
              let (ka, ma, ta) = run_measure m a
                  (kb, mb, tb) = run_measure m b
              in (if ma == mb && ta == tb
                    then Num (toEnum (kb - ka))
                  else if not (null ma) && null mb
                    then Num (toEnum (kb - ka)) -- kb - (ka + |x|) <= kb - ka
                  else 
                    trace ("orig: " ++ show m ++ " / " ++ show a ++ " =?= " ++ show b) $
                    trace (" new: " ++ show (ma,ta) ++ " =?= " ++ show (mb,tb)) $
                    Sym Na))
          argpairs))
        measures
    matrix = map snd $ (traceShowId reduced)
