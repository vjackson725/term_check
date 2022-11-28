{-# LANGUAGE TupleSections #-}

module TerminationChecking.Exec
  (
    Entry(..),
    Val(..),
    matrixify,
  )
where

import Data.Bifunctor (bimap, first, second)
import Data.Maybe (mapMaybe, maybeToList, fromMaybe)
import Data.List (nub, permutations)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

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

funApply :: Eq v => FunDef v -> Term v -> Maybe (Term v)
funApply ((p,s_body):fs) s_arg =
  case pattern_match p s_arg of
    Just bnd -> Just $ subst_term bnd s_body
    Nothing  -> funApply fs s_arg
funApply [] t = Nothing

-- big step; will loop on a non-terminating recursive definition
eval :: (Eq v, Ord v) => State v -> Term v -> Value v
eval st (TVar x) = Map.lookup x st |> fromMaybe VUndefined
eval st TUnit = VUnit
eval st (TPair t0 t1) = VPair (eval st t0) (eval st t1)
eval st (TNatLit n) = VNat n
eval st (TBoolLit b) = VBool b
eval st (TIf tb tt tf) =
  case eval st tb of
    VBool True  -> eval st tt
    VBool False -> eval st tf
    _ -> VUndefined
eval st (TApp (TVar xfn) t) =
  case Map.lookup xfn st of
    Just (VFunDef fdefn) ->
      case funApply fdefn t of
        Just t' -> eval st t'
        Nothing -> VUndefined
    Just _ -> error "state lookup must be a VFunDef"
    Nothing -> VUndefined
eval st (TApp _ _) = VUndefined
eval st (TRoll e) = VRoll (eval st e)
eval st (TSumL e) = VSumL (eval st e)
eval st (TSumR e) = VSumR (eval st e)
eval st (TOp _) = error "undefined"

--
-- Term decrease matrix construction algorithm
--

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

termToCallterms :: Term v -> [(v, Term v)]
termToCallterms = snd . termToCalltermsAux
  where
    termToCalltermsAux :: Term v -> (Term v, [(v, Term v)])
    termToCalltermsAux a@(TVar x)   = (a, [])
    termToCalltermsAux a@TUnit      = (a, [])
    termToCalltermsAux a@TNatLit{}  = (a, [])
    termToCalltermsAux a@TBoolLit{} = (a, [])
    termToCalltermsAux (TPair t0 t1) =
      let (a0, a0s) = termToCalltermsAux t0
          (a1, a1s) = termToCalltermsAux t1
      in (TPair a0 a1, a0s ++ a1s)
    termToCalltermsAux (TSumL t) = first TSumL $ termToCalltermsAux t
    termToCalltermsAux (TSumR t) = first TSumR $ termToCalltermsAux t
    termToCalltermsAux (TRoll t) = first TRoll $ termToCalltermsAux t
    termToCalltermsAux (TApp (TVar f) t) =
      (TUnit, uncurry (:) $ first (f,) $ termToCalltermsAux t)
    termToCalltermsAux (TApp t0 t1) =
      let (_, as) = termToCalltermsAux t0
          (_, bs) = termToCalltermsAux t1
      in (TUnit, as ++ bs)
    -- TODO: in the TApp cases, the value is not actually TUnit, though it might
    --       be fine.
    termToCalltermsAux (TOp v) = error "undefined"
    termToCalltermsAux (TIf tc tt tf) = error "undefined"

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

measureRecursive :: Eq v => v -> Term v -> [[MeasureStep]]
measureRecursive x t = measureRecursiveAux [] x t
  where
    measureRecursiveAux :: Eq v => [MeasureStep] -> v -> Term v -> [[MeasureStep]]
    measureRecursiveAux m x (TVar y) = [reverse m | x == y]
    measureRecursiveAux m x TUnit = []
    measureRecursiveAux m x (TBoolLit b0) = []
    measureRecursiveAux m x (TNatLit n0) = []
    measureRecursiveAux m x (TPair a b) =
      measureRecursiveAux (MPairL:m) x a ++ measureRecursiveAux (MPairR:m) x b
    measureRecursiveAux m x (TSumL a) = measureRecursiveAux (MSumL:m) x a
    measureRecursiveAux m x (TSumR a) = measureRecursiveAux (MSumR:m) x a
    measureRecursiveAux m x (TRoll a) = measureRecursiveAux (MRoll:m) x a
    measureRecursiveAux m x (TOp v) = error "undefined"
    measureRecursiveAux m x (TIf tc tt tf) = error "undefined"
    measureRecursiveAux m x (TApp a b) = error "undefined"

makeMeasures :: Eq v => Pattern v -> Term v -> [Measure]
makeMeasures = makeMeasuresAux []
  where
    makeMeasuresAux :: Eq v => [MeasureStep] -> Pattern v -> Term v -> [Measure]
    makeMeasuresAux m p (TVar x) = map (reverse m,) $ measureRecursive x (patternToTerm p)
    makeMeasuresAux m (PVar x) t = map (reverse m,) $ measureRecursive x t
    makeMeasuresAux _ PUnit TUnit = []
    makeMeasuresAux _ (PBoolLit b0) (TBoolLit b1) = []
    makeMeasuresAux _ (PNatLit n0) (TNatLit n1) = []
    makeMeasuresAux m (PPair a0 a1) (TPair b0 b1) =
      makeMeasuresAux (MPairL:m) a0 b0 ++ makeMeasuresAux (MPairR:m) a1 b1
    makeMeasuresAux m (PRoll a) (TRoll b) = makeMeasuresAux (MRoll:m) a b
    -- different sum conflict
    makeMeasuresAux m (PSumL a) (TSumR b) = [(reverse (MRLtL:m), [])]
    makeMeasuresAux m (PSumR a) (TSumL b) = [(reverse (MLLtR:m), [])]
    -- conflict case
    makeMeasuresAux m _ _ = []

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

runMeasure :: (Show v, Eq v) => Measure -> Term v -> (Int, Maybe (Measure, Term v))
runMeasure (base, rpath) tinit =
  let (k, mmt) = iterateFixp
                    (\(k, mmt) ->
                      case mmt of
                        Nothing -> (k, mmt)
                        Just (m, t) ->
                          let ((j, mt'), m') = runMeasureSteps m t
                           in if null m'
                                then (k+j, (rpath,) <$> mt')
                              else if m == m'
                                then (k, Just (m, t)) -- ASSERT: j == 0 && mt' == Some t
                              else (k+j, (m',) <$> mt'))
                    (0, Just (base,  tinit))
   in (k, first (,rpath) <$> mmt)
  where
    runMeasureSteps :: [MeasureStep] -> Term v -> ((Int, Maybe (Term v)), [MeasureStep])
    runMeasureSteps msteps t =
      tryfoldl'
        (\(k,mt) mstep ->
          do
            t <- mt
            (j, mt') <- runMeasureStep mstep t
            return (k+j, mt'))
        (0, Just t)
        msteps

    runMeasureStep :: MeasureStep -> Term v -> Maybe (Int, Maybe (Term v))
    runMeasureStep MPairL (TPair a _) = Just (0, Just a)
    runMeasureStep MPairR (TPair _ b) = Just (0, Just b)
    runMeasureStep MSumL  (TSumL a) = Just (0, Just a)
    runMeasureStep MSumR  (TSumR a) = Just (0, Just a)
    runMeasureStep MRoll  (TRoll a) = Just (1, Just a)
    runMeasureStep MNat   (TNatLit k) = Just (0, Nothing)
    runMeasureStep MBool  (TBoolLit k) = Just (0, Nothing)
    runMeasureStep MSumR  TSumL{} = Just (0, Nothing)
    runMeasureStep MSumL  TSumR{} = Just (0, Nothing)
    runMeasureStep MLLtR  TSumL{} = Just (0, Nothing)
    runMeasureStep MRLtL  TSumR{} = Just (0, Nothing)
    runMeasureStep MLLtR  TSumR{} = Just (1, Nothing)
    runMeasureStep MRLtL  TSumL{} = Just (1, Nothing)
    runMeasureStep _ _ = Nothing

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
        (\(argp,t) ->
          let callterms = mapMaybe
                            (\(fn, t) -> if fn == name then Just t else Nothing)
                            (termToCallterms t)
          in map (argp,) callterms)
    measures = nub . concatMap (uncurry makeMeasures) $ argpairs
    reduced =
      map
        (\m ->
          (m, map
            (\(a, b) ->
              let (ka, mmta) = runMeasure m (patternToTerm a)
                  (kb, mmtb) = runMeasure m b
              in (if mmta == mmtb || (not (null mmta) && null mmtb)
                    -- Case 1: kb + |x| - (ka + |x|) == kb - ka
                    -- Case 2: kb - (ka + |x|) <= kb - ka
                    then Num (toEnum (kb - ka))
                  else Sym Na))
          argpairs))
        measures
    matrix = map snd {- . traceShowId $ -} reduced
