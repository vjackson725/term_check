{-# LANGUAGE TupleSections #-}

module TerminationChecking.Exec
  (
    Entry(..),
    isNum,
    isSym,
    theNum,
    theSym,
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
    measureRecursiveAux m x (TVar y) = [reverse m | x == y, not (null m)]
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
    makeMeasuresAux m (PSumL a) (TSumL b) = makeMeasuresAux (MSumL:m) a b
    makeMeasuresAux m (PSumR a) (TSumR b) = makeMeasuresAux (MSumR:m) a b
    makeMeasuresAux m (PRoll a) (TRoll b) = makeMeasuresAux (MRoll:m) a b
    -- different sum conflict
    makeMeasuresAux m (PSumL a) (TSumR b) = [(reverse (MRLtL:m), [])]
    makeMeasuresAux m (PSumR a) (TSumL b) = [(reverse (MLLtR:m), [])]
    -- conflict case
    makeMeasuresAux m _ _ = []

{-
  This function takes a measure and a term, and runs the measure on the term to
  find the structural size of the term.

  There are two components to a measure, the base, and the recursive part.
  The base is run till it is exhausted or fails to match, and then the recursive
  part is unfolded into the base and execution continues.

  Execution of a measure finishes when either a measure is applied to something
  it does not match, or the measure reaches a base case (MNat, MBool, MLLtR, MRLtL).

  The result can be a suspended symbolic value, as the measure may be reduced to
  a measure applied to a variable, or to a measure applied to something which
  it is not a match for.
-}


runMeasure :: (Show v, Eq v) => Measure -> Term v -> (Int, Maybe (Measure, Term v))
runMeasure m t = runMeasureAux 0 m t
  where
    runMeasureAux :: (Show v, Eq v) => Int -> Measure -> Term v -> (Int, Maybe (Measure, Term v))
    runMeasureAux k (MPairL : mb, mr) (TPair ta _) = runMeasureAux k (mb, mr) ta
    runMeasureAux k (MPairR : mb, mr) (TPair _ tb) = runMeasureAux k (mb, mr) tb
    runMeasureAux k (MSumL  : mb, mr) (TSumL t) = runMeasureAux k (mb, mr) t
    runMeasureAux k (MSumR  : mb, mr) (TSumR t) = runMeasureAux k (mb, mr) t
    runMeasureAux k (MRoll  : mb, mr) (TRoll t) = runMeasureAux (k+1) (mb, mr) t
    runMeasureAux k (MNat   : mb, mr) (TNatLit m)  = (k, Nothing)
    runMeasureAux k (MBool  : mb, mr) (TBoolLit b) = (k, Nothing)
    runMeasureAux k (MSumR  : mb, mr) TSumL{} = (k, Nothing)
    runMeasureAux k (MSumL  : mb, mr) TSumR{} = (k, Nothing)
    runMeasureAux k (MLLtR  : mb, mr) TSumL{} = (k, Nothing)
    runMeasureAux k (MRLtL  : mb, mr) TSumR{} = (k, Nothing)
    runMeasureAux k (MLLtR  : mb, mr) TSumR{} = (k+1, Nothing)
    runMeasureAux k (MRLtL  : mb, mr) TSumL{} = (k+1, Nothing)
    runMeasureAux k m@(_:_, _) t = (k, Just (m, t))
    runMeasureAux k ([], mr@(MPairL : mr')) (TPair ta _) = runMeasureAux k (mr', mr) ta
    runMeasureAux k ([], mr@(MPairR : mr')) (TPair _ tb) = runMeasureAux k (mr', mr) tb
    runMeasureAux k ([], mr@(MSumL  : mr')) (TSumL t) = runMeasureAux k (mr', mr) t
    runMeasureAux k ([], mr@(MSumR  : mr')) (TSumR t) = runMeasureAux k (mr', mr) t
    runMeasureAux k ([], mr@(MRoll  : mr')) (TRoll t) = runMeasureAux (k+1) (mr', mr) t
    runMeasureAux k ([], mr@(MNat   : mr')) (TNatLit m)  = (k, Nothing)
    runMeasureAux k ([], mr@(MBool  : mr')) (TBoolLit b) = (k, Nothing)
    runMeasureAux k ([], mr@(MSumR  : mr')) TSumL{} = (k, Nothing)
    runMeasureAux k ([], mr@(MSumL  : mr')) TSumR{} = (k, Nothing)
    runMeasureAux k ([], MLLtR:_) TSumL{} = (k, Nothing)
    runMeasureAux k ([], MRLtL:_) TSumR{} = (k, Nothing)
    runMeasureAux k ([], MLLtR:_) TSumR{} = (k+1, Nothing)
    runMeasureAux k ([], MRLtL:_) TSumL{} = (k+1, Nothing)
    runMeasureAux k ([], rm@(_:_)) t = (k, Just ((rm,rm), t))
    runMeasureAux k ([], []) _ = error "Bad measure"

data Val = Na | Le | Leq
  deriving (Show, Eq)

data Entry = Num Double | Sym Val
  deriving (Show, Eq)

isNum :: Entry -> Bool
isNum Num{} = True
isNum _ = False

isSym :: Entry -> Bool
isSym Sym{} = True
isSym _ = False

theNum :: Entry -> Double
theNum (Num x) = x

theSym :: Entry -> Val
theSym (Sym x) = x

{-
  Turns a function definition (along with the name of the function) into an
  entry matrix. (An entry matrix is a matrix of `Entry`s where the rows
  correspond to recursive calls, and the columns to measures.)

  1. Firstly, argument-pairs are found by recursion. Argument pairs are the
     term passed to a case in the function, paired with the term passed to
     a recursive call to that same function, from that case.
  2. Measures are generated according to the `makeMeasures` function,
     by inspection of the argpairs.
  3. Then, the measures are run on the original-recursive term pairs, to find
     the *structural* decrease between these terms.
     (This reduction is done as a separate step so we have a representation of
      the measure we can return later, although we don't do so at the moment.)
  4. These reduced values are the entries in the output entry matrix.
-}
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
    measures = traceShowId $ nub . concatMap (uncurry makeMeasures) $ argpairs
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
