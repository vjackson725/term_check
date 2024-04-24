{-# LANGUAGE TupleSections #-}

module TerminationChecking.Measure
  (Measure, makeMeasures, runMeasure)
where

import Debug.Trace

import Control.Monad (guard)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (Maybe, fromMaybe)
import Data.Bifunctor (first, second)
import Data.List (isSuffixOf)
import Data.List.Split (chunksOf)

import TerminationChecking.Lang

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
  deriving (Show, Eq, Ord)

-- (Base measure, Recursive measure)
type Measure = ([MeasureStep], [MeasureStep])

measureRecursive :: Eq v => v -> Term v -> [[MeasureStep]]
measureRecursive x t = measureRecursiveAux [] x t
  where
    measureRecursiveAux :: Eq v => [MeasureStep] -> v -> Term v -> [[MeasureStep]]
    measureRecursiveAux m x (TVar y) = [reverse m | x == y, not (null m)]
    measureRecursiveAux m x TUnit = []
    measureRecursiveAux m x (TBoolLit b0) = []
    measureRecursiveAux m x (TNatLit n0) = [MNat:m]
    measureRecursiveAux m x (TPair a b) =
      measureRecursiveAux (MPairL:m) x a ++ measureRecursiveAux (MPairR:m) x b
    measureRecursiveAux m x (TSumL a) = measureRecursiveAux (MSumL:m) x a
    measureRecursiveAux m x (TSumR a) = measureRecursiveAux (MSumR:m) x a
    measureRecursiveAux m x (TRoll a) = measureRecursiveAux (MRoll:m) x a
    measureRecursiveAux m x (TApp a b) = []
    measureRecursiveAux m x (TOp v) = error "unimplemented"
    measureRecursiveAux m x (TIf tc tt tf) = error "unimplemented"

makeRawMeasures :: Eq v => Pattern v -> Term v -> [Measure]
makeRawMeasures = aux []
  where
    aux :: Eq v => [MeasureStep] -> Pattern v -> Term v -> [Measure]
    aux m p (TVar x) = map (reverse m,) $ measureRecursive x (patternToTerm p)
    aux m (PVar x) t = map (reverse m,) $ measureRecursive x t
    aux _ PUnit TUnit = []
    aux _ (PBoolLit b0) (TBoolLit b1) = []
    aux _ (PNatLit n0) (TNatLit n1) = []
    aux m (PPair a0 a1) (TPair b0 b1) =
      aux (MPairL:m) a0 b0 ++ aux (MPairR:m) a1 b1
    aux m (PSumL a) (TSumL b) = aux (MSumL:m) a b
    aux m (PSumR a) (TSumR b) = aux (MSumR:m) a b
    aux m (PRoll a) (TRoll b) = aux (MRoll:m) a b
    -- different sum conflict
    aux m (PSumL a) (TSumR b) = [(reverse (MRLtL:m), [])]
    aux m (PSumR a) (TSumL b) = [(reverse (MLLtR:m), [])]
    -- conflict case
    aux m _ _ = []

orElse :: Maybe a -> Maybe a -> Maybe a
orElse ma@(Just a) _  = ma
orElse Nothing     mb = mb

makeMeasures :: Eq v => Pattern v -> Term v -> [Measure]
makeMeasures p t =
  let rawMeas = makeRawMeasures p t
      reducedMeasures =
        map
          (\(mb,mr) ->
            let mr' = reduceMeasureR mr
                mb' = until (\xs -> null mr' || (not . isSuffixOf mr') xs) (\xs -> take (length xs - length mr') xs) mb
             in (mb', mr'))
          rawMeas
   in reducedMeasures
  where
    reduceMeasureR mr =
      let divisors = do
                      d <- [1..length mr-1]
                      guard (length mr `mod` d == 0) -- only the divisors
                      return d
          mout = foldr
                    (\d ->
                      (`orElse`
                        (let chunks = chunksOf d mr
                             -- invariant: more than one chunk, by non-length divisor
                             (c : chunks') = chunks
                        in if all (c ==) chunks' then Just c else Nothing))
                    )
                    Nothing
                    divisors
       in fromMaybe mr mout


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


runMeasure :: (Show v, Eq v) => Measure -> Term v -> (Integer, Maybe (Measure, Term v))
runMeasure m t = runMeasureAux 0 m t
  where
    runMeasureAux :: (Show v, Eq v) => Integer -> Measure -> Term v -> (Integer, Maybe (Measure, Term v))
    runMeasureAux k (MPairL : mb, mr) (TPair ta _) = runMeasureAux k (mb, mr) ta
    runMeasureAux k (MPairR : mb, mr) (TPair _ tb) = runMeasureAux k (mb, mr) tb
    runMeasureAux k (MSumL  : mb, mr) (TSumL t) = runMeasureAux k (mb, mr) t
    runMeasureAux k (MSumR  : mb, mr) (TSumR t) = runMeasureAux k (mb, mr) t
    runMeasureAux k (MRoll  : mb, mr) (TRoll t) = runMeasureAux (k+1) (mb, mr) t
    runMeasureAux k (MNat   : mb, mr) (TNatLit m) | m >= 0  = (k + m, Nothing)
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
    runMeasureAux k ([], mr@(MNat   : mr')) (TNatLit m) | 0 <= m = (k + m, Nothing)
    runMeasureAux k ([], mr@(MBool  : mr')) (TBoolLit b) = (k, Nothing)
    runMeasureAux k ([], mr@(MSumR  : mr')) TSumL{} = (k, Nothing)
    runMeasureAux k ([], mr@(MSumL  : mr')) TSumR{} = (k, Nothing)
    runMeasureAux k ([], MLLtR:_) TSumL{} = (k, Nothing)
    runMeasureAux k ([], MRLtL:_) TSumR{} = (k, Nothing)
    runMeasureAux k ([], MLLtR:_) TSumR{} = (k+1, Nothing)
    runMeasureAux k ([], MRLtL:_) TSumL{} = (k+1, Nothing)
    runMeasureAux k ([], rm@(_:_)) t = (k, Just ((rm,rm), t))
    runMeasureAux k ([], []) _ = error "Bad measure"
