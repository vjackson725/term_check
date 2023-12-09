{-# LANGUAGE TupleSections #-}

module TerminationChecking.Exec
  (
    Entry(..),
    isNum,
    theNum,
    isInf,
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
import TerminationChecking.Measure

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

data Entry = Num Double | Inf
  deriving (Show, Eq)

isNum :: Entry -> Bool
isNum Num{} = True
isNum _ = False

theNum :: Entry -> Double
theNum (Num x) = x

isInf :: Entry -> Bool
isInf Inf{} = True
isInf _ = False

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
matrixify :: (Show v, Eq v) => v -> FunDef v -> ([Measure], [[Entry]])
matrixify name fundef = (measures, matrix)
  where
    argpairs =
      fundef
      |> concatMap
        (\(argp,t) ->
          let callterms = mapMaybe
                            (\(fn, t) -> if fn == name then Just t else Nothing)
                            (termToCallterms t)
          in map (argp,) callterms)
    measures = {- traceShowId $ -} nub . concatMap (uncurry makeMeasures) $ argpairs
    reduced = {- traceShowId $ -}
      map
        (\m ->
          (m, map
            (\(a, b) ->
              let (ka, mmta) = runMeasure m (patternToTerm a)
                  (kb, mmtb) =
                    -- trace (show (patternToTerm a) ++ " vs. " ++ show b) $
                    --  trace ("(" ++ show ka ++ " + " ++ show mmta ++ ") - (" ++ show kb ++ " + " ++ show mmtb) $
                    runMeasure m b
              in (if (mmta == mmtb || (not (null mmta) && null mmtb))
                    -- Case 1: kb + |x| - (ka + |x|) == kb - ka
                    -- Case 2: kb - (ka + |x|) <= kb - ka
                    then Num (fromInteger (kb - ka))
                  else Inf))
          argpairs))
        measures
    matrix = map snd reduced
