{-# LANGUAGE TupleSections,  ScopedTypeVariables #-}

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
import Data.Ratio ((%))
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
eval st TPChoice{} =
  error "not implemented in this semantics"
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

type ProbTerm v = (Rational, Term v)

termToCallterms :: Term v -> [(v, ProbTerm v)]
termToCallterms (TVar x)   = []
termToCallterms TUnit      = []
termToCallterms TNatLit{}  = []
termToCallterms TBoolLit{} = []
termToCallterms (TPair t0 t1) =
  termToCallterms t0 ++ termToCallterms t1
termToCallterms (TSumL t) = termToCallterms t
termToCallterms (TSumR t) = termToCallterms t
termToCallterms (TRoll t) = termToCallterms t
termToCallterms (TApp (TVar f) t) =
  (f, (1 % 1, t)) : termToCallterms t
termToCallterms (TApp t0 t1) =
  termToCallterms t0 ++ termToCallterms t1
termToCallterms (TOp v) = error "undefined"
termToCallterms (TIf tc tt tf) =
  termToCallterms tt ++ termToCallterms tf
termToCallterms (TPChoice p t0 t1) =
  map (second (first ((*) p))) (termToCallterms t0)
  ++ map (second (first ((*) (1 - p)))) (termToCallterms t1)

data Entry = Num Rational | Inf
  deriving (Show, Eq)

isNum :: Entry -> Bool
isNum Num{} = True
isNum _ = False

theNum :: Entry -> Rational
theNum (Num x) = x

isInf :: Entry -> Bool
isInf Inf{} = True
isInf _ = False

approxSub :: (Show v, Eq v) => Measure -> Pattern v -> Term v -> Entry
approxSub m a b =
  let (ka, mmta) = runMeasure m (patternToTerm a)
      (kb, mmtb) = runMeasure m b
  in {- trace (show (ka, mmta) ++ " <? " ++ show (kb, mmtb)) $ -}
      (if (mmta == mmtb || (not (null mmta) && null mmtb))
        -- Case 1: kb + |x| - (ka + |x|) == kb - ka
        -- Case 2: kb - (ka + |x|) <= kb - ka
        then Num (fromInteger (kb - ka))
      else Inf)

-- This is probably the wrong behaviour
entryPlus :: Entry -> Entry -> Entry
entryPlus (Num x) (Num y) = Num (x + y)
entryPlus Inf y = Inf
entryPlus x Inf = Inf

entryMult :: Entry -> Entry -> Entry
entryMult (Num x) (Num y) = Num (x * y)
entryMult _ Inf = Inf
entryMult Inf _ = Inf

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
matrixify :: forall v. (Show v, Eq v) => v -> FunDef v -> ([Measure], [[Entry]])
matrixify name fundef = (measures, matrix)
  where
    argpairs :: [(Pattern v,[(Rational,Term v)])]
    argpairs =
      fundef
      |> map
          (\(argp,t) ->
            let callterms =
                  mapMaybe
                    (\(fn, pt) -> if fn == name then Just pt else Nothing)
                    (termToCallterms t)
            in (argp, callterms))
    measures :: [Measure]
    measures = {- traceShowId $ -}
      argpairs
      |> concatMap (\(pat,ts) -> concatMap (\(_,t) -> makeMeasures pat t) ts)
      |> nub
    matrix :: [[Entry]]
    matrix = {- traceShowId $ -}
      argpairs
      |> mapMaybe
          (\(a,bs) ->
            if null bs
            then Nothing
            else Just $
              foldr
                (\(p,b) ->
                  let ks = map (\m -> Num p `entryMult` approxSub m a b) measures
                  in zipWith entryPlus ks)
                (replicate (length measures) (Num 0))
                bs)
      -- (\m ->
      --   concatMap
      --     (\(a,bs) -> map (\(_,b) -> approxSub m a b) bs)
      --     argpairs)
