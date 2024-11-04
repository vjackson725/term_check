{-# LANGUAGE TupleSections, ScopedTypeVariables, LambdaCase, DeriveFunctor, DeriveFoldable #-}

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
import Data.Bifoldable (bifoldr)
import Data.Maybe (mapMaybe, maybeToList, fromMaybe)
import Data.List (nub, permutations)
import Data.List.NonEmpty (NonEmpty)
import Data.Set (Set)
import Data.Ratio ((%))
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

import Debug.Trace

import TerminationChecking.Lang
import TerminationChecking.Measure
import TerminationChecking.Misc

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

-------------------------------------------------
-- Term decrease matrix construction algorithm --
-------------------------------------------------

--
-- Matrix Entries
--

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

--
-- Approximate Substitution
--

approxSub :: (Show v, Eq v) =>
  (Prob, Rational, Maybe (Measure, Term v)) ->
  (Rational, Maybe (Measure, Term v)) ->
  Entry
approxSub (p, x, ta) (y, tb)
  | p <= 0
  = error "approxSub precondition violation, p <= 0"
  | p > 1
  = error "approxSub precondition violation, p > 1"
  | (ta == tb && p == 1) || null tb
      -- Case 1: x + p*|t| - (y + |t|)
      --         == (x - y) + (p-1)*|t|
      --         == (x - y)             (when p == 1)
      -- Case 2a: x + p*|ta| - y <= x - y
      -- Case 2b: x - y
  = Num (x - y)
  | otherwise
  = Inf

--
-- Choice Tree
--

-- | The choice tree datastructure is a representation of the 'choice structure'
--   of a recursive function, that being a reflection of the structure of the
--   term, except only paying attention to the probabilistic choice, and
--   erasing the differences between constructors.
--     We use this datastructure to extract the argument structure of recursive
--   functions together with the probability of tthat recursive call occuring.
data ChoiceTree a =
  ProbChoice Prob (ChoiceTree a) (ChoiceTree a) |
  Split (ChoiceTree a) (ChoiceTree a) |
  DataLeaf a |
  EmptyLeaf
  deriving (Eq, Show, Functor, Foldable)

extractChoiceTreeTm :: Eq v => v -> Term v -> ChoiceTree (Term v)
extractChoiceTreeTm funnm = aux
  where
    aux (TVar x)   = EmptyLeaf
    aux TUnit      = EmptyLeaf
    aux TNatLit{}  = EmptyLeaf
    aux TBoolLit{} = EmptyLeaf
    aux (TPair t0 t1) = Split (aux t0) (aux t1)
    aux (TSumL t) = aux t
    aux (TSumR t) = aux t
    aux (TRoll t) = aux t
    aux (TApp (TVar f) t) | f == funnm = Split (DataLeaf t) (aux t)
                          | otherwise  = aux t
    aux (TApp t0 t1) = Split (aux t0) (aux t1)
    aux (TOp opnm) = error "undefined"
    aux (TIf tc tt tf) = Split (aux tt) (aux tf)
    aux (TPChoice p t0 t1) = ProbChoice p (aux t0) (aux t1)

extractChoiceTrees :: Eq v => v -> FunDef v -> [(Pattern v, ChoiceTree (Term v))]
extractChoiceTrees funnm = map (second (extractChoiceTreeTm funnm))

-- | A condensed choice tree, with splits all distributed to the toplevel.
type CondensedChoiceTree a = [[(Prob, a)]]

-- | A choice tree is condensed by weighting each datum by the probability it
--   occurs, and taking _all combinations_ of data from different sides of a
--   split.
condenseChoiceTree :: ChoiceTree a -> CondensedChoiceTree a
condenseChoiceTree (ProbChoice p a b) =
  do
    ca <- condenseChoiceTree a
    cb <- condenseChoiceTree b
    return $ map (first (p *)) ca ++ map (first ((1-p) *)) cb
condenseChoiceTree (Split a b) = condenseChoiceTree a ++ condenseChoiceTree b
condenseChoiceTree (DataLeaf x) = [[(1, x)]]
-- NB: an empty leaf translates to _one_ pchoice, which is empty.
condenseChoiceTree EmptyLeaf = [[]]

--
-- Matrixify
--

makeRow :: forall v. (Show v, Eq v) =>
            [Measure]
            -> Pattern v
            -> [(Prob, Term v)]
            -> Maybe [Entry]
makeRow measures lArg rArgs
  | null rArgs = Nothing
  | otherwise =
    let lArgMeasured :: [(Rational, MeasureApp v)]
        lArgMeasured = map (\m -> runMeasure m (patternToTerm lArg)) measures
        -- The outer list is an entry per each measure, the inner list is an entry
        -- per each rArg.
        rArgsMeasured :: [[((Prob, Rational), MeasureApp v)]]
        rArgsMeasured =
          map
            (\m ->
              map (\(p, tm) -> (\(x,m) -> ((p,x),m)) $ runMeasure m tm) rArgs)
            measures
        pairedMeasuredArgs ::
          [((Rational, MeasureApp v), [((Prob, Rational), MeasureApp v)])]
        pairedMeasuredArgs = zip lArgMeasured rArgsMeasured
        subtractedRow :: [Entry]
        subtractedRow =
          map
            (\case
                (lRes, rRess) ->
                  let grouped :: [(MeasureApp v, NonEmpty (Prob, Rational))]
                      grouped = groupOnSnd rRess
                      reduced :: [(MeasureApp v, (Prob, Rational))]
                      reduced = map
                                  (second
                                    (foldr
                                      (\(p,x) (pp,xx) -> (p + pp, runProb p*x + xx))
                                      (0, 0)))
                                  grouped
                  in case reduced of
                        [(mb,(pp,x))] -> approxSub (pp,x,mb) lRes
                        _ -> Inf)
            pairedMeasuredArgs
    in Just subtractedRow

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
matrixify funnm fundef = (measures, matrix)
  where
    argpairs :: [(Pattern v, [(Prob, Term v)])]
    argpairs = concatMap (uncurry (\pat -> map (pat,) . condenseChoiceTree))
                $ extractChoiceTrees funnm fundef
    measures :: [Measure]
    measures = {- traceShowId $ -}
      argpairs
      |> concatMap (uncurry (\pat -> concatMap (makeMeasures pat . snd)))
      |> nub
    matrix :: [[Entry]]
    matrix = {- traceShowId $ -}
      mapMaybe (uncurry (makeRow measures)) argpairs
