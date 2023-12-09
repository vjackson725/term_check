module TerminationChecking.Solver
  ( TermResult
  , Measure
  , solveMat
  )
where

import Debug.Trace

import Data.List (splitAt, replicate, sort, partition, transpose)
import Data.Maybe (mapMaybe)
import Data.Bifunctor (bimap, second)
import Numeric.LinearAlgebra (vector, (#>), (<#), toList, toLists, fromList, fromLists, tr, ident)
import Numeric.LinearProgramming
import Text.Parsec (parse)

import qualified Data.Map as M

import TerminationChecking.Lang ((|>))
import TerminationChecking.Measure (Measure)
import TerminationChecking.Exec (Entry(..), isNum, theNum, isInf)
import TerminationChecking.Parser (parse_program)

----------
-- Misc --
----------

enumerate :: [a] -> [(Int, a)]
enumerate xs = aux 0 xs
  where
    aux _ [] = []
    aux k (x : xs) = (k, x) : aux (k+1) xs

selectIdxs :: [Int] -> [a] -> [a]
selectIdxs is xs = selectIdxsAux (sort is) xs 0
  where
    selectIdxsAux :: [Int] -> [a] -> Int -> [a]
    selectIdxsAux _ [] _ = []
    selectIdxsAux [] _ _ = []
    selectIdxsAux (i:is) (x:xs) j =
      if i < j then
        selectIdxsAux is (x:xs) j
      else if i == j then
        x : selectIdxsAux (i:is) xs (j+1)
      else -- i > j
        selectIdxsAux (i:is) xs (j+1)

dropIdxs :: [Int] -> [a] -> [a]
dropIdxs is xs = dropIdxsAux (sort is) xs 0
  where
    dropIdxsAux :: [Int] -> [a] -> Int -> [a]
    dropIdxsAux _ [] _ = []
    dropIdxsAux [] xs _ = xs
    dropIdxsAux (i:is) (x:xs) j =
      if i < j then
        dropIdxsAux is (x:xs) j
      else if i == j then
        dropIdxsAux (i:is) xs (j+1)
      else -- i > j
        x : dropIdxsAux (i:is) xs (j+1)

snoc :: [a] -> a -> [a]
snoc [] y = [y]
snoc (x:xs) y = x : (snoc xs y)

-----------
-- Types --
-----------

-- type TermResult = Bool
type TermResult m = Maybe [[(Double, m)]]

-- A matrix of numbers, represented as a list of columns
type NumMatrix = [[Double]]

-- A matrix of entries, represented as a list of columns
type TMatrix = [[Entry]]

-------------------
-- Linear Solver --
-------------------

{-
  Solve the Maximal Negative Entries problem for matrix a.

  Returns the weights vector and the solution vector, in that order.

  == Maximal Negative Entries ==
  Finds a linear combination of the columns without symbols such that all entries
  are less than or equal to 0 and the number of non-zero entries are maximized
  by solving the following linear programming problem:

  maximise:
    sum y
  such that:
    Ax + y <= 0
    0 <= x
    0 <= y <= 1
  (where <= on vectors is taken pointwise).

  Because of the limitations of the linear programming library we're using,
  x, y and z are represented as a single big vector
    x ++ y ++ z.
  The actual program we solve is more like

  maximise:
    ( 0 1 ) * ( x y )
  subject to:
    ( A I ) * ( x y ) <= 0
    0 <= x
    0 <= y <= 1
-}
lin :: NumMatrix -> ([Double], [Bool])
lin numMat =
  let -- Switch from list of columns to list of rows
      rows = transpose numMat
      -- useful lengths
      lenX = length numMat
      lenY = length rows
      -- Generate problem objective: Maximise sum y
      prob = Maximize $ replicate lenX 0 ++ replicate lenY 1
      -- Generate constraint matrix
      idMat = toLists $ ident lenY
      -- ( A I )
      constrMat = zipWith (++) rows idMat
      constr = Dense $ map (:<=: 0) constrMat
      -- set up bounds
      bounds = map (\x -> x :&: (0,1)) [lenX + 1..lenX + lenY]
      -- solve the problem
      solution = simplex prob constr bounds
  in
    case solution of
        Optimal (objective, allWeights) ->
          let
            weights = allWeights |> take lenX
            selected = allWeights |> drop lenX |> map (> 0)
          in (weights, selected)
        _ -> error "Failed to solve linear program; this should be impossible!"

-------------------------------
-- Solve the overall problem --
-------------------------------

{-
  Split a matrix into the pure numeric columns and the the mixed numeric/inf
  columns, and record the original indices.
-}
numericFilterMatrix :: TMatrix -> (([Int], NumMatrix), ([Int], TMatrix))
numericFilterMatrix m =
  let mIndexed = enumerate m
      (numericCols, mixedCols) = partition (all isNum . snd) mIndexed
      (numericIdxs, numericMatrix) = second (map (map theNum)) $ unzip numericCols
      (mixedIdxs, mixedMatrix) = unzip mixedCols
   in
    ((numericIdxs, numericMatrix), (mixedIdxs, mixedMatrix))

{-
  Do the linear/lexicographic loop
-}
calculateTerminationMeasure :: Show m => [m] -> TMatrix -> [[(Double, m)]] -> Maybe [[(Double, m)]]
calculateTerminationMeasure measures mat out =
  let ((is, matNumeric), (js, matMixed)) = {- traceShowId $ -} numericFilterMatrix mat
   in if null matNumeric
      then Nothing
      else
        let
          (weights, sol) = lin matNumeric
          colsPicked = zip is weights |> mapMaybe (\(k, w) -> if w > 0 then Just k else Nothing)
          rowsToElim = map fst . filter snd . enumerate $ sol
          weightedMeasures = {- traceShowId $ -} zip weights (selectIdxs colsPicked measures)
          measuresRemaining = {- traceShowId $ -} selectIdxs js {- $ traceShowId -} measures
          newOut = snoc out weightedMeasures
        in if null colsPicked
           then Nothing
           else if null matMixed
           then Just newOut
           else
              calculateTerminationMeasure
                measuresRemaining
                (map (dropIdxs rowsToElim) matMixed)
                newOut

solveMat :: [String] -> TMatrix -> TermResult String
solveMat measNames termmat =
  calculateTerminationMeasure measNames termmat []
