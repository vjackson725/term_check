module TerminationChecking.Solver
  (TermResult, solveMat)
where


import Data.List (splitAt, replicate)
import Numeric.LinearAlgebra
import Numeric.LinearProgramming
import Text.Parsec (parse)

import qualified Data.Map as M

import TerminationChecking.Lang
import TerminationChecking.Exec (Entry(..), isNum, theNum, Val(..))
import TerminationChecking.Parser (parse_program)

{-
Finds a linear combination of the columns without symbols such that all entries
are less than or equal to 0 and the number of non-zero entries are maximized
by solving the following linear programming problem:

maximise:
  sum y
such that:
  Ax + y + z = 0
  0 <= x
  0 <= z
  0 <= y <= 1
(where <= on vectors is taken pointwise).

Because of the limitations of the linear programming library we're using, x, y and z are represented
as 1 vector x ++ y ++ z, and we just work with the appropriate parts of that big vector.
-}


type TermResult = Bool
-- type TermResult = [(Integer, Measure)]

type Tmatrix = [[Entry]]

solveMat :: Tmatrix -> TermResult
solveMat termmat = null termmat || termCheck termmat

vecCheck :: [Entry] -> Val
vecCheck vec | null vec = Na
             | otherwise = go True vec
    where
-- TODO: make this simpler
        go v [] | v                   = Le
                | otherwise           = Leq
        go v (Num y : ys) | y > 0     = Na
                          | y == 0    = go False ys
                          | otherwise = go v ys
        go v (Sym y : ys) | y == Na   = Na
                          | y == Le   = go v ys
                          | otherwise = go False ys

isReduced :: [Entry] -> Bool
isReduced v = vecCheck v == Le

removeIndex :: Int -> [a] -> [a]
removeIndex n xs = let (x, y:ys) = splitAt n xs
                   in (x ++ ys)

lexic :: Tmatrix -> Tmatrix -> Tmatrix
lexic [] _ = []
lexic ret [] = ret
lexic ret (x:xs) | vecCheck x == Na = lexic ret xs
                 | otherwise        = lexic (reduce 0 x ret) xs
               where
                   reduce n [] a = a
                   reduce n (Num y : ys) a | y < 0     = reduce n ys (map (removeIndex n) a)
                                           | otherwise = reduce (n+1) ys a
                   reduce n (Sym y : ys) a | y == Le || y == Leq = reduce n ys (map (removeIndex n) a)
                                           | otherwise = reduce (n+1) ys a

lexic' :: Tmatrix -> (Bool, Tmatrix)
lexic' a | b == a     = (False, [])
         | all null b = (True, [])
         | otherwise  = (False, b)
  where
    b = lexic a a

toLists' a = toLists (tr a :: Matrix Double)
fromLists' a = tr (fromLists a) :: Matrix Double

addId a = a ++ toLists' (ident (length a))


bindLists [] _ _ = []
bindLists (b:bs) n lenx = (idRow 0 :&: (0, 1)) : (b :==: 0) : bindLists bs (n+1) lenx
    where
      idRow k | k == n + lenx = 1:idRow (k+1)
              | k == length b = []
              | otherwise     = 0:idRow (k+1)

split :: [a] -> ([a], [a])
split myList = splitAt ((length myList + 1) `div` 2) myList

lin a = let (nums, rest) = extract a [] []

            -- List of rows
            rows = toLists $ tr (fromLists nums) :: [[Double]]

            -- Maximise sum y
            prob = Maximize $ sumy nums rows

            idMat = toLists $ ident (length rows)

            constrMat = zipWith (++) rows (zipWith (++) idMat idMat)
            constr = Dense $ bindLists constrMat 0 (length nums)

            Optimal (b, bs) = simplex prob constr []

            x = take (length nums) bs
            x' = map Num (toList (fromLists' nums #> vector x))
          in (x':rest)
  where
    extract [] num sym = (num, sym)
    extract (x:xs) num sym | all isNum x = extract xs (map theNum x : num) sym
                           | otherwise   = extract xs num (x:sym)

    sumy xs ys = map (const 0) xs ++ map (const 1) ys ++ map (const 0) ys



lin' a =
  let (b:bs) = lin a in (isReduced b, b:bs)


-- Checks if a function with associated matrix `a` terminates
termCheck a =
    let
        (v, a') = lin' a
    in
      if v
      then
        v
      else
        let (v', a'') = lexic' a'
        in
          if null a''
          then
            v'
          else
            termCheck a''
