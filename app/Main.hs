import PatternLambda
import Data.List (splitAt)

import Numeric.LinearAlgebra
import Numeric.LinearProgramming


data Val = Na | Leq | Le 

instance Show Val where
    show Na  = "?"
    show Leq = "<="
    show Le  = "<"

instance Eq Val where
    (==) Na Na   = True
    (==) Leq Leq = True
    (==) Le Le   = True
    (==) _ _     = False

data Entry = Num Double | Sym Val deriving (Eq, Show)
type Tmatrix = [[Entry]]


--zero :: [Int] -> [Int]
zero [] = []
zero (x:xs) = 0 : (zero xs)

vecCheck :: [Entry] -> Val
vecCheck vec | vec == [] = Na
             | otherwise = go True vec
    where
        go v [] | v == True           = Le
                | otherwise           = Leq
        go v ((Num y):ys) | y > 0     = Na
                          | y == 0    = go False ys
                          | otherwise = go v ys
        go v ((Sym y):ys) | y == Na   = Na
                          | y == Le   = go v ys
                          | otherwise = go False ys


reduced v | vecCheck v == Le = True
          | otherwise        = False  
--removeIndex :: Int -> [a] -> [a]
removeIndex n xs = let (x, y:ys) = splitAt n xs 
                   in (x ++ ys)

--lexic :: Tmatrix -> Tmatrix
lexic [] _ = []
lexic ret [] = ret
lexic ret (x:xs) | vecCheck x == Na = lexic ret xs
                 | otherwise        = lexic (reduce 0 x ret) xs
               where
                   reduce n [] a = a
                   reduce n ((Num y):ys) a | y < 0     = reduce n ys (map (removeIndex n) a)
                                           | otherwise = reduce (n+1) ys a
                   reduce n ((Sym y):ys) a | y == Le || y == Leq = reduce n ys (map (removeIndex n) a)
                                           | otherwise = reduce (n+1) ys a
                    


isEmpty []      = True
isEmpty ([]:xs) = isEmpty xs
isEmpty _       = False

lexic' a | b == a = (False, [])
         | isEmpty b = (True, [])
         | otherwise = (False, b)
         where
             b = lexic a a

toLists' a = toLists (tr a :: Matrix Double)
fromLists' a = tr (fromLists a) :: Matrix Double

addId a = a ++ (toLists' (ident (length a))) 



bindLists [] _ _ = []
bindLists (b:bs) n lenx = ((idRow 0) :&: (0, 1)) : (b :==: 0) : (bindLists bs (n+1) lenx)
    where
        m = length b

        idRow k | k == n + lenx   = 1:idRow (k+1)
                | k == m          = []
                | otherwise       = 0:idRow (k+1)

split :: [a] -> ([a], [a])
split myList = splitAt (((length myList) + 1) `div` 2) myList

listAdd (x:xs) (y:ys) = (x+y) : (listAdd xs ys)
listAdd [] [] = []
listAdd _ _ = error "length mismatch"

pointwiseConc (x:xs) (y:ys) = (x++y) : (pointwiseConc xs ys)
pointwiseConc [] [] = []
pointwiseConc _ _ = error "length mismatch"

{-
Finds a linear combination of the columns without symbols such that all entries
are less than or equal to 0 and the number of non-zero entries are maximized
by solving the following linear programming problem:

maximise sum y

Ax + y + z = 0
x >= 0
z >= 0
0 <= y <= 1

where relational operators are taken pointwise.

Because of the limitations of the linear programming library we're using, x, y and z are represented
as 1 vector x ++ y ++ z, and we just work with the appropriate parts of that big vector.
-}
lin a = let (nums, rest) = extract a [] []
            
            -- List of rows
            rows = toLists $ tr (fromLists nums) :: [[Double]]

            -- Maximise sum y
            prob = Maximize $ (sumy nums rows)

            idMat = toLists $ ident (length rows)

            constrMat = pointwiseConc rows (pointwiseConc idMat idMat)
            constr = Dense $ bindLists constrMat 0 (length nums)

            Optimal (b, bs) = simplex prob constr []

            x = take (length nums) bs
            x' = toEnt (toList ((fromLists' nums) #> (vector x)))
          in (x':rest)
  where
    isInt []           = True
    isInt ((Num x):xs) = isInt xs
    isInt ((Sym x):xs) = False 

    toInt' [] = []
    toInt' ((Num x):xs) = x:(toInt' xs) 

    toEnt [] = []
    toEnt (x:xs) = (Num x):(toEnt xs)

    extract [] num sym = (num, sym)
    extract (x:xs) num sym | isInt x   = extract xs ((toInt' x):num) sym
                           | otherwise = extract xs num (x:sym)

    sumy (x:xs) ys = 0:(sumy xs ys)
    sumy [] ys     = go ys 0
        where
            go [] 0     = []
            go [] n     = 0:(go [] (n-1))
            go (k:ks) n = 1:(go ks (n+1))
                       


lin' a = let (b:bs) = lin a
         in case () of _
                        | reduced b -> (True, (b:bs))
                        | otherwise -> (False, (b:bs))
          

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
          if a'' == []
          then
            v'
          else
            termCheck a''

main = putStrLn $ show $ termCheck [[]]

checkTermination :: Ord v => v -> FunDef v -> Bool
checkTermination name fun = termCheck (matrixify name fun)

{-f (x:xs) y (z:z':zs) v w = f xs y zs (0:0:0:0:v) (0:w)
f x (y:ys) (z:zs) v w = f (listAdd x x) ys zs (0:v) (0:w)
f x y z (v:v':v'':vs) w = f x (listAdd y y) (0:z) vs (0:w)
f _ _ _ _ w = w-}