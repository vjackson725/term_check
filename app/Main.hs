
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

{-lexic' a = let b = lexic a a 
           in if b == a then Nothing else b-}

--toMatrix :: [[R]] -> Matrix R
--toMatrix (a:as) = matrix (length a) (join (a:as))

--fromMatrix :: Matrix r -> [[r]]
--fromMatrix ((a><b) xs) = let (x, y) = splitAt a xs
 --                        in x:(fromMatrix y)

--lin :: Tmatrix -> Tmatrix

--intSolve a b = do 
    --rat <- linearSolve a b

toLists' a = toLists (tr a :: Matrix Double)
fromLists' a = tr (fromLists a) :: Matrix Double

addId a = a ++ (toLists' (ident (length a))) 



{-nullSum (a:as) = foldl listAdd (zero a) a'''
    where
        a' = toLists' (nullspace (fromLists' (addId (a:as))))
        

        a'' = filter sameSign a'

        a''' = map (take (length a)) a''

        sameSign (x:xs) | x >= 0     = and (map (>= 0) xs)
                        | otherwise  = and (map (<= 0) xs)

        listAdd (x:xs) (y:ys) = (x+y) : listAdd xs ys
        listAdd []     []     = []
        listAdd _      _      = error "length mismatch"-}


neg1 [] = []
neg1 (x:xs) = (-1):(neg1 xs)

bindLists []     = []
bindLists (x:xs) = (x :&: (-1, 0)) : (bindLists xs)
-- | b' == zero b -> Nothing

lin a = let (a', rest) = extract a [] []
            --b = nullspace (fromLists (addId a'))
            --b  = nullSum a'
            rows = toLists $ tr (fromLists a')
            prob = Minimize $ map sum a'

            constr = Dense $ bindLists rows

            Optimal (b, bs) = simplex prob constr []

            b' = toEnt (toList ((fromLists' a') #> (vector bs)))
          in (b':rest)
            --b = linearSolveSVD (fromLists' a') (matrix 1 (neg1 a'))
            --b' = toEnt (toList ((fromLists' a') #> (vector b)))
            --b' = toEnt (join (toLists' b))
          {-in case () of _
                         | vecCheck b' == Le || vecCheck b' == Leq -> return (b':rest)
                         | vecCheck b' == Na                       -> Nothing-}
  {-where
    isInt []           = True
    isInt ((Num x):xs) = isInt xs
    isInt ((Sym x):xs) = False 

    toInt [] = []
    toInt ((Num x):xs) = x:(toInt xs) 

    toEnt [] = []
    toEnt (x:xs) = (Num x):(toEnt xs)

    --extract :: [[Entry]] -> [[Int]] -> [[Entry]] -> ([[Int]], [[Entry]])
    extract [] num sym = (num, sym)
    extract (x:xs) num sym | isInt x   = extract xs ((toInt x):num) sym
                            | otherwise = extract xs num (x:sym)-}

isInt []           = True
isInt ((Num x):xs) = isInt xs
isInt ((Sym x):xs) = False 

toInt' [] = []
toInt' ((Num x):xs) = x:(toInt' xs) 

toEnt [] = []
toEnt (x:xs) = (Num x):(toEnt xs)

    --extract :: [[Entry]] -> [[Int]] -> [[Entry]] -> ([[Int]], [[Entry]])
extract [] num sym = (num, sym)
extract (x:xs) num sym | isInt x   = extract xs ((toInt' x):num) sym
                       | otherwise = extract xs num (x:sym)

lin' a = let b = lin a
         in case () of _
                        | length b == 1 && reduced (mconcat b) -> (True, b)
                        | otherwise                            -> (False, b)
          
--termCheck :: Tmatrix -> Bool
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

{-termCheck' a | b == Nothing = False
             | otherwise    = True
             where
                 b = termCheck a-}
--solveIntegerLinearEqs Z3 [[Int]] (A) [Int] (b)
-- solveIntegerLinearEqs Z3 A (zero A)
--termCheck :: [[Int]] -> Bool 
-- search for 

--termCheck (x:xs) = 
  --  where

main = putStrLn $ show $ termCheck [[]]