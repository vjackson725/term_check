
module TerminationChecking.Misc
  (
    enumerate,
    groupOnSnd
  )
where

import Data.List (partition)
import Data.List.NonEmpty (NonEmpty((:|)))

enumerate :: [a] -> [(Int, a)]
enumerate = aux 0
  where
    aux k [] = []
    aux k (x:xs) = (k,x) : aux (k+1) xs

groupOnSnd :: Eq b => [(a,b)] -> [(b, NonEmpty a)]
groupOnSnd [] = []
groupOnSnd ((a,b) : xs) =
  let (bs, xs2) = partition ((== b) . snd) xs
  in (b, a :| map fst bs) : groupOnSnd xs2
