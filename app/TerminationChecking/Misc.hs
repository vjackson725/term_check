
module TerminationChecking.Misc
  (
    enumerate
  )
where

enumerate :: [a] -> [(Int, a)]
enumerate = aux 0
  where
    aux k [] = []
    aux k (x:xs) = (k,x) : aux (k+1) xs