
module TerminationChecking.Examples where

import TerminationChecking.Exec

-- Ought to give matrix [[-1]]
f (x:xs) = f xs
f [] = ()

data BTree = B BTree BTree | L

g (B l r) = (g l) + (g r)
g L = 1

{-

-- Ought to have matrix [[-1, -1]]

[ ( PRoll (PSumR (PPair (PVar 'x') (PVar 'y'))), TRoll (TSumR (TVar 'y')) ), ( PRoll (PSumL PUnit), TRoll (TSumL TUnit) )]

tlet 'f' [ ( PRoll 'y' (PSumR (PPair (PVar 'x') (PVar 'y'))), TApp 'f' (TRoll 'y' (TSumR (TVar 'y'))) ), ( PRoll 'y' (PSumL PUnit), TRoll 'y' (TSumL TUnit) )]

[ ( PRoll 'y' (PSumR (PPair (PVar 'x') (PVar 'y'))), TRoll 'y' (TSumR (TVar 'y')) ), ( PRoll 'y' (PSumL PUnit), TRoll 'y' (TSumL TUnit) )]

[ ( PRoll (PSumR (PPair (PVar "x") (PRoll (PSumR (PPair (PVar "y") (PVar "z")))))), TApp (TVar "foo") (TVar "z") ), ( PRoll (PSumL PUnit), TRoll (TSumL TUnit) )]
--state = M.fromList [("foo", VFunDef [(PVar "x", TPair (TVar "x") (TVar "x"))])]

state = Map.fromList [("foo", VFunDef [ ( PRoll "y" (PSumR (PPair (PVar "x") (PVar "y"))), TApp (TVar "foo") (TRoll "y" (TSumR (TVar "y"))) ), ( PRoll "y" (PSumL PUnit), TRoll "y" (TSumL TUnit) )])]


state = Map.fromList [("foo", VFunDef [(PVar "x", TApp (TVar "foo") TUnit)])]
-- Ought to give matrix [-1]
-- matrixify "foo" [("foo", VFunDef [ ( PRoll "y" (PSumR (PPair (PVar "x") (PVar "y"))), TApp (TVar "foo") (TRoll "y" (TSumR (TVar "y"))) ), ( PRoll "y" (PSumL PUnit), TRoll "y" (TSumL TUnit) )])] == [-1]
[ ( PRoll "z" (PSumR (PPair (PVar "x") (PRoll "z" (PSumR (PPair (PVar "y") (PVar "z")))))), TApp (TVar "foo") (TRoll "z" (TSumR (TVar "z"))) ), ( PRoll "y" (PSumL PUnit), TRoll "y" (TSumL TUnit) )]


state = Map.fromList [("foo", VFunDef [ ( PRoll "xs" (PSumR (PPair (PVar "x") (PVar "xs"))), TApp (TVar "foo") (TVar "xs") ), ( PRoll "ys" (PSumL PUnit), TRoll "ys" (TSumL TUnit) )])]

{-
Idea of function in Haskell Syntax:
data T = A T | B T | C Int | D Bool
g (A t) = g (B t)
g (B t) = g t
g (C n) = g (D (isEven n))
g (D b) = b

At the moment, there are a couple of possible matrices we could give this, one being:
< 0
? -1
< 0

and one being:
<
-1
<

Depending on whether we want to have the measure on the disjunct as a seperate measure or whether we want to
combine these columns like we have in this second matrix.

We ought to show that these combinations are always possible, e.g. if we have something like:
data t = A Nat | B Nat
f (A 0)     = 0
f (A (S n)) = f (B n)
f (B n)     = S (f(A n))

Which will either give the matrix
? -1
< 0

Or:

-1
<

i.e. we check the box difference first, and then the ordering on the disjuncts. So this doesn't give a counterexample.

-}

[ ( PRoll (PSumR (PPair (PVar "x") (PVar "z"))), TApp (TVar "foo") (TVar "z") ), ( PRoll (PSumL PUnit), TRoll (TSumL TUnit) )]

{-
foo (x:y:xs) = foo xs
foo [] = []

Ought to give matrix:
[[-2]]
-}
[(PRoll (PSumR (PPair (PVar "x") (PRoll (PSumR (PPair (PVar "y") (PVar "xs")))))),TApp (TVar "foo") (TVar "xs")),( PRoll (PSumL PUnit), TRoll (TSumL TUnit) )]

{-
data BTree = B BTree BTree | L

g (B l r) = (g l)
g (B l r) = (g r)
g L = 1

(Think of above defn. as being non-deterministic)

Note: the function,

g (B l r) = (g l) + (g r)
g L = 1

is a bit difficult to write in this languge because it would use a TApp with an outside function, which would give [[?, ?]].

To be correct about things, we need to provide a proof that + terminates.

I might add a construct called TAppStops which applies a function and assumes it terminates for writing definitions like this,
but for now I'm going to get as much mileage out of the current language constructs as possible.

Ought to give matrix [[-1, -1]]
-}
[(PRoll (PSumL (PPair (PVar "l") (PVar "r"))), TApp (TVar "g") (TVar "l")), (PRoll (PSumL (PPair (PVar "l") (PVar "r"))), TApp (TVar "g") (TVar "r")), (PRoll (PSumR PUnit), TRoll (TSumR TUnit))]

{-
A different comprotmise for this function is:


g (B l r) = B (g l) (g r)
g L = 1

which ought to also give the matrix:

[[-1, -1]]
-}

[(PRoll (PSumL (PPair (PVar "l") (PVar "r"))), TRoll ( TSumL ( TPair (TApp (TVar "g") (TVar "l")) (TApp (TVar "g") (TVar "r"))))), (PRoll (PSumL (PPair (PVar "l") (PVar "r"))), TApp (TVar "g") (TVar "r")), (PRoll (PSumR PUnit), TRoll (TSumR TUnit))]

{-
f (x:y:xs) ys = f xs (0:ys)
f xs (x:y:ys) = f (0:xs) ys

Should give a matrix of [[-2, 1], [1, -2]], which should terminate
-}
[(PPair (PRoll (PSumR (PPair (PVar "x") (PRoll (PSumR (PPair (PVar "y") (PVar "xs"))))))) (PVar "ys"), TApp (TVar "f") (TPair (TVar "xs") (TRoll (TSumR (TPair (TNatLit 0) (TVar "ys")))))), (PPair (PVar "xs") (PRoll (PSumR (PPair (PVar "x") (PRoll (PSumR (PPair (PVar "y") (PVar "ys"))))))), TApp (TVar "f") (TPair (TRoll (TSumR (TPair (TNatLit 0) (TVar "xs")))) (TVar "ys")))]

{-
f (x:xs) y (z:z':zs) v w = f xs y zs (0:0:0:0:v) (0:w)
f x (y:ys) (z:zs) v w = f (listAdd x x) ys zs (0:v) (0:w)
f x y z (v:v':v'':vs) w = f x (listAdd y y) (0:z) vs (0:w)
f _ _ _ _ w = w

Ought to give matrix
[[-1, ?, 0], [0, -1, ?], [-2, -1, 1], [4, 1, -3], [1, 1, 1]]

Which should terminate
-}

{-
A | B

1 | a:as
f (A [])     = []
f (A (n:ns)) = f (B ns)
f (B n)      = f(A n)

Should terminate with the matrix

[[-1, 0], [0, 1], [0, -1]]
-}

[(PSumL (PRoll (PSumR (PPair (PVar "n") (PVar "ns")))), TApp (TVar "f") (TSumR (TVar "ns"))), (PSumR (PVar "n"), TApp (TVar "f") (TSumL (TVar "n")))]

-}