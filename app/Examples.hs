import PatternLambda

-- Ought to give matrix [[-1]]
f (x:xs) = f xs
f [] = ()

data BTree = B BTree BTree | L

g (B l r) = (g l) + (g r)
g L = 1

-- Ought to have matrix [[-1, -1]]

[ ( PBox (PSumR (PPair (PVar 'x') (PVar 'y'))), TBox (TSumR (TVar 'y')) ), ( PBox (PSumL PUnit), TBox (TSumL TUnit) )]

tlet 'f' [ ( PBox 'y' (PSumR (PPair (PVar 'x') (PVar 'y'))), TApp 'f' (TBox 'y' (TSumR (TVar 'y'))) ), ( PBox 'y' (PSumL PUnit), TBox 'y' (TSumL TUnit) )]

[ ( PBox 'y' (PSumR (PPair (PVar 'x') (PVar 'y'))), TBox 'y' (TSumR (TVar 'y')) ), ( PBox 'y' (PSumL PUnit), TBox 'y' (TSumL TUnit) )]

[ ( PBox (PSumR (PPair (PVar "x") (PBox (PSumR (PPair (PVar "y") (PVar "z")))))), TApp (TVar "foo") (TVar "z") ), ( PBox (PSumL PUnit), TBox (TSumL TUnit) )]
--state = Map.fromList [("foo", VFunDef [(PVar "x", TPair (TVar "x") (TVar "x"))])]

state = Map.fromList [("foo", VFunDef [ ( PBox "y" (PSumR (PPair (PVar "x") (PVar "y"))), TApp (TVar "foo") (TBox "y" (TSumR (TVar "y"))) ), ( PBox "y" (PSumL PUnit), TBox "y" (TSumL TUnit) )])]


state = Map.fromList [("foo", VFunDef [(PVar "x", TApp (TVar "foo") TUnit)])]
-- Ought to give matrix [-1]
-- matrixify "foo" [("foo", VFunDef [ ( PBox "y" (PSumR (PPair (PVar "x") (PVar "y"))), TApp (TVar "foo") (TBox "y" (TSumR (TVar "y"))) ), ( PBox "y" (PSumL PUnit), TBox "y" (TSumL TUnit) )])] == [-1] 
[ ( PBox "z" (PSumR (PPair (PVar "x") (PBox "z" (PSumR (PPair (PVar "y") (PVar "z")))))), TApp (TVar "foo") (TBox "z" (TSumR (TVar "z"))) ), ( PBox "y" (PSumL PUnit), TBox "y" (TSumL TUnit) )]


state = Map.fromList [("foo", VFunDef [ ( PBox "xs" (PSumR (PPair (PVar "x") (PVar "xs"))), TApp (TVar "foo") (TVar "xs") ), ( PBox "ys" (PSumL PUnit), TBox "ys" (TSumL TUnit) )])]

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

[ ( PBox (PSumR (PPair (PVar "x") (PVar "z"))), TApp (TVar "foo") (TVar "z") ), ( PBox (PSumL PUnit), TBox (TSumL TUnit) )]

{-
foo (x:y:xs) = foo xs
foo [] = []

Ought to give matrix:
[[-2]]
-}
[(PBox (PSumR (PPair (PVar "x") (PBox (PSumR (PPair (PVar "y") (PVar "xs")))))),TApp (TVar "foo") (TVar "xs")),( PBox (PSumL PUnit), TBox (TSumL TUnit) )]

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
[(PBox (PSumL (PPair (PVar "l") (PVar "r"))), TApp (TVar "g") (TVar "l")), (PBox (PSumL (PPair (PVar "l") (PVar "r"))), TApp (TVar "g") (TVar "r")), (PBox (PSumR PUnit), TBox (TSumR TUnit))]
