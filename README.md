== Linear-Lexicographic Termination Checking For Functional Programs ==

This repository implements a linear--lexicographic termination checking algorithm for functional programs.

-- Building --

To build this code, run
```
cabal build
```

This code is known to build correctly with ghc 9..6.2 and cabal 3.6.2.0.

-- Running --

To run this code, run
```
cabal run term-check -- <command> <file to termination check>
```

There are two commands of interest: `makematrix` which generates the primitive measures and prints the termination matrix, and `solve` (or the alias `programcheck`) which attempts to solve the matrix.

-- Examples --

The expected output for `ackermann.fun` is
```
> cabal run term-check -- makematrix examples/ackermann.fun 
== Fun: ack ==
m0: ([MPairL],[MRoll,MSumR,MPairR])
m1: ([MPairR],[MRoll,MSumR,MPairR])
m2: ([MPairR,MRoll,MRLtL],[])
[[-1.0, 0.0, -1.0], [ω, -1.0, 1.0], [ω, ω, -1.0]]

> cabal run term-check -- solve examples/ackermann.fun 
fromList [("ack",Just [[(1.0,"m0")],[(1.0,"m1")]])]
```

The expected output for `sparse_list.fun` is
```
> cabal run term-check -- makematrix examples/sparse_list.fun 
== Fun: toList ==
m0: ([MRoll,MSumR,MPairR,MPairL],[MRoll,MSumR])
m1: ([],[MRoll,MSumR,MPairR,MPairR])
[[-1.0, ω], [0.0, -1.0]]

> cabal run term-check -- solve examples/sparse_list.fun 
fromList [("toList",Just [[(1.0,"m1")],[(1.0,"m0")]])]
```
