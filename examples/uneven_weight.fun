--
-- An example where the solution does not have equal linear weights
-- The expected weights are [6,9,5]
--

-- Nat
-- Suc x = Roll (Right x)
-- Zero = Roll (Left ())
--
--   f (Sx,   y,    z) = f ( x, Sy,  z)
--   f ( x,   y, SSSz) = f (Sx, Sy,  z)
--   f ( x, SSy,    z) = f ( x,  y, Sz)
-- or, as a matrix,
--   [ -1  1  0 ]
--   [  1  1 -3 ]
--   [  0 -2  1 ].

f (Roll x, y, z) = f (x, Roll y, z)
f (x, y, Roll (Roll (Roll z))) = f (Roll x, Roll y, z)
f (x, Roll (Roll y), z) = f (x, y, Roll z)