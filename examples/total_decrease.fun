--
-- Example where the total structural size decreases, but one argument is
-- decreasing, and the other increasing.
--
-- Nat
-- Suc x = Roll (Right x)
-- Zero = Roll (Left ())

-- f (SSx, y) = f (x, Sy)
-- f (x, SSy) = f (Sx, y)
-- f (x, y) = ()

f (Roll (Right (Roll (Right n))), m) = f (n, Roll (Right m))
f (n, Roll (Right (Roll (Right m)))) = f (Roll (Right n), m)
f (n, m) = ()

--
-- Same idea, but with more layers
--
-- g (SSSx, y) = g (x, SSy)
-- g (x, SSSy) = g (SSx, y)
-- g (x, y) = ()

g (Roll (Right (Roll (Right (Roll (Right  x)), y)))) = g (x, Roll (Right (Roll (Right  y))))
g (x, Roll (Right (Roll (Right (Roll (Right  y)))))) = g (Roll (Right (Roll (Right  x), y)))
g (x, y) = ()
