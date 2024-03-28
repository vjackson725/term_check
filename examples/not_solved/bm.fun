--
-- Distributing If statements
--
-- Ast
-- Atom a = Roll (Left a)
-- If x y z = Roll (Right (x, y, z))

norm (Roll (Left n)) = Roll (Left n)
norm (Roll (Right (Roll (Left a), y, z))) = Roll (Right (Roll (Left a), norm y, norm z))
norm (Roll (Right (Roll (Right (u, v, w)), y, z))) = norm (Roll (Right (u, Roll (Right (v, y, z)), Roll (Right (w, y, z)))))