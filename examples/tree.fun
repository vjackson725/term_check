-- Leaf = Roll (Left ())
-- Branch x y = Roll (Right (x, y))
--
f (Roll (Left ())) = ()
f (Roll (Right ((Left ()), z))) = ()
f (Roll (Right (Roll (Right (x, y)), z))) = f (Roll (Right (x, Roll (Right (x, y)))))