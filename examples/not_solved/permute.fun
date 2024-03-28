--
-- Permutation of arguments
-- The size-change method can solve this class of problems, whereas our method
-- cannot.
--

f (Roll (Right x), y) = f (y, x)
f (x, Roll (Right y)) = f (x, y)
f (Roll (Left ()), Roll (Left ())) = ()