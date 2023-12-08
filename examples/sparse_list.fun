-- Nat
-- Zero = Roll (Left ())
-- Suc x = Roll (Right x)
--
-- List
-- Nil = Roll (Left ())
-- Cons x xs = Roll (Right (x, xs))
--
-- SparseList
-- SNil = Roll (Left ())
-- SCons x n xs = Roll (Right (x, n, xs))
--
toList Roll (Left ()) = Roll (Left ())
toList (Roll (Right (x, Roll (Left ()), xs))) = toList xs
toList (Roll (Right (x, Roll (Right n), xs))) = Roll (Right (x, toList (Roll (Right (x, n, xs)))))