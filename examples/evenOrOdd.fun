-- Nat
-- Zero = Roll (Left ())
-- Suc x = Roll (Right x)
--
-- False = Left ()
-- True = Right ()
--
-- odd n = evenOrOdd (Left n)
-- even n = evenOrOdd (Right n)
--
evenOrOdd (Left  (Roll (Left ()))) = Left ()
evenOrOdd (Right (Roll (Left ()))) = Right ()
evenOrOdd (Left  (Roll (Right n))) = evenOrOdd (Right n)
evenOrOdd (Right (Roll (Right n))) = evenOrOdd (Left n)