--
-- The ackermann function
--
-- An example of a purely lexicographic argument
--
-- Nat
-- Zero = Roll (Left ())
-- Suc n = Roll (Right n)
--

ack (Roll (Left ()), n) = Roll (Right n)
ack (Roll (Right m), Roll (Left ())) = ack (m, Roll (Right (Roll (Left ()))))
ack (Roll (Right m), Roll (Right n)) = ack (m, ack (Roll (Right m), n))