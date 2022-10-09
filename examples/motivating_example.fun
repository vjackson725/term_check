f (Roll (Right ((), Roll (Right ((), n)))), m) = f (n, Roll (Right ((), m)))
f (n, Roll (Right ((), Roll (Right ((), m))))) = f (Roll (Right ((), n)), m)
f (n, m) = ()