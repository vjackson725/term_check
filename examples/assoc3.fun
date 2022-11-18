-- Rewrite a semigroup to associate right

normalise (Left (Roll (Left ()))) = Roll (Left ())
normalise (Left (Roll (Right (a, b)))) = normalise (Right (normalise (Left a), b))
normalise (Right (Roll (Left ())       , b)) = Roll (Left ())
normalise (Right (Roll (Right (a0, a1)), b)) = Roll (Right (a0, normalise (Right (a1, b))))
