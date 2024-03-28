--
-- Rewrite a monoid to associate right, with variations
--

normalise (Roll (Left ())) = Roll (Left ())
normalise (Roll (Right (Roll (Left ()), b))) = Roll (Right (Roll (Left ()), normalise b))
normalise (Roll (Right (Roll (Right (a0, a1)), b))) = normalise (Roll (Right (a0, Roll (Right (a1, b)))))

normalise2 (Roll (Left ())) = Roll (Left ())
normalise2 (Roll (Right ( Roll (Left ()), b ))) = Roll (Right ( Roll (Left ()), normalise2 b ))
normalise2 (Roll (Right ( Roll (Right (a0, a1)), b ))) = normalise2 (Roll (Right ( a0, normalise2 (Roll (Right (a1, b))) )))

normalise3 (Left (Roll (Left ()))) = Roll (Left ())
normalise3 (Left (Roll (Right (a, b)))) = normalise3 (Right (normalise3 (Left a), b))
normalise3 (Right (Roll (Left ())       , b)) = Roll (Left ())
normalise3 (Right (Roll (Right (a0, a1)), b)) = Roll (Right (a0, normalise3 (Right (a1, b))))
