-- Rewrite a monoid to associate right

normalise (Roll (Left ())) = Roll (Left ())
normalise (Roll (Right (Roll (Left ()), b))) = Roll (Right (Roll (Left ()), normalise b))
normalise (Roll (Right (Roll (Right (a0, a1)), b))) = normalise (Roll (Right (a0, Roll (Right (a1, b)))))