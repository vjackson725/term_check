-- Leaf v = Roll (Left v)
-- Branch x y = Roll (Right (x, y))
--
rotateAllRight (Roll (Left v)) = Left v
rotateAllRight (Roll (Right ((Left v), z))) = Right (v, z)
rotateAllRight (Roll (Right (Roll (Right (x, y)), z))) = rotateAllRight (Roll (Right (x, Roll (Right (y, z)))))