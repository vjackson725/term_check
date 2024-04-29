--
-- An example that does not terminate, but which the lexicographic algorithm
-- might claim terminates if implemented incorrectly.
--
-- The matrix is
--   [ -1 ]
--   [  0 ]
-- and if you 'eliminate the column', you might expect this would result in
-- the empty matrix and succeed. But it should not! Instead, if you implement
-- it correctly, it will result in
--   [[]]
-- which is not the empty matrix.
--

f (Roll x) = f x
f x = f x