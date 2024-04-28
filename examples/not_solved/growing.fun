--
-- An example that does not terminate.
--
-- If you don't fail when the linear program returns all zeros,
-- this will pass the termination checker!
--

f x = f (Roll x)