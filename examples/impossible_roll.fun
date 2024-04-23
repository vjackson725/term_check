--
-- An example to generate that our 'Roll' is not the standard roll, because
-- there are no types enforcing that Roll cannot have non-Roll terms in it.
--
-- We show this terminates, because it does under the assumption that all terms
-- are finite. In a typed setting, this would not typecheck.
--

f (Roll x) = f x