-- Example from 
--  Hyvernat Pierre - The Size-Change Termination Principle for Constructor Based Languages.
--  lmcs:1003 - Logical Methods in Computer Science, February 13, 2014, Volume 10, Issue 1.
--  https://doi.org/10.2168/LMCS-10(1:11)2014
-- size change fails for this example.
--
-- Our method also fails for this example.
--
-- The function rearranges a binary tree so that all right nodes are leaves,
-- essentially making it a list.
--
-- Tree
-- Leaf = Roll (Left ())
-- Branch x y = Roll (Right (x, y))
--
listify (Roll (Left ())) = (Roll (Left ()))
listify (Roll (Right (x, Roll (Left ())))) = Roll (Right (listify x, Roll (Left ())))
listify (Roll (Right (x, Roll (Right (y, z))))) = listify (Roll (Right (Roll (Right (x, y)), z)))