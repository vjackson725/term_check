--
-- ex3 from the paper
--

ex3 (            x,               y,   Roll (Left z)) = ex3 (x,   y,   z)
ex3 (            x,   Roll (Left y), Roll (Right ())) = ex3 (x,   y, h y)
ex3 (Roll (Left x), Roll (Right ()), Roll (Right ())) = ex3 (x, h x, h x)
