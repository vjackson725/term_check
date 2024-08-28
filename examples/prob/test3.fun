
test3 (Roll (Right (Roll (Right x))), y) = pchoice 0.5 then test4 (x, y) else ()
test3 (x, Roll (Right y)) = test4 (double x, y)
