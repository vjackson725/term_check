
test4 (Roll (Right (Roll (Right x))), y) = pchoice 0.5 then test4 (x, y) else ()
test4 (x, Roll (Right y)) = test4 (x, y)
