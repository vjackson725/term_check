
rdecr (Roll (Left ())) = ()
rdecr (Roll (Right x)) = pchoice 0.5 then rdecr (Roll (Right x)) else rdecr x