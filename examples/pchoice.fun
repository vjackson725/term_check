
eventually0 () = pchoice 0.5 then eventually0 () else 0

rdecr (Roll (Left ())) = ()
rdecr (Roll (Right x)) = pchoice 0.5 then rdecr (Roll (Right x)) else rdecr x