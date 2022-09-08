f (Box (Left ())) = ()
f (Box (Right n)) = f n

g () = ()