
nested () = pchoice 0.5 then (pchoice 0.5 then nested () else ()) else ()