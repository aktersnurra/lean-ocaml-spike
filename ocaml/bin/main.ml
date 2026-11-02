(* Gate 1b harness: an ordinary Dune executable calling the extracted core via Leancore. *)
let () = print_endline (Z.to_string (Leancore.gate1 (Z.of_string Sys.argv.(1))))
