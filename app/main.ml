(* Gate 1 harness: call the extracted function with a Nat read from argv.
   Nat is Z.t (zarith) on the OCaml side; the signature comes from the
   generated gate1.mli ("val main: Z.t -> Z.t"). *)
let () = print_endline (Z.to_string (Gate1.main (Z.of_string Sys.argv.(1))))
