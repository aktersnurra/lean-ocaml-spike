(* Left-deep chain Add(Add(...Add(Lit 0, Lit 0)..., Lit 0), Lit 0) of depth n.
   Request tags (generated layout): EvalFormula = 3, EchoFormula = 4; Formula: Lit = 0, Add = 2. *)
let deep_formula n = String.make n '\x02' ^ "\x00\x00" ^ String.concat "" (List.init n (fun _ -> "\x00\x00"))
let probe name req =
  let t0 = Unix.gettimeofday () in
  let r = match Leancore.call_api (Bytes.of_string req) with
    | b -> (match Spike_api.decode_reply b with
        | Ok (Ok (Spike_api.Value v)) -> "value " ^ Z.to_string v
        | Ok (Ok (Spike_api.Formula _)) -> "formula (echoed)"
        | Ok (Error (Spike_api.Transport _)) -> "transport error"
        | Ok _ -> "other" | Error c -> Printf.sprintf "undecodable (%d)" c
        | exception Stack_overflow -> "client decoder: Stack_overflow")
    | exception Stack_overflow -> "core: Stack_overflow"
    | exception e -> "core: " ^ Printexc.to_string e in
  Printf.printf "%-42s %-28s %.2fs\n%!" name r (Unix.gettimeofday () -. t0)
let () =
  Printf.printf "OCaml %s\n" Sys.ocaml_version;
  List.iter (fun n ->
    probe (Printf.sprintf "eval, depth %d" n) ("\x03" ^ deep_formula n ^ "\x05");
    probe (Printf.sprintf "echo, depth %d" n) ("\x04" ^ deep_formula n);
    probe (Printf.sprintf "truncated, depth %d" n) ("\x03" ^ String.make n '\x02'))
    (match Sys.getenv_opt "DEPTHS" with Some s -> List.map int_of_string (String.split_on_char ',' s) | None -> [ 1_000; 10_000; 100_000; 1_000_000 ])
