(* OCaml 5 domain-concurrency stress test: many domains call Leancore.call in parallel on
   distinct requests and check every response against the native oracle (computed in the
   same domain). Shared state in the extracted code or runtime axioms would show up as
   wrong answers, exceptions or crashes. *)

let leb i =
  let b = Buffer.create 4 in
  let rec go n = if n < 128 then Buffer.add_char b (Char.chr n) else (Buffer.add_char b (Char.chr (n land 127 lor 128)); go (n lsr 7)) in
  go i; Buffer.contents b

(* Deterministic request i: mix of valid orders, domain errors and malformed input. *)
let request seed i =
  let st = Random.State.make [| seed; i |] in
  match Random.State.int st 4 with
  | 0 -> "\x01" ^ leb (Random.State.int st 1_000_000_000)
  | 3 -> String.init (Random.State.int st 20) (fun _ -> Char.chr (Random.State.int st 256))
  | _ ->
    let n = 1 + Random.State.int st 30 in
    let b = Buffer.create 64 in
    Buffer.add_string b ("\x02" ^ leb i ^ leb (Random.State.int st 110) ^ leb n);
    for j = 0 to n - 1 do
      Buffer.add_string b (leb (if Random.State.int st 50 = 0 then 0 else j));
      Buffer.add_string b (leb (Random.State.int st 20));
      Buffer.add_string b (leb (Random.State.int st 1_000_000))
    done;
    Buffer.contents b

let () =
  let domains = try int_of_string Sys.argv.(1) with _ -> 8 in
  let per = try int_of_string Sys.argv.(2) with _ -> 50_000 in
  let t0 = Unix.gettimeofday () in
  let work d () =
    let bad = ref 0 and exn = ref 0 in
    for i = 0 to per - 1 do
      let req = Bytes.of_string (request d i) in
      match Leancore.call req with
      | r -> if not (Bytes.equal r (Native_core.handle req)) then incr bad
      | exception _ -> incr exn
    done;
    (!bad, !exn)
  in
  let ds = List.init domains (fun d -> Domain.spawn (work d)) in
  let results = List.map Domain.join ds in
  let bad = List.fold_left (fun a (b, _) -> a + b) 0 results and exn = List.fold_left (fun a (_, e) -> a + e) 0 results in
  Printf.printf "domains=%d calls=%d wrong=%d exceptions=%d time=%.2fs (recommended_domain_count=%d)\n"
    domains (domains * per) bad exn (Unix.gettimeofday () -. t0) (Domain.recommended_domain_count ());
  if bad + exn > 0 then (print_endline "== domain stress FAILED =="; exit 1) else print_endline "== domain stress PASSED =="
