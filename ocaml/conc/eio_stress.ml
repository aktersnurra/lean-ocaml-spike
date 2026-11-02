(* Eio fiber test (separate from the domain test): many fibers in one domain interleave
   calls to Leancore.call (yielding between calls), then the same work across an Eio
   domain pool via Domain_manager. Checks every response against the native oracle. *)

let leb i =
  let b = Buffer.create 4 in
  let rec go n = if n < 128 then Buffer.add_char b (Char.chr n) else (Buffer.add_char b (Char.chr (n land 127 lor 128)); go (n lsr 7)) in
  go i; Buffer.contents b

let request f i =
  let n = 1 + (f + i) mod 17 in
  let b = Buffer.create 64 in
  Buffer.add_string b ("\x02" ^ leb f ^ leb ((f * 7 + i) mod 105) ^ leb n);
  for j = 0 to n - 1 do
    Buffer.add_string b (leb (if (i + j) mod 41 = 0 then 0 else j)); Buffer.add_string b (leb ((i + j) mod 9)); Buffer.add_string b (leb (i * 31 + j))
  done;
  Buffer.contents b

let run_fiber f per bad =
  for i = 0 to per - 1 do
    let req = Bytes.of_string (request f i) in
    (match Leancore.call req with
     | r -> if not (Bytes.equal r (Native_core.handle req)) then Atomic.incr bad
     | exception _ -> Atomic.incr bad);
    Eio.Fiber.yield ()
  done

let () =
  Eio_main.run @@ fun env ->
  let bad = Atomic.make 0 in
  let fibers = 1000 and per = 100 in
  let t0 = Unix.gettimeofday () in
  Eio.Fiber.all (List.init fibers (fun f () -> run_fiber f per bad));
  Printf.printf "eio fibers (1 domain): fibers=%d calls=%d wrong=%d time=%.2fs\n" fibers (fibers * per) (Atomic.get bad) (Unix.gettimeofday () -. t0);
  let dm = Eio.Stdenv.domain_mgr env in
  let t0 = Unix.gettimeofday () in
  Eio.Fiber.all (List.init 4 (fun d () ->
    Eio.Domain_manager.run dm (fun () ->
      Eio.Fiber.all (List.init 100 (fun f () -> run_fiber (10_000 + d * 100 + f) 250 bad)))));
  Printf.printf "eio fibers (4 domains x 100 fibers): calls=%d wrong-so-far=%d time=%.2fs\n" (4 * 100 * 250) (Atomic.get bad) (Unix.gettimeofday () -. t0);
  if Atomic.get bad > 0 then (print_endline "== eio stress FAILED =="; exit 1) else print_endline "== eio stress PASSED =="
