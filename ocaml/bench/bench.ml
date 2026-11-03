(* Gate 3 benchmark: extracted Lean core (Leancore.call, bytes -> bytes, including the
   bytes <-> Z.t list conversion) vs the hand-written native OCaml implementation
   (Native_core.handle, same wire spec, Zarith amounts, Hashtbl duplicate check).
   Reports ns per call (best of 5 runs) and the ratio. Target: ratio <= 10. *)

let leb i =
  let b = Buffer.create 4 in
  let rec go n = if n < 128 then Buffer.add_char b (Char.chr n) else (Buffer.add_char b (Char.chr (n land 127 lor 128)); go (n lsr 7)) in
  go i; Buffer.contents b

let order n =
  let b = Buffer.create (n * 8) in
  Buffer.add_string b ("\x02" ^ leb 4242 ^ leb 15 ^ leb n);
  for j = 0 to n - 1 do Buffer.add_string b (leb (1000 + j)); Buffer.add_string b (leb (1 + j mod 9)); Buffer.add_string b (leb (199 + 37 * j)) done;
  Bytes.of_string (Buffer.contents b)

let time_per_call f req iters =
  let best = ref infinity in
  for _ = 1 to 5 do
    let t0 = Unix.gettimeofday () in
    for _ = 1 to iters do ignore (Sys.opaque_identity (f req)) done;
    let dt = (Unix.gettimeofday () -. t0) /. float iters in
    if dt < !best then best := dt
  done;
  !best *. 1e9

let () =
  let cases = [
    ("gate1 n=123456", Bytes.of_string ("\x01" ^ leb 123456), 1_000_000);
    ("order 1 line", order 1, 500_000);
    ("order 10 lines", order 10, 100_000);
    ("order 100 lines", order 100, 10_000);
    ("order 1000 lines", order 1000, 1_000);
    ("order 10000 lines", order 10000, 100);
    ("malformed (truncated order)", Bytes.of_string "\x02\x01\x05\x03\x07", 1_000_000);
  ] in
  Printf.printf "OCaml %s\n%-30s %12s %12s %8s\n" Sys.ocaml_version "case" "lean ns" "native ns" "ratio";
  let worst = ref 0. in
  List.iter (fun (name, req, iters) ->
    assert (Bytes.equal (Leancore.call req) (Native_core.handle req));
    let l = time_per_call Leancore.call req iters and n = time_per_call Native_core.handle req iters in
    let r = l /. n in
    if r > !worst then worst := r;
    Printf.printf "%-30s %12.0f %12.0f %8.2f\n%!" name l n r) cases;
  Printf.printf "worst ratio %.2f (target <= 10): %s\n" !worst (if !worst <= 10. then "PASS" else "FAIL");
  (* Wire format v2 (generated codecs, Codec typeclass in Lean): same orders, same work. *)
  let v2_order n : Spike_api.order =
    { customer = Z.of_int 4242; discount_pct = Z.of_int 15;
      lines = List.init n (fun j -> ({ sku = Z.of_int (1000 + j); qty = Z.of_int (1 + j mod 9); unit_price = Z.of_int (199 + 37 * j) } : Spike_api.line)) } in
  Printf.printf "\nwire v2 (generated): raw bytes and typed call vs v1 (all Lean)\n%-30s %12s %12s %12s %8s\n" "case" "v1 ns" "v2 raw ns" "v2 typed ns" "v2/v1";
  List.iter (fun (name, n, iters) ->
    let v1req = order n in
    let o = v2_order n in
    let v2req = Spike_api.encode_request (Spike_api.PriceOrder o) in
    let v1 = time_per_call Leancore.call v1req iters in
    let v2 = time_per_call Leancore.call_api v2req iters in
    let typed = time_per_call (fun o -> Spike_api.call (Spike_api.PriceOrder o)) o iters in
    Printf.printf "%-30s %12.0f %12.0f %12.0f %8.2f\n%!" name v1 v2 typed (v2 /. v1))
    [ ("order 1 line", 1, 500_000); ("order 10 lines", 10, 100_000); ("order 100 lines", 100, 10_000); ("order 1000 lines", 1000, 1_000) ]
