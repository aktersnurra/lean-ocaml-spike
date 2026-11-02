(* Gate 3 robustness tests for the extracted core, driven only through Leancore.call.
   Native_core (a hand-written implementation of the same spec) is the differential oracle.
   Test-side helpers (LEB128 encoder, order builder, response reader) are reference code. *)

let failures = ref 0
let fail fmt = Printf.ksprintf (fun s -> incr failures; print_endline ("FAIL " ^ s)) fmt
let hex s = String.concat " " (List.map (fun c -> Printf.sprintf "%02x" (Char.code c)) (List.of_seq (String.to_seq s)))
let short s = if String.length s > 40 then hex (String.sub s 0 40) ^ " ..." else hex s

let leb (n : Z.t) : string =
  let b = Buffer.create 8 in
  let rec go n =
    let lo = Z.to_int (Z.logand n (Z.of_int 127)) and hi = Z.shift_right n 7 in
    if Z.equal hi Z.zero then Buffer.add_char b (Char.chr lo)
    else (Buffer.add_char b (Char.chr (lo lor 128)); go hi)
  in
  go n; Buffer.contents b
let lebi i = leb (Z.of_int i)

(* Buffer-based (the stdlib List.map in OCaml 4.14 is not tail recursive and overflows the
   test's own stack on million-line orders). *)
let order ?(customer = 1) ~pct lines =
  let b = Buffer.create 64 in
  Buffer.add_string b ("\x02" ^ lebi customer ^ lebi pct ^ lebi (List.length lines));
  List.iter (fun (s, q, p) -> Buffer.add_string b (leb s); Buffer.add_string b (leb q); Buffer.add_string b (leb p)) lines;
  Buffer.contents b

(* Read a varint from s at position i; returns value and next position. *)
let read_leb s i =
  let rec go i shift acc =
    let b = Char.code s.[i] in
    let acc = Z.add acc (Z.shift_left (Z.of_int (b land 127)) shift) in
    if b < 128 then (acc, i + 1) else go (i + 1) (shift + 7) acc
  in
  go i 0 Z.zero

let quote_of s =
  if String.length s < 1 || s.[0] <> '\x00' then None
  else
    let a, i = read_leb s 1 in let b, i = read_leb s i in
    let c, i = read_leb s i in let d, i = read_leb s i in
    if i <> String.length s then None else Some (a, b, c, d)

let call s = Bytes.to_string (Leancore.call (Bytes.of_string s))
let native s = Bytes.to_string (Native_core.handle (Bytes.of_string s))

let check name req want =
  let got = call req and nat = native req in
  if got <> want then fail "%s: %s -> %s, want %s" name (short req) (hex got) (hex want)
  else if nat <> got then fail "%s: native disagrees: %s vs %s" name (hex nat) (hex got)
  else Printf.printf "ok   %s\n" name

let z = Z.of_int
let err c = Printf.sprintf "\x01%c" (Char.chr c)

let () =
  (* --- 1. one case per boundary constructor (every op, every response form) --- *)
  print_endline "-- constructors";
  check "op gate1 -> ok" ("\x01" ^ lebi 21) ("\x00" ^ lebi 43);
  check "op priceOrder -> ok quote" (order ~pct:10 [ (z 7, z 2, z 150); (z 8, z 1, z 100) ])
    ("\x00" ^ lebi 400 ^ lebi 40 ^ lebi 360 ^ lebi 2);
  check "error 1 empty" "" (err 1);
  check "error 3 unknownOp" "\x09" (err 3);
  check "error 4 truncated (order)" "\x02\x01" (err 4);
  check "error 5 trailing (order)" (order ~pct:0 [ (z 1, z 1, z 1) ] ^ "\x00") (err 5);
  check "error 16 noLines" (order ~pct:0 []) (err 16);
  check "error 17 zeroQty" (order ~pct:0 [ (z 1, z 0, z 5) ]) (err 17);
  check "error 18 badDiscount" (order ~pct:101 [ (z 1, z 1, z 5) ]) (err 18);
  check "error 19 duplicateSku" (order ~pct:0 [ (z 1, z 1, z 5); (z 2, z 1, z 5); (z 1, z 3, z 5) ]) (err 19);
  check "validation order: noLines beats badDiscount" (order ~pct:200 []) (err 16);
  check "validation order: badDiscount beats zeroQty" (order ~pct:200 [ (z 1, z 0, z 1) ]) (err 18);
  check "100% discount" (order ~pct:100 [ (z 1, z 3, z 7) ]) ("\x00" ^ lebi 21 ^ lebi 21 ^ lebi 0 ^ lebi 1);
  let big = Z.shift_left Z.one 200 in
  check "bignum amounts (2^200 * 3)" (order ~pct:50 [ (z 1, z 3, big) ])
    ("\x00" ^ leb (Z.mul big (z 3)) ^ leb (Z.div (Z.mul (Z.mul big (z 3)) (z 50)) (z 100))
     ^ leb (Z.sub (Z.mul big (z 3)) (Z.div (Z.mul (Z.mul big (z 3)) (z 50)) (z 100))) ^ lebi 1);

  (* --- 2. random valid orders: domain invariants + agreement with native --- *)
  print_endline "-- random valid orders";
  Random.init 7;
  let rnd_z () = if Random.int 10 = 0 then Z.shift_left (z (Random.bits ())) (Random.int 100) else z (Random.int 100_000) in
  let n_valid = 20_000 and bad = ref 0 in
  for _ = 1 to n_valid do
    let k = 1 + Random.int 12 in
    let lines = List.init k (fun i -> (z (i * 7 + Random.int 7), Z.succ (z (Random.int 50)), rnd_z ())) in
    let pct = Random.int 101 in
    let req = order ~customer:(Random.int 1_000_000) ~pct lines in
    let got = call req in
    (match quote_of got with
     | None -> incr bad; if !bad < 5 then fail "valid order rejected: %s -> %s" (short req) (hex got)
     | Some (sub, disc, total, cnt) ->
       let exp_sub = List.fold_left (fun a (_, q, p) -> Z.add a (Z.mul q p)) Z.zero lines in
       if not (Z.equal sub exp_sub && Z.leq disc sub && Z.equal (Z.add total disc) sub
               && Z.equal disc (Z.div (Z.mul sub (z pct)) (z 100)) && Z.equal cnt (z k)) then
         (incr bad; if !bad < 5 then fail "quote invariant broken for %s" (short req)));
    if native req <> got then (incr bad; if !bad < 5 then fail "native disagrees on valid order %s" (short req))
  done;
  Printf.printf "valid orders: %d, problems: %d\n" n_valid !bad;

  (* --- 3. differential fuzz: mutated valid requests and random bytes --- *)
  print_endline "-- differential fuzz (extracted vs native, byte for byte)";
  let mutate s =
    let b = Bytes.of_string s in
    let len = Bytes.length b in
    match Random.int 4 with
    | 0 when len > 0 -> Bytes.set b (Random.int len) (Char.chr (Random.int 256)); Bytes.to_string b
    | 1 when len > 1 -> Bytes.sub_string b 0 (Random.int len)
    | 2 -> s ^ String.make 1 (Char.chr (Random.int 256))
    | _ -> let i = Random.int (len + 1) in String.sub s 0 i ^ String.make 1 (Char.chr (Random.int 256)) ^ String.sub s i (len - i)
  in
  let n_fuzz = 200_000 and diffs = ref 0 and malformed = ref 0 and hist = Hashtbl.create 16 in
  for i = 1 to n_fuzz do
    let req =
      if i mod 3 = 0 then String.init (Random.int 32) (fun _ -> Char.chr (Random.int 256))
      else
        let lines = List.init (Random.int 5) (fun j -> (z (j + Random.int 3), z (Random.int 4), z (Random.int 1000))) in
        let r = ref (order ~pct:(Random.int 120) lines) in
        for _ = 1 to Random.int 3 do r := mutate !r done; !r
    in
    match call req with
    | exception e -> incr malformed; if !malformed < 5 then fail "exception on %s: %s" (short req) (Printexc.to_string e)
    | got ->
      let key = if String.length got >= 1 && got.[0] = '\x00' then "ok" else if String.length got = 2 then Printf.sprintf "err %d" (Char.code got.[1]) else "MALFORMED" in
      Hashtbl.replace hist key (1 + try Hashtbl.find hist key with Not_found -> 0);
      if key = "MALFORMED" then incr malformed;
      if native req <> got then (incr diffs; if !diffs < 5 then fail "diff on %s: lean %s native %s" (short req) (hex got) (hex (native req)))
  done;
  let keys = List.sort compare (Hashtbl.fold (fun k v a -> (k, v) :: a) hist []) in
  Printf.printf "fuzz: %d inputs, %d diffs, %d malformed/exceptions; responses: %s\n" n_fuzz !diffs !malformed
    (String.concat ", " (List.map (fun (k, v) -> Printf.sprintf "%s=%d" k v) keys));

  (* --- 4. adversarial inputs: must terminate quickly with an encoded error --- *)
  print_endline "-- adversarial";
  let timed name req want =
    let t0 = Unix.gettimeofday () in
    let r = try Ok (call req) with e -> Error (Printexc.to_string e) in
    let dt = Unix.gettimeofday () -. t0 in
    match r with
    | Ok got when want = "" || got = want -> Printf.printf "ok   %-45s %8.3f s  -> %s\n" name dt (short got)
    | Ok got -> fail "%s: got %s want %s" name (short got) (hex want)
    | Error e -> fail "%s: raised %s after %.3f s" name e dt
  in
  timed "claimed 2^60 lines, no line data" ("\x02\x01\x00" ^ leb (Z.shift_left Z.one 60)) (err 4);
  timed "claimed 2^60 lines, 1000 lines of data" ("\x02\x01\x00" ^ leb (Z.shift_left Z.one 60) ^ String.concat "" (List.init 1000 (fun i -> lebi i ^ "\x01\x01"))) (err 4);
  timed "10_000-byte varint (gate1)" ("\x01" ^ String.make 9_999 '\x80' ^ "\x01") "";
  timed "10_000-byte unterminated varint" ("\x01" ^ String.make 10_000 '\xff') (err 4);
  timed "10_000-line order" (order ~pct:5 (List.init 10_000 (fun i -> (z i, z 1, z 3)))) "";
  timed "100_000-line order" (order ~pct:5 (List.init 100_000 (fun i -> (z i, z 1, z 3)))) "";
  timed "1_000_000-byte unterminated varint" ("\x01" ^ String.make 1_000_000 '\xff') (err 4);
  timed "1_000_000-line order" (order ~pct:5 (List.init 1_000_000 (fun i -> (z i, z 1, z 3)))) "";
  timed "1_000_000-line order, duplicate at the end" (order ~pct:5 (List.init 1_000_000 (fun i -> (z (if i = 999_999 then 0 else i), z 1, z 3)))) (err 19);
  if !failures > 0 then (Printf.printf "%d FAILURES\n" !failures; exit 1) else print_endline "== Gate 3 tests PASSED =="
