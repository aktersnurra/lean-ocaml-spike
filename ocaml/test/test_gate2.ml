(* Gate 2 tests: drive the extracted Lean core only through Leancore.call (bytes -> bytes).
   The LEB128 encoder/decoder here is test-only reference code used to build requests and
   read responses; the boundary itself has no knowledge of the wire format. *)

let leb128 (n : Z.t) : string =
  let b = Buffer.create 8 in
  let rec go n =
    let lo = Z.to_int (Z.logand n (Z.of_int 127)) and hi = Z.shift_right n 7 in
    if Z.equal hi Z.zero then Buffer.add_char b (Char.chr lo)
    else (Buffer.add_char b (Char.chr (lo lor 128)); go hi)
  in
  go n; Buffer.contents b

let hex s = String.concat " " (List.map (fun c -> Printf.sprintf "%02x" (Char.code c)) (List.of_seq (String.to_seq s)))
let call s = Bytes.to_string (Leancore.call (Bytes.of_string s))
let failures = ref 0
let expect name req want =
  let got = call req in
  if got = want then Printf.printf "ok   %-28s %s -> %s\n" name (hex req) (hex got)
  else (incr failures; Printf.printf "FAIL %-28s %s -> %s, want %s\n" name (hex req) (hex got) (hex want))

let ok_gate1 n = "\x00" ^ leb128 (Z.add (Z.mul n (Z.of_int 2)) Z.one)
let err code = String.make 1 '\x01' ^ String.make 1 (Char.chr code)

let () =
  expect "gate1 0" ("\x01" ^ leb128 Z.zero) (ok_gate1 Z.zero);
  expect "gate1 5" ("\x01" ^ leb128 (Z.of_int 5)) (ok_gate1 (Z.of_int 5));
  expect "gate1 127 (1-byte edge)" ("\x01" ^ leb128 (Z.of_int 127)) (ok_gate1 (Z.of_int 127));
  expect "gate1 128 (2-byte edge)" ("\x01" ^ leb128 (Z.of_int 128)) (ok_gate1 (Z.of_int 128));
  let big = Z.shift_left Z.one 100 in
  expect "gate1 2^100" ("\x01" ^ leb128 big) (ok_gate1 big);
  expect "non-canonical varint 80 00" "\x01\x80\x00" (ok_gate1 Z.zero);
  expect "error empty" "" (err 1);
  expect "error unknown op" "\x07\x05" (err 3);
  expect "error op without payload" "\x01" (err 4);
  expect "error truncated varint" "\x01\x80" (err 4);
  expect "error trailing bytes" "\x01\x05\x00" (err 5);
  (* Fuzz through the boundary: random byte strings, biased towards op 0x01. Every
     response must be well formed: 00 + payload, or 01 + one code in 1..5 (2 = notBytes
     cannot arise from real bytes). No exceptions, every call returns. *)
  Random.init 42;
  let n = 100_000 and bad = ref 0 and oks = ref 0 in
  for _ = 1 to n do
    let len = Random.int 24 in
    let s = String.init len (fun i -> if i = 0 && Random.bool () then '\x01' else Char.chr (Random.int 256)) in
    match call s with
    | r when String.length r >= 1 && r.[0] = '\x00' -> incr oks
    | r when String.length r = 2 && r.[0] = '\x01' && List.mem (Char.code r.[1]) [1; 3; 4; 5; 16; 17; 18; 19] -> ()
    | r -> incr bad; if !bad <= 5 then Printf.printf "FAIL fuzz %s -> %s\n" (hex s) (hex r)
    | exception e -> incr bad; if !bad <= 5 then Printf.printf "FAIL fuzz %s raised %s\n" (hex s) (Printexc.to_string e)
  done;
  Printf.printf "fuzz: %d inputs, %d ok responses, %d malformed/exceptions\n" n !oks !bad;
  failures := !failures + !bad;
  if !failures > 0 then (Printf.printf "%d FAILURES\n" !failures; exit 1) else print_endline "== Gate 2 tests PASSED =="
