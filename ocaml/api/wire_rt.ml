(* Runtime for generated OCaml codecs (wire format v2). Hand-written, small, TRUSTED but
   UNVERIFIED: it must agree with the Lean primitives in domain/Spike/Wire.lean and
   domain/Spike/Codec.lean. ocaml/test/test_api.ml checks that agreement differentially
   (OCaml-encoded values decoded by the Lean core and vice versa, plus fuzzing). *)

exception Decode_error of int

(* Same codes as Spike.Wire.Err.code. *)
let truncated = 4
let trailing = 5
let bad_tag = 6

type cursor = { buf : bytes; mutable pos : int }

let byte c =
  if c.pos >= Bytes.length c.buf then raise (Decode_error truncated);
  let b = Char.code (Bytes.unsafe_get c.buf c.pos) in
  c.pos <- c.pos + 1;
  b

let tag b i = Buffer.add_char b (Char.chr i)

(* Unsigned LEB128, as Spike.Wire.encodeNat (canonical). *)
let enc_nat b z =
  if Z.sign z < 0 then invalid_arg "Wire_rt.enc_nat: negative value for a Nat field";
  let z = ref z and fin = ref false in
  while not !fin do
    let lo = Z.to_int (Z.logand !z (Z.of_int 127)) in
    z := Z.shift_right !z 7;
    if Z.equal !z Z.zero then (Buffer.add_char b (Char.chr lo); fin := true)
    else Buffer.add_char b (Char.chr (lo lor 128))
  done

(* As Spike.Wire.decodeNat: accepts non-canonical forms; truncated if unterminated. *)
let dec_nat c =
  let acc = ref Z.zero and shift = ref 0 and fin = ref false in
  while not !fin do
    let x = byte c in
    acc := Z.add !acc (Z.shift_left (Z.of_int (x land 127)) !shift);
    shift := !shift + 7;
    if x < 128 then fin := true
  done;
  !acc

let enc_bool b v = Buffer.add_char b (if v then '\001' else '\000')
let dec_bool c = match byte c with 0 -> false | 1 -> true | _ -> raise (Decode_error bad_tag)

let enc_list f b xs = enc_nat b (Z.of_int (List.length xs)); List.iter (f b) xs

let dec_list f c =
  let n = dec_nat c in
  let acc = ref [] and i = ref Z.zero in
  while Z.lt !i n do acc := f c :: !acc; i := Z.succ !i done;
  List.rev !acc

let enc_except fa fe b = function Ok a -> tag b 0; fa b a | Error e -> tag b 1; fe b e
let dec_except fa fe c = match byte c with 0 -> Ok (fa c) | 1 -> Error (fe c) | _ -> raise (Decode_error bad_tag)

let to_bytes f x = let b = Buffer.create 64 in f b x; Buffer.to_bytes b

(* Decode a whole input; Error code on failure (same codes and precedence as the Lean decoder). *)
let decode f bs =
  let c = { buf = bs; pos = 0 } in
  match f c with
  | v -> if c.pos <> Bytes.length bs then Error trailing else Ok v
  | exception Decode_error e -> Error e
