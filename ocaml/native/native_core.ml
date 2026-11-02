(* Straightforward native implementation of wire format v1 (see domain/Spike/Gate2.lean).
   Amounts use Zarith so that semantics match the Lean core exactly (unbounded naturals);
   this is what makes byte-for-byte differential testing possible. *)

exception Fail of int

let handle (req : bytes) : bytes =
  let n = Bytes.length req in
  let pos = ref 0 in
  let byte () =
    if !pos >= n then raise (Fail 4);
    let b = Char.code (Bytes.unsafe_get req !pos) in
    incr pos; b
  in
  (* LEB128, same value semantics as Lean's decodeNat (non-canonical forms accepted). *)
  let varint () =
    let acc = ref Z.zero and shift = ref 0 and fin = ref false in
    while not !fin do
      let b = byte () in
      acc := Z.add !acc (Z.shift_left (Z.of_int (b land 127)) !shift);
      shift := !shift + 7;
      if b < 128 then fin := true
    done;
    !acc
  in
  let buf = Buffer.create 32 in
  let emit z =
    let z = ref z in
    let fin = ref false in
    while not !fin do
      let lo = Z.to_int (Z.logand !z (Z.of_int 127)) in
      z := Z.shift_right !z 7;
      if Z.equal !z Z.zero then (Buffer.add_char buf (Char.chr lo); fin := true)
      else Buffer.add_char buf (Char.chr (lo lor 128))
    done
  in
  let finish () = if !pos <> n then raise (Fail 5) in
  try
    if n = 0 then raise (Fail 1);
    let op = byte () in
    Buffer.add_char buf '\x00';
    (match op with
     | 1 ->
       let v = varint () in
       finish ();
       emit (Z.succ (Z.mul v (Z.of_int 2)))
     | 2 ->
       let _customer = varint () in
       let pct = varint () in
       let count = varint () in
       let lines = ref [] in
       let i = ref Z.zero in
       while Z.lt !i count do
         let sku = varint () in
         let qty = varint () in
         let price = varint () in
         lines := (sku, qty, price) :: !lines;
         i := Z.succ !i
       done;
       finish ();
       let lines = !lines in
       if lines = [] then raise (Fail 16);
       if Z.gt pct (Z.of_int 100) then raise (Fail 18);
       if List.exists (fun (_, q, _) -> Z.equal q Z.zero) lines then raise (Fail 17);
       let seen = Hashtbl.create 16 in
       List.iter (fun (s, _, _) -> if Hashtbl.mem seen s then raise (Fail 19); Hashtbl.add seen s ()) lines;
       let sub = List.fold_left (fun a (_, q, p) -> Z.add a (Z.mul q p)) Z.zero lines in
       let disc = Z.div (Z.mul sub pct) (Z.of_int 100) in
       emit sub; emit disc; emit (Z.sub sub disc); emit (Z.of_int (List.length lines))
     | _ -> raise (Fail 3));
    Buffer.to_bytes buf
  with Fail c -> Bytes.of_string (Printf.sprintf "\x01%c" (Char.chr c))
