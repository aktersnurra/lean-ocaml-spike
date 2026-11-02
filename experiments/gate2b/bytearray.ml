(* Representation: Lean ByteArray = OCaml bytes, never mutated after creation (Lean values are
   persistent; push copies, so it is O(n)). Lean UInt8 = OCaml int in 0..255. *)
let z256 = Z.of_int 256
let def__UInt8_ofNat n = Z.to_int (Z.erem n z256)
let def__ByteArray_emptyWithCapacity _ = Bytes.empty
let def__ByteArray_size b = Z.of_int (Bytes.length b)
(* Lean's get! returns the default (0) out of bounds (after a panic message). *)
let def__ByteArray_get_u33 b i =
  if Z.sign i >= 0 && Z.lt i (Z.of_int (Bytes.length b)) then Char.code (Bytes.get b (Z.to_int i)) else 0
let def__ByteArray_push b x =
  let n = Bytes.length b in
  let r = Bytes.create (n + 1) in
  Bytes.blit b 0 r 0 n; Bytes.set r n (Char.chr (x land 255)); r
