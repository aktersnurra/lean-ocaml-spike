(* Hand-written axioms for Lean's ByteArray/UInt8 (option (b) probe). TRUSTED, UNVERIFIED. *)
val def__UInt8_ofNat : Z.t -> int
val def__ByteArray_emptyWithCapacity : Z.t -> bytes
val def__ByteArray_size : bytes -> Z.t
val def__ByteArray_get_u33 : bytes -> Z.t -> int
val def__ByteArray_push : bytes -> int -> bytes
