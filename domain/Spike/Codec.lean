import Spike.Wire

/-!
# `Codec`: wire codecs that carry their own correctness proofs

Every instance bundles an encoder, a decoder, and proofs that
* decoding an encoding gives back the value and leaves the rest of the input untouched, and
* encoders only emit bytes (elements < 256).

So any value of a type with a `Codec` instance round-trips by construction. Instances for
user types are produced by `deriving Codec` (see `Spike.Codec.Derive`). The proof fields
are erased at extraction; only `enc`/`dec` reach OCaml.
-/

namespace Spike.Wire

class Codec (α : Type) where
  enc : α → Bytes
  dec : Bytes → Except Err (α × Bytes)
  dec_enc : ∀ (x : α) (rest : Bytes), dec (enc x ++ rest) = .ok (x, rest)
  enc_bytes : ∀ (x : α), allBytes (enc x) = true

attribute [simp] Codec.dec_enc Codec.enc_bytes

/-- Decode a whole input with a codec (no trailing bytes). -/
def Codec.decodeExact [Codec α] (bs : Bytes) : Except Err α := exact (Codec.dec bs)

theorem Codec.decodeExact_enc [Codec α] (x : α) : Codec.decodeExact (Codec.enc x) = .ok x := by
  have h := Codec.dec_enc x []
  simp only [List.append_nil] at h
  simp [Codec.decodeExact, exact, h]

/-! ## Base instances -/

instance : Codec Nat where
  enc := encodeNat
  dec := decodeNat
  dec_enc := decodeNat_encodeNat
  enc_bytes := allBytes_encodeNat

def decodeBool : Bytes → Except Err (Bool × Bytes)
  | [] => .error .truncated
  | b :: r => if b = 0 then .ok (false, r) else if b = 1 then .ok (true, r) else .error .badTag

instance : Codec Bool where
  enc b := if b then [1] else [0]
  dec := decodeBool
  dec_enc := by intro x rest; cases x <;> simp [decodeBool]
  enc_bytes := by intro x; cases x <;> simp [allBytes]

instance [Codec α] : Codec (List α) where
  enc := encodeList Codec.enc
  dec := decodeList Codec.dec
  dec_enc := decodeList_encodeList Codec.enc Codec.dec Codec.dec_enc
  enc_bytes := allBytes_encodeList Codec.enc Codec.enc_bytes

/-- `Except ε α` on the wire: tag 0 = ok, tag 1 = error (same convention as wire v1). -/
def encodeExcept [Codec ε] [Codec α] : Except ε α → Bytes
  | .ok a => 0 :: Codec.enc a
  | .error e => 1 :: Codec.enc e

def decodeExcept [Codec ε] [Codec α] : Bytes → Except Err (Except ε α × Bytes)
  | [] => .error .truncated
  | t :: r =>
    if t = 0 then
      match Codec.dec r with
      | .error e => .error e
      | .ok (a, r') => .ok (.ok a, r')
    else if t = 1 then
      match Codec.dec r with
      | .error e => .error e
      | .ok (e, r') => .ok (.error e, r')
    else .error .badTag

instance [Codec ε] [Codec α] : Codec (Except ε α) where
  enc := encodeExcept
  dec := decodeExcept
  dec_enc := by intro x rest; cases x <;> simp [encodeExcept, decodeExcept]
  enc_bytes := by intro x; cases x <;> simp [encodeExcept, allBytes]

end Spike.Wire
