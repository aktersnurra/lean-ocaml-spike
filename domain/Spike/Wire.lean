/-!
Wire primitives for the byte boundary: bytes as `List Nat` (each element < 256),
unsigned LEB128 varints, and length-prefixed lists. Everything is total and structurally
recursive. Round-trip and "output is bytes" lemmas live next to the definitions.
-/

namespace Spike.Wire

abbrev Bytes := List Nat

/-- Transport-level decode errors. Domain errors are separate (see `Spike.Order`). -/
inductive Err where
  | empty          -- request has no op byte
  | notBytes       -- some element is > 255 (transport invariant broken)
  | unknownOp      -- op byte not recognised
  | truncated      -- input ran out in the middle of a value
  | trailing       -- bytes left over after the payload
  | badTag         -- constructor tag out of range (generated codecs, wire format v2)
  | tooLarge       -- request longer than the API's size limit (wire format v2)
deriving DecidableEq, Repr

def Err.code : Err → Nat
  | .empty => 1 | .notBytes => 2 | .unknownOp => 3 | .truncated => 4 | .trailing => 5 | .badTag => 6 | .tooLarge => 7

/-- Every element is a byte. -/
def allBytes : Bytes → Bool
  | [] => true
  | b :: bs => if b < 256 then allBytes bs else false

theorem allBytes_append (a b : Bytes) : allBytes (a ++ b) = (allBytes a && allBytes b) := by
  induction a with
  | nil => simp [allBytes]
  | cons x xs ih => by_cases h : x < 256 <;> simp [allBytes, ih, h]

/-! ### Varints -/

/-- LEB128 encoding with explicit fuel; `encodeNat` supplies enough. -/
def encodeAux : Nat → Nat → Bytes
  | 0, _ => []
  | k + 1, n => if n < 128 then [n] else (n % 128 + 128) :: encodeAux k (n / 128)

def encodeNat (n : Nat) : Bytes := encodeAux (n + 1) n

/-- Is there a terminating byte (< 128) before the input runs out? Tail recursive, no
arithmetic, so an unterminated varint of any length is rejected in linear time without
building a bignum. -/
def terminated : Bytes → Bool
  | [] => false
  | b :: rest => if b < 128 then true else terminated rest

/-- Tail-recursive LEB128 accumulation: `m` is the current place value, `acc` the sum so far. -/
def decodeNatAux : Nat → Nat → Bytes → Except Err (Nat × Bytes)
  | _, _, [] => .error .truncated
  | m, acc, b :: rest =>
    if b < 128 then .ok (acc + m * b, rest)
    else decodeNatAux (m * 128) (acc + m * (b - 128)) rest

/-- LEB128 decoding; returns the value and the rest of the input. Uses constant stack. -/
def decodeNat (bs : Bytes) : Except Err (Nat × Bytes) :=
  if terminated bs then decodeNatAux 1 0 bs else .error .truncated

theorem terminated_encodeAux (k n : Nat) (rest : Bytes) (h : n < k) :
    terminated (encodeAux k n ++ rest) = true := by
  induction k generalizing n with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    rcases Nat.lt_or_ge n 128 with hn | hn
    · simp only [encodeAux, hn, if_true, List.cons_append, List.nil_append, terminated]
    · have h1 : n / 128 < k := by omega
      have hn' : ¬ n < 128 := by omega
      have hb : ¬ (n % 128 + 128 < 128) := by omega
      simp only [encodeAux, hn', if_false, List.cons_append, terminated, hb, ih (n / 128) h1]

theorem decodeNatAux_encodeAux (k n m acc : Nat) (rest : Bytes) (h : n < k) :
    decodeNatAux m acc (encodeAux k n ++ rest) = .ok (acc + m * n, rest) := by
  induction k generalizing n m acc with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    rcases Nat.lt_or_ge n 128 with hn | hn
    · simp only [encodeAux, hn, if_true, List.cons_append, List.nil_append, decodeNatAux]
    · have h1 : n / 128 < k := by omega
      have hn' : ¬ n < 128 := by omega
      have hb : ¬ (n % 128 + 128 < 128) := by omega
      have h2 : n % 128 + 128 - 128 = n % 128 := by omega
      simp only [encodeAux, hn', if_false, List.cons_append, decodeNatAux, hb,
        ih (n / 128) _ _ h1, h2]
      have hv : n % 128 + 128 * (n / 128) = n := Nat.mod_add_div n 128
      have : m * (n % 128) + m * 128 * (n / 128) = m * n := by
        rw [Nat.mul_assoc, ← Nat.mul_add, hv]
      rw [Nat.add_assoc, this]

theorem decodeNat_encodeAux (k n : Nat) (rest : Bytes) (h : n < k) :
    decodeNat (encodeAux k n ++ rest) = .ok (n, rest) := by
  simp only [decodeNat, terminated_encodeAux k n rest h, if_true,
    decodeNatAux_encodeAux k n 1 0 rest h, Nat.zero_add, Nat.one_mul]

theorem decodeNat_encodeNat (n : Nat) (rest : Bytes) :
    decodeNat (encodeNat n ++ rest) = .ok (n, rest) :=
  decodeNat_encodeAux _ _ _ (Nat.lt_succ_self n)

theorem allBytes_encodeAux (k n : Nat) : allBytes (encodeAux k n) = true := by
  induction k generalizing n with
  | zero => simp [encodeAux, allBytes]
  | succ k ih =>
    by_cases hn : n < 128
    · simp [encodeAux, hn, allBytes]; omega
    · simp [encodeAux, hn, allBytes, ih]; omega

theorem allBytes_encodeNat (n : Nat) : allBytes (encodeNat n) = true := allBytes_encodeAux _ _

/-! ### Length-prefixed lists -/

def encodeElems (enc : α → Bytes) : List α → Bytes
  | [] => []
  | x :: xs => enc x ++ encodeElems enc xs

def encodeList (enc : α → Bytes) (xs : List α) : Bytes :=
  encodeNat xs.length ++ encodeElems enc xs

/-- Decode `n` elements into an accumulator (reversed), tail recursive. Structural on `n`;
every element decoder used here consumes input or fails, so a huge claimed count on short
input ends with `truncated` after at most `input length` steps. -/
def decodeElemsAux (dec : Bytes → Except Err (α × Bytes)) :
    Nat → List α → Bytes → Except Err (List α × Bytes)
  | 0, acc, bs => .ok (acc.reverse, bs)
  | n + 1, acc, bs =>
    match dec bs with
    | .error e => .error e
    | .ok (x, r) => decodeElemsAux dec n (x :: acc) r

def decodeElems (dec : Bytes → Except Err (α × Bytes)) (n : Nat) (bs : Bytes) :
    Except Err (List α × Bytes) :=
  decodeElemsAux dec n [] bs

def decodeList (dec : Bytes → Except Err (α × Bytes)) (bs : Bytes) : Except Err (List α × Bytes) :=
  match decodeNat bs with
  | .error e => .error e
  | .ok (n, r) => decodeElems dec n r

theorem decodeElemsAux_encodeElems (enc : α → Bytes) (dec : Bytes → Except Err (α × Bytes))
    (hdec : ∀ x rest, dec (enc x ++ rest) = .ok (x, rest)) (xs acc : List α) (rest : Bytes) :
    decodeElemsAux dec xs.length acc (encodeElems enc xs ++ rest) = .ok (acc.reverse ++ xs, rest) := by
  induction xs generalizing acc with
  | nil => simp [encodeElems, decodeElemsAux]
  | cons x xs ih => simp [encodeElems, decodeElemsAux, List.append_assoc, hdec, ih]

theorem decodeElems_encodeElems (enc : α → Bytes) (dec : Bytes → Except Err (α × Bytes))
    (hdec : ∀ x rest, dec (enc x ++ rest) = .ok (x, rest)) (xs : List α) (rest : Bytes) :
    decodeElems dec xs.length (encodeElems enc xs ++ rest) = .ok (xs, rest) := by
  simp [decodeElems, decodeElemsAux_encodeElems enc dec hdec]

theorem decodeList_encodeList (enc : α → Bytes) (dec : Bytes → Except Err (α × Bytes))
    (hdec : ∀ x rest, dec (enc x ++ rest) = .ok (x, rest)) (xs : List α) (rest : Bytes) :
    decodeList dec (encodeList enc xs ++ rest) = .ok (xs, rest) := by
  simp [decodeList, encodeList, List.append_assoc, decodeNat_encodeNat,
    decodeElems_encodeElems enc dec hdec]

theorem allBytes_encodeList (enc : α → Bytes) (henc : ∀ x, allBytes (enc x) = true)
    (xs : List α) : allBytes (encodeList enc xs) = true := by
  simp only [encodeList, allBytes_append, allBytes_encodeNat, Bool.true_and]
  induction xs with
  | nil => simp [encodeElems, allBytes]
  | cons x xs ih => simp [encodeElems, allBytes_append, henc, ih]

/-- Decode a value that must consume the whole input. -/
def exact (r : Except Err (α × Bytes)) : Except Err α :=
  match r with
  | .error e => .error e
  | .ok (x, []) => .ok x
  | .ok (_, _ :: _) => .error .trailing

end Spike.Wire
