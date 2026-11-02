import LeanToLambdaBox
import Spike.Gate1

/-!
Gate 2: an opaque byte boundary, option (a): bytes are `List Nat` with every element in 0..255.

The extracted entry point is `main : List Nat → List Nat` (OCaml: `Z.t list -> Z.t list`).
All parsing and serialization happens here, in Lean. The OCaml side only converts
`bytes <-> Z.t list` and checks the transport invariant (every element is a byte); it
never looks at domain values or decides on errors.

Wire format v0 (all integers are unsigned LEB128 varints):
  request  = op:byte  payload
             op 0x01 (gate1): payload = varint n          -> gate1 n
  response = 0x00 payload                                  success
           | 0x01 code:byte                                error, code below

Every function here is total and structurally recursive (no `partial`, no well-founded
recursion, no `implemented_by`/`extern`, no `Float`).
-/

namespace Spike.Wire

abbrev Bytes := List Nat

inductive Err where
  | empty          -- request has no op byte
  | notBytes       -- some element is > 255 (transport invariant broken)
  | unknownOp      -- op byte not recognised
  | truncated      -- varint ran off the end of the input
  | trailing       -- bytes left over after the payload
deriving DecidableEq, Repr

def Err.code : Err → Nat
  | .empty => 1 | .notBytes => 2 | .unknownOp => 3 | .truncated => 4 | .trailing => 5

/-- Every element is a byte. -/
def allBytes : Bytes → Bool
  | [] => true
  | b :: bs => decide (b < 256) && allBytes bs

/-- LEB128 encoding with explicit fuel; `encodeNat` supplies enough. -/
def encodeAux : Nat → Nat → Bytes
  | 0, _ => []
  | k + 1, n => if n < 128 then [n] else (n % 128 + 128) :: encodeAux k (n / 128)

def encodeNat (n : Nat) : Bytes := encodeAux (n + 1) n

/-- LEB128 decoding; returns the value and the rest of the input. Structural on the list. -/
def decodeNat : Bytes → Except Err (Nat × Bytes)
  | [] => .error .truncated
  | b :: rest =>
    if b < 128 then .ok (b, rest)
    else match decodeNat rest with
      | .error e => .error e
      | .ok (m, r) => .ok (b - 128 + 128 * m, r)

/-- Decode a varint that must consume the whole input. -/
def decodeNatExact (bs : Bytes) : Except Err Nat :=
  match decodeNat bs with
  | .error e => .error e
  | .ok (n, []) => .ok n
  | .ok (_, _ :: _) => .error .trailing

def dispatch : Bytes → Except Err Bytes
  | [] => .error .empty
  | op :: payload =>
    if op = 1 then
      match decodeNatExact payload with
      | .error e => .error e
      | .ok n => .ok (encodeNat (Spike.gate1 n))
    else .error .unknownOp

def respond : Except Err Bytes → Bytes
  | .ok payload => 0 :: payload
  | .error e => [1, e.code]

/-- The extracted entry point. -/
def handle (req : Bytes) : Bytes :=
  if allBytes req then respond (dispatch req) else respond (.error .notBytes)

/-! Kernel-checked examples (erased before extraction). `notBytes` cannot be produced from
real OCaml bytes, so it is only testable here. -/
example : handle [1, 300] = [1, 2] := by decide
example : handle [] = [1, 1] := by decide
example : handle [2] = [1, 3] := by decide
example : handle [1, 128] = [1, 4] := by decide
example : handle [1, 5, 0] = [1, 5] := by decide
example : handle [1, 5] = [0, 11] := by decide
example : handle [1, 128, 1] = [0, 129, 2] := by decide

end Spike.Wire

#erase Spike.Wire.handle config {remove_irrel_constr_args := true} to "build/gate2.ast" mli "build/gate2.mli"
