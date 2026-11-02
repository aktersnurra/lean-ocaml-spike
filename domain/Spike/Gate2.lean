import LeanToLambdaBox
import Spike.Gate1
import Spike.Wire
import Spike.Order

/-!
The extracted byte boundary (module `Gate2` on the OCaml side).

`handle : List Nat → List Nat` (OCaml: `Z.t list -> Z.t list`). All parsing, dispatch,
serialization and error tagging happen here. The OCaml side only converts
`bytes <-> Z.t list` and checks that each element is a byte.

Wire format v1 (integers are unsigned LEB128 varints, lists are varint count + elements):
  request  = op:byte payload
    op 0x01 gate1:      payload = n                                -> ok n'      (n' = 2n+1)
    op 0x02 priceOrder: payload = customer discountPct [line]      -> ok quote
                        line    = sku qty unitPrice
                        quote   = subtotal discount total lineCount
  response = 0x00 payload        success
           | 0x01 code:byte      error
    transport codes 1 empty, 2 notBytes, 3 unknownOp, 4 truncated, 5 trailing
    domain codes   16 noLines, 17 zeroQty, 18 badDiscount, 19 duplicateSku

No `partial`, well-founded recursion, `implemented_by`, `extern` or `Float` in this module
or anything it extracts.
-/

namespace Spike.Wire
open Spike.Order

def dispatch : Bytes → Except Nat Bytes
  | [] => .error Err.empty.code
  | op :: payload =>
    if op = 1 then
      match exact (decodeNat payload) with
      | .error e => .error e.code
      | .ok n => .ok (encodeNat (Spike.gate1 n))
    else if op = 2 then
      match exact (decodeOrder payload) with
      | .error e => .error e.code
      | .ok o =>
        match priceOrder o with
        | .error d => .error d.code
        | .ok q => .ok (encodeQuote q)
    else .error Err.unknownOp.code

def respond : Except Nat Bytes → Bytes
  | .ok payload => 0 :: payload
  | .error c => [1, c]

/-- The extracted entry point. -/
def handle (req : Bytes) : Bytes :=
  if allBytes req then respond (dispatch req) else respond (.error Err.notBytes.code)

/-! ### End-to-end theorems about the extracted function -/

theorem err_code_lt (e : Err) : e.code < 256 := by cases e <;> decide
theorem orderErr_code_lt (e : OrderErr) : e.code < 256 := by cases e <;> decide

/-- Every response is a byte string, so the OCaml boundary's byte check can only fail if
the trusted pipeline (extraction, runtime axioms, compiler) is broken. -/
theorem allBytes_handle (req : Bytes) : allBytes (handle req) = true := by
  unfold handle
  split
  · unfold dispatch
    split
    · simp [respond, allBytes, Err.code]
    · split
      · split <;> simp_all [respond, allBytes, allBytes_encodeNat, err_code_lt]
      · split
        · split
          · simp [respond, allBytes, err_code_lt]
          · split <;> simp [respond, allBytes, orderErr_code_lt, allBytes_encodeQuote]
        · simp [respond, allBytes, Err.code]
  · simp [respond, allBytes, Err.code]

/-- On a well-formed order request, the response is exactly the encoded result of the
domain function. -/
theorem handle_priceOrder (o : Order) :
    handle (2 :: encodeOrder o) =
      match priceOrder o with
      | .ok q => 0 :: encodeQuote q
      | .error d => [1, d.code] := by
  have hb : allBytes (2 :: encodeOrder o) = true := by
    simp [allBytes, allBytes_encodeOrder]
  simp only [handle, hb, if_true, dispatch, exact_decodeOrder_encodeOrder]
  simp only [show (2 : Nat) ≠ 1 by decide, if_false]
  split <;> simp_all [respond]

/-! Kernel-checked examples (erased before extraction). `notBytes` cannot be produced from
real OCaml bytes, so it is only testable here. -/
example : handle [1, 300] = [1, 2] := by decide
example : handle [] = [1, 1] := by decide
example : handle [7] = [1, 3] := by decide
example : handle [1, 128] = [1, 4] := by decide
example : handle [1, 5, 0] = [1, 5] := by decide
example : handle [1, 5] = [0, 11] := by decide
example : handle [1, 128, 1] = [0, 129, 2] := by decide
-- order: customer 1, 10% off, lines (sku 7, qty 2, 150c) and (sku 8, qty 1, 100c)
example : handle [2, 1, 10, 2, 7, 2, 150, 1, 8, 1, 100] = [0, 144, 3, 40, 232, 2, 2] := by decide
example : handle [2, 1, 10, 0] = [1, 16] := by decide
example : handle [2, 1, 101, 1, 7, 1, 1] = [1, 18] := by decide
example : handle [2, 1, 0, 1, 7, 0, 1] = [1, 17] := by decide
example : handle [2, 1, 0, 2, 7, 1, 1, 7, 1, 1] = [1, 19] := by decide

end Spike.Wire

#erase Spike.Wire.handle config {remove_irrel_constr_args := true} to "build/gate2.ast" mli "build/gate2.mli"
