import Spike.Wire
import Lean.Data.RBMap

/-!
Gate 3 domain core: price an order.

A representative pure domain function: validation with several distinct domain errors,
nested data (an order holds a list of lines), and arithmetic on unbounded naturals
(amounts are in cents). Includes domain theorems and the request/response codecs with
`decode (encode x) = x` proofs.
-/

namespace Spike.Order
open Spike.Wire

structure Line where
  sku : Nat
  qty : Nat
  unitPrice : Nat   -- cents
deriving DecidableEq, Repr

structure Order where
  customer : Nat
  discountPct : Nat -- 0..100
  lines : List Line
deriving DecidableEq, Repr

structure Quote where
  subtotal : Nat
  discount : Nat
  total : Nat
  lineCount : Nat
deriving DecidableEq, Repr

inductive OrderErr where
  | noLines | zeroQty | badDiscount | duplicateSku
deriving DecidableEq, Repr

/-- Domain error codes on the wire (16..19, disjoint from transport codes 1..5). -/
def OrderErr.code : OrderErr → Nat
  | .noLines => 16 | .zeroQty => 17 | .badDiscount => 18 | .duplicateSku => 19

-- All traversals over the (attacker-sized) line list are tail recursive.

def anyZeroQty : List Line → Bool
  | [] => false
  | l :: ls => if l.qty = 0 then true else anyZeroQty ls

/-- Duplicate check in O(n log n) with Lean's red-black tree map (`Lean.RBMap`, structural
recursion, no externs). `seen` holds the SKUs met so far. -/
def hasDupSkuAux (seen : Lean.RBMap Nat Unit compare) : List Line → Bool
  | [] => false
  | l :: ls => if seen.contains l.sku then true else hasDupSkuAux (seen.insert l.sku ()) ls

def hasDupSku (ls : List Line) : Bool := hasDupSkuAux {} ls

def subtotalAux (acc : Nat) : List Line → Nat
  | [] => acc
  | l :: ls => subtotalAux (acc + l.qty * l.unitPrice) ls

def subtotal (ls : List Line) : Nat := subtotalAux 0 ls

/-- The domain function. -/
def priceOrder (o : Order) : Except OrderErr Quote :=
  match o.lines with
  | [] => .error .noLines
  | _ :: _ =>
    if o.discountPct > 100 then .error .badDiscount
    else if anyZeroQty o.lines then .error .zeroQty
    else if hasDupSku o.lines then .error .duplicateSku
    else
      let sub := subtotal o.lines
      let disc := sub * o.discountPct / 100
      .ok { subtotal := sub, discount := disc, total := sub - disc, lineCount := o.lines.length }

/-! ### Domain theorems -/

theorem priceOrder_ok {o : Order} {q : Quote} (h : priceOrder o = .ok q) :
    q.discount ≤ q.subtotal ∧ q.total + q.discount = q.subtotal ∧
    q.subtotal = subtotal o.lines ∧ q.lineCount = o.lines.length ∧ o.lines ≠ [] ∧
    o.discountPct ≤ 100 := by
  unfold priceOrder at h
  split at h
  · cases h
  · rename_i hl
    by_cases hd : o.discountPct > 100
    · simp [hd] at h
    · by_cases hz : anyZeroQty o.lines
      · simp [hd, hz] at h
      · by_cases hs : hasDupSku o.lines
        · simp [hd, hz, hs] at h
        · simp only [hd, hz, hs, if_false, Bool.false_eq_true, Except.ok.injEq] at h
          subst h
          have hle : subtotal o.lines * o.discountPct / 100 ≤ subtotal o.lines := by
            calc subtotal o.lines * o.discountPct / 100
                ≤ subtotal o.lines * 100 / 100 :=
                  Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))
              _ = subtotal o.lines := Nat.mul_div_cancel _ (by decide)
          refine ⟨hle, by simp only; omega, rfl, rfl, by simp [hl], by omega⟩

theorem priceOrder_noLines (o : Order) (h : o.lines = []) : priceOrder o = .error .noLines := by
  simp [priceOrder, h]

/-! ### Codecs -/

def encodeLine (l : Line) : Bytes := encodeNat l.sku ++ encodeNat l.qty ++ encodeNat l.unitPrice

def decodeLine (bs : Bytes) : Except Err (Line × Bytes) :=
  match decodeNat bs with
  | .error e => .error e
  | .ok (sku, r1) =>
    match decodeNat r1 with
    | .error e => .error e
    | .ok (qty, r2) =>
      match decodeNat r2 with
      | .error e => .error e
      | .ok (price, r3) => .ok ({ sku := sku, qty := qty, unitPrice := price }, r3)

def encodeOrder (o : Order) : Bytes :=
  encodeNat o.customer ++ encodeNat o.discountPct ++ encodeList encodeLine o.lines

def decodeOrder (bs : Bytes) : Except Err (Order × Bytes) :=
  match decodeNat bs with
  | .error e => .error e
  | .ok (c, r1) =>
    match decodeNat r1 with
    | .error e => .error e
    | .ok (d, r2) =>
      match decodeList decodeLine r2 with
      | .error e => .error e
      | .ok (ls, r3) => .ok ({ customer := c, discountPct := d, lines := ls }, r3)

def encodeQuote (q : Quote) : Bytes :=
  encodeNat q.subtotal ++ encodeNat q.discount ++ encodeNat q.total ++ encodeNat q.lineCount

/-- Response decoder. Not used by the extracted core (OCaml clients decode responses);
defined so the response codec's round trip can be proved too. -/
def decodeQuote (bs : Bytes) : Except Err (Quote × Bytes) :=
  match decodeNat bs with
  | .error e => .error e
  | .ok (s, r1) =>
    match decodeNat r1 with
    | .error e => .error e
    | .ok (d, r2) =>
      match decodeNat r2 with
      | .error e => .error e
      | .ok (t, r3) =>
        match decodeNat r3 with
        | .error e => .error e
        | .ok (n, r4) => .ok ({ subtotal := s, discount := d, total := t, lineCount := n }, r4)

/-! ### Round trips: `decode (encode x) = x` -/

theorem decodeLine_encodeLine (l : Line) (rest : Bytes) :
    decodeLine (encodeLine l ++ rest) = .ok (l, rest) := by
  simp [decodeLine, encodeLine, List.append_assoc, decodeNat_encodeNat]

theorem decodeOrder_encodeOrder (o : Order) (rest : Bytes) :
    decodeOrder (encodeOrder o ++ rest) = .ok (o, rest) := by
  simp [decodeOrder, encodeOrder, List.append_assoc, decodeNat_encodeNat,
    decodeList_encodeList encodeLine decodeLine decodeLine_encodeLine]

theorem decodeQuote_encodeQuote (q : Quote) (rest : Bytes) :
    decodeQuote (encodeQuote q ++ rest) = .ok (q, rest) := by
  simp [decodeQuote, encodeQuote, List.append_assoc, decodeNat_encodeNat]

/-- The headline round trip for the request type. -/
theorem exact_decodeOrder_encodeOrder (o : Order) :
    exact (decodeOrder (encodeOrder o)) = .ok o := by
  have := decodeOrder_encodeOrder o []
  simp only [List.append_nil] at this
  simp [exact, this]

theorem exact_decodeQuote_encodeQuote (q : Quote) :
    exact (decodeQuote (encodeQuote q)) = .ok q := by
  have := decodeQuote_encodeQuote q []
  simp only [List.append_nil] at this
  simp [exact, this]

/-! ### Encoders only produce bytes -/

theorem allBytes_encodeLine (l : Line) : allBytes (encodeLine l) = true := by
  simp [encodeLine, allBytes_append, allBytes_encodeNat]

theorem allBytes_encodeOrder (o : Order) : allBytes (encodeOrder o) = true := by
  simp [encodeOrder, allBytes_append, allBytes_encodeNat,
    allBytes_encodeList encodeLine allBytes_encodeLine]

theorem allBytes_encodeQuote (q : Quote) : allBytes (encodeQuote q) = true := by
  simp [encodeQuote, allBytes_append, allBytes_encodeNat]

end Spike.Order
