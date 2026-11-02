import LeanToLambdaBox
/-! Gate 2 option (b) probe: an opaque byte type (Lean `ByteArray`) with hand-written OCaml
axioms (experiments/gate2b/bytearray.ml). Not part of the core; see README "Gate 2". -/
/-- Reverse the bytes, then append the length mod 256. -/
def probeB (b : ByteArray) : ByteArray :=
  let rec go : Nat → ByteArray → ByteArray
    | 0, acc => acc
    | k + 1, acc => go k (acc.push (b.get! k))
  (go b.size ByteArray.empty).push (UInt8.ofNat b.size)
#erase probeB config {remove_irrel_constr_args := true} to "build/probe_b/probeB.ast" mli "build/probe_b/probeB.mli"
