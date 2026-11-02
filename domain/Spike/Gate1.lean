import LeanToLambdaBox

/-!
Gate 1: the smallest function that still exercises Nat (a bignum in the OCaml
runtime, via zarith) and a proof that is erased during extraction.

`#erase` writes the lambda-box program (`.ast`) and the OCaml signature (`.mli`)
for the named definition. The extracted OCaml module exposes it as `main`.
The output directory is `build/` relative to where `lake lean` is run
(see scripts/gate1.sh).
-/

namespace Spike

/-- Double and add one. -/
def gate1 (n : Nat) : Nat := n * 2 + 1

/-- The invariant we prove and expect to disappear at extraction time. -/
theorem gate1_odd (n : Nat) : gate1 n % 2 = 1 := by
  unfold gate1
  omega

end Spike

#erase Spike.gate1 config {remove_irrel_constr_args := true} to "build/gate1.ast" mli "build/gate1.mli"
