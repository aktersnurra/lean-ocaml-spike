/-!
A small recursive domain type: pricing formulas over one input `x` (e.g. a quantity),
evaluated over `Nat` (subtraction truncates, division by zero is zero, as in Lean).
Exercises `deriving Codec` for recursive types (see `Spike.Api`).
-/

namespace Spike.Formula

inductive Formula where
  | lit (n : Nat)
  | x
  | add (a b : Formula)
  | sub (a b : Formula)
  | mul (a b : Formula)
  | div (a b : Formula)
  | ifLt (a b thn els : Formula)   -- if a < b then thn else els
deriving DecidableEq, Repr

def Formula.eval (v : Nat) : Formula → Nat
  | .lit n => n
  | .x => v
  | .add a b => a.eval v + b.eval v
  | .sub a b => a.eval v - b.eval v
  | .mul a b => a.eval v * b.eval v
  | .div a b => a.eval v / b.eval v
  | .ifLt a b t e => if a.eval v < b.eval v then t.eval v else e.eval v

def Formula.size : Formula → Nat
  | .lit _ | .x => 1
  | .add a b | .sub a b | .mul a b | .div a b => a.size + b.size + 1
  | .ifLt a b t e => a.size + b.size + t.size + e.size + 1

/-- Example domain fact: a formula with no `sub`/`div`/`ifLt` is monotone in `x`. -/
def Formula.monotoneShape : Formula → Bool
  | .lit _ | .x => true
  | .add a b | .mul a b => a.monotoneShape && b.monotoneShape
  | _ => false

theorem Formula.eval_mono (f : Formula) (h : f.monotoneShape = true) {v w : Nat} (hvw : v ≤ w) :
    f.eval v ≤ f.eval w := by
  induction f with
  | lit n => simp [eval]
  | x => simpa [eval]
  | add a b iha ihb =>
    simp [monotoneShape] at h
    exact Nat.add_le_add (iha h.1) (ihb h.2)
  | mul a b iha ihb =>
    simp [monotoneShape] at h
    exact Nat.mul_le_mul (iha h.1) (ihb h.2)
  | sub | div | ifLt => simp [monotoneShape] at h

end Spike.Formula
