import Spike.Order

/-!
Mutual and parametric domain types for the generator (see `Spike.Api`):

* `Cond` / `Rule`: discount rules, mutually recursive. A rule gives a percentage when its
  condition holds, or takes the best of several rules (`List Rule`, nested inside the mutual
  block); a condition can test the order or whether another rule fires.
* `Batch α`: a parametric container (used as `Batch Order` and `Batch (Except OrderErr Quote)`).
* `PTree α`: a parametric rose tree.
-/

namespace Spike.Rules
open Spike.Order

mutual
inductive Cond where
  | minQty (n : Nat)         -- total quantity ≥ n
  | hasSku (sku : Nat)
  | not (c : Cond)
  | both (a b : Cond)
  | fires (r : Rule)         -- the rule gives a non-zero discount
inductive Rule where
  | pct (cond : Cond) (pct : Nat)
  | best (rules : List Rule)
end

def totalQty : List Line → Nat
  | [] => 0
  | l :: ls => l.qty + totalQty ls

def hasSku (s : Nat) : List Line → Bool
  | [] => false
  | l :: ls => l.sku == s || hasSku s ls

mutual
def Cond.holds (o : Order) : Cond → Bool
  | .minQty n => decide (n ≤ totalQty o.lines)
  | .hasSku s => hasSku s o.lines
  | .not c => !c.holds o
  | .both a b => a.holds o && b.holds o
  | .fires r => decide (0 < r.discount o)
termination_by structural c => c
/-- The discount percentage a rule gives for an order (best of all firing rules). -/
def Rule.discount (o : Order) : Rule → Nat
  | .pct c p => if c.holds o then p else 0
  | .best rs => Rule.discountList o rs
termination_by structural r => r
def Rule.discountList (o : Order) : List Rule → Nat
  | [] => 0
  | r :: rs => max (r.discount o) (Rule.discountList o rs)
termination_by structural rs => rs
end

mutual
/-- The largest percentage written anywhere in a rule (conditions included). -/
def Cond.cap : Cond → Nat
  | .minQty _ | .hasSku _ => 0
  | .not c => c.cap
  | .both a b => max a.cap b.cap
  | .fires r => r.cap
termination_by structural c => c
def Rule.cap : Rule → Nat
  | .pct c p => max c.cap p
  | .best rs => Rule.capList rs
termination_by structural r => r
def Rule.capList : List Rule → Nat
  | [] => 0
  | r :: rs => max r.cap (Rule.capList rs)
termination_by structural rs => rs
end

mutual
/-- A rule never gives more than the largest percentage written in it. -/
theorem Rule.discount_le_cap (o : Order) : ∀ (r : Rule), r.discount o ≤ r.cap
  | .pct c p => by
    simp only [Rule.discount, Rule.cap]
    split <;> omega
  | .best rs => by
    simp only [Rule.discount, Rule.cap]
    exact Rule.discountList_le_capList o rs
termination_by structural r => r
theorem Rule.discountList_le_capList (o : Order) : ∀ (rs : List Rule), Rule.discountList o rs ≤ Rule.capList rs
  | [] => by simp [Rule.discountList, Rule.capList]
  | r :: rs => by
    simp only [Rule.discountList, Rule.capList]
    have h1 := Rule.discount_le_cap o r
    have h2 := Rule.discountList_le_capList o rs
    omega
termination_by structural rs => rs
end

structure Batch (α : Type) where
  items : List α

inductive PTree (α : Type) where
  | leaf (a : α)
  | node (kids : List (PTree α))

mutual
def PTree.sum : PTree Nat → Nat
  | .leaf a => a
  | .node ks => PTree.sumList ks
termination_by structural t => t
def PTree.sumList : List (PTree Nat) → Nat
  | [] => 0
  | t :: ts => t.sum + PTree.sumList ts
termination_by structural ts => ts
end

end Spike.Rules
