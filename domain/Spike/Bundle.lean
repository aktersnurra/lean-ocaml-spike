/-!
A nested recursive domain type: product bundles. A bundle is a single item or a group of
sub-bundles with its own discount, so discounts nest (a 10%-off group inside a 5%-off
group, ...). Exercises `deriving Codec` for nested recursion (`List Bundle` inside
`Bundle`); see `Spike.Api`.
-/

namespace Spike.Bundle

inductive Bundle where
  | item (sku qty unitPrice : Nat)
  | group (discountPct : Nat) (parts : List Bundle)
deriving Repr

mutual
/-- Price with all nested discounts applied (discounts above 100% count as 100%). -/
def Bundle.price : Bundle → Nat
  | .item _ q p => q * p
  | .group d ps => let s := Bundle.priceList ps; s - s * min d 100 / 100
termination_by structural b => b
def Bundle.priceList : List Bundle → Nat
  | [] => 0
  | b :: bs => b.price + Bundle.priceList bs
termination_by structural bs => bs
end

mutual
/-- Price without any discount. -/
def Bundle.gross : Bundle → Nat
  | .item _ q p => q * p
  | .group _ ps => Bundle.grossList ps
termination_by structural b => b
def Bundle.grossList : List Bundle → Nat
  | [] => 0
  | b :: bs => b.gross + Bundle.grossList bs
termination_by structural bs => bs
end

theorem discounted_le (s d : Nat) : s - s * min d 100 / 100 ≤ s := Nat.sub_le _ _

mutual
/-- Nested discounts never make a bundle cost more than its undiscounted price. -/
theorem Bundle.price_le_gross : ∀ (b : Bundle), b.price ≤ b.gross
  | .item _ _ _ => by simp [Bundle.price, Bundle.gross]
  | .group d ps => by
    simp only [Bundle.price, Bundle.gross]
    exact Nat.le_trans (discounted_le _ d) (Bundle.priceList_le_grossList ps)
termination_by structural b => b
theorem Bundle.priceList_le_grossList : ∀ (bs : List Bundle), Bundle.priceList bs ≤ Bundle.grossList bs
  | [] => by simp [Bundle.priceList, Bundle.grossList]
  | b :: bs => by
    simp only [Bundle.priceList, Bundle.grossList]
    exact Nat.add_le_add (Bundle.price_le_gross b) (Bundle.priceList_le_grossList bs)
termination_by structural bs => bs
end

/-- A nested recursive *structure* (single constructor): a product category tree. -/
structure Category where
  id : Nat
  children : List Category

end Spike.Bundle
