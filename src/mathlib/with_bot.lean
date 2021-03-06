import order.bounded_order

open function

namespace with_bot
variables {α : Type*} {C : with_bot α → Sort*} (h₁ : C ⊥) (h₂ : Π a : α, C ↑a)

lemma coe_injective : injective (coe : α → with_bot α) := option.some_injective _

lemma coe_ne_coe {a b : α} : (a : with_bot α) ≠ b ↔ a ≠ b := coe_eq_coe.not

end with_bot
