import order.bounded_order

open function

namespace with_bot
variables {α : Type*} {C : with_bot α → Sort*} (h₁ : C ⊥) (h₂ : Π a : α, C ↑a)

lemma coe_injective : injective (coe : α → with_bot α) := option.some_injective _

lemma coe_ne_coe {a b : α} : (a : with_bot α) ≠ b ↔ a ≠ b := coe_eq_coe.not

instance [has_lt α] [is_well_order α (<)] : is_strict_total_order' (with_bot α) (<) :=
begin
  classical,
  letI : linear_order α := linear_order_of_STO' (<),
  apply_instance
end

instance [preorder α] [is_well_order α (<)] :  is_well_order (with_bot α) (<) :=
⟨well_founded_lt ‹is_well_order α (<)›.2⟩

end with_bot
