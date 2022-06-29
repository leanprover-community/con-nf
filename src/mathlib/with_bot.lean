import order.bounded_order

namespace with_bot
variables {α : Type*} {C : with_bot α → Sort*} (h₁ : C ⊥) (h₂ : Π a : α, C ↑a)

@[simp] lemma rec_bot_coe_bot : (rec_bot_coe h₁ h₂ (⊥ : with_bot α) : C ⊥) = h₁ := rfl
@[simp] lemma rec_bot_coe_coe (a : α) : (rec_bot_coe h₁ h₂ (a : with_bot α) : C a) = h₂ a := rfl

end with_bot
