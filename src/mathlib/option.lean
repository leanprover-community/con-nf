import group_theory.group_action.defs

variables {α β : Type*}

namespace option

section has_scalar
variables [has_scalar α β]

instance : has_scalar α (option β) := ⟨λ a, option.map $ (•) a⟩

@[simp] lemma coe_none (a : α) : a • (none : option β) = none := rfl
@[simp] lemma coe_some (a : α) (b : β) : a • some b = some (a • b) := rfl

end has_scalar

instance [monoid α] [mul_action α β] : mul_action α (option β) :=
{ smul := (•),
  one_smul := λ b, by { cases b, { refl }, { exact congr_arg some (one_smul _ _) } },
  mul_smul := λ a₁ a₂ b, by { cases b, { refl }, { exact congr_arg some (mul_smul _ _ _) } } }

end option
