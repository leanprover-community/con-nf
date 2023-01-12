import group_theory.perm.basic

variables {α β γ : Type*}

namespace equiv

@[simp] lemma symm_trans (f : α ≃ β) (g : β ≃ γ) : (f.trans g).symm = (g.symm).trans f.symm := rfl

end equiv
