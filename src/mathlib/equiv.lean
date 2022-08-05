import group_theory.perm.basic

open equiv

variables {α β γ : Type*}

namespace equiv

@[simp] lemma symm_trans (f : α ≃ β) (g : β ≃ γ) : (f.trans g).symm = (g.symm).trans f.symm := rfl

namespace perm

@[simp] lemma preimage_inv (f : perm α) (s : set α) : ⇑f⁻¹ ⁻¹' s = f '' s :=
(f.image_eq_preimage _).symm

@[simp] lemma image_inv (f : perm α) (s : set α) : ⇑f⁻¹ '' s = f ⁻¹' s :=
equiv.image_eq_preimage _ _

end perm
end equiv
