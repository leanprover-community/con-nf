import data.set.basic
import order.symm_diff

/-!
# Order theoretic results
-/

open function

variables {α β : Type*}

section generalized_boolean_algebra
variables [generalized_boolean_algebra α] (a b c : α)

-- True in co-Heyting algebras
lemma sdiff_triangle : a \ c ≤ a \ b ⊔ b \ c :=
begin
  rw [sdiff_le_iff, sup_left_comm, ←sdiff_le_iff],
  exact sdiff_sdiff_le.trans (sdiff_le_iff.1 le_rfl),
end

lemma symm_diff_triangle : a ∆ c ≤ a ∆ b ⊔ b ∆ c :=
begin
  refine (sup_le_sup (sdiff_triangle a b c) $ sdiff_triangle _ b _).trans_eq _,
  rw [@sup_comm _ _ (c \ b), sup_sup_sup_comm],
  refl,
end

variables {a b c}

@[simp] lemma le_symm_diff_iff_left : a ≤ a ∆ b ↔ disjoint a b :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw symm_diff_eq_sup_sdiff_inf at h,
    exact (le_sdiff_iff.1 $ inf_le_of_left_le h).le },
  { rw h.symm_diff_eq_sup,
    exact le_sup_left }
end

@[simp] lemma le_symm_diff_iff_right : b ≤ a ∆ b ↔ disjoint a b :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw symm_diff_eq_sup_sdiff_inf at h,
    exact (le_sdiff_iff.1 $ inf_le_of_right_le h).le },
  { rw h.symm_diff_eq_sup,
    exact le_sup_right }
end

end generalized_boolean_algebra

namespace set
variables (f : α → β) (s t : set α)

lemma subset_image_symm_diff : (f '' s) ∆ (f '' t) ⊆ f '' s ∆ t :=
(union_subset_union (subset_image_diff _ _ _) $ subset_image_diff _ _ _).trans
  (image_union _ _ _).superset

end set

namespace equiv
variables [generalized_boolean_algebra α]

/-- Symmetric difference by `a` as an equivalence. -/
protected def symm_diff (a : α) : α ≃ α :=
{ to_fun := (∆) a,
  inv_fun := λ b, b ∆ a,
  left_inv := symm_diff_symm_diff_self' _,
  right_inv := λ b, by rw [←symm_diff_assoc, symm_diff_symm_diff_self'] }

@[simp] lemma coe_symm_diff (a : α) : ⇑(equiv.symm_diff a) =  (∆) a := rfl
@[simp] lemma symm_diff_apply (a b : α) : equiv.symm_diff a b = a ∆ b := rfl
@[simp] lemma symm_diff_symm (a : α) : (equiv.symm_diff a).symm = equiv.symm_diff a :=
ext $ λ b, symm_diff_comm _ _

end equiv

section generalized_boolean_algebra
variables [generalized_boolean_algebra α]

lemma symm_diff_left_injective (a : α): injective ((∆) a) := (equiv.symm_diff a).injective
lemma symm_diff_right_injective (a : α): injective (∆ a) := (equiv.symm_diff a).symm.injective

end generalized_boolean_algebra
