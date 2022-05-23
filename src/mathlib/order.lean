import data.set.basic
import order.symm_diff

/-!
# Order theoretic results
-/

variables {α β : Type*}

section boolean_algebra
variables [boolean_algebra α] (a b c : α)

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

end boolean_algebra

namespace set
variables (f : α → β) (s t : set α)

lemma subset_image_symm_diff : (f '' s) ∆ (f '' t) ⊆ f '' s ∆ t :=
(union_subset_union (subset_image_diff _ _ _) $ subset_image_diff _ _ _).trans
  (image_union _ _ _).superset

end set
