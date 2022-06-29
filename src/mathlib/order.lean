import data.set.basic
import order.symm_diff

/-!
# Order theoretic results
-/

namespace set
variables {α β : Type*} (f : α → β) (s t : set α)

lemma subset_image_symm_diff : (f '' s) ∆ (f '' t) ⊆ f '' s ∆ t :=
(union_subset_union (subset_image_diff _ _ _) $ subset_image_diff _ _ _).trans
  (image_union _ _ _).superset

variables {s}

@[simp] lemma compl_eq_empty : sᶜ = ∅ ↔ s = univ := compl_eq_bot
@[simp] lemma compl_eq_univ : sᶜ = univ ↔ s = ∅ := compl_eq_top

end set
