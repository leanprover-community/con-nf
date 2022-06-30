import algebra.parity
import data.set.lattice
import order.symm_diff

/-!
# Order theoretic results
-/

variables {α β : Type*}

namespace set
variables (f : α → β) (s t : set α)

lemma subset_image_symm_diff : (f '' s) ∆ (f '' t) ⊆ f '' s ∆ t :=
(union_subset_union (subset_image_diff _ _ _) $ subset_image_diff _ _ _).trans
  (image_union _ _ _).superset

variables {s}

@[simp] lemma compl_eq_empty : sᶜ = ∅ ↔ s = univ := compl_eq_bot
@[simp] lemma compl_eq_univ : sᶜ = univ ↔ s = ∅ := compl_eq_top

lemma exists_inter_of_Union_eq_Union {s t : set α} {f : α → set β}
  (h : (⋃ b ∈ s, f b) = ⋃ c ∈ t, f c) :
  ∀ b ∈ s, (f b).nonempty → ∃ c ∈ t, (f b ∩ f c).nonempty :=
begin
  rintros b hb ⟨x, hx⟩,
  have : x ∈ ⋃ c ∈ t, f c := (subset_Union₂ b hb).trans h.subset hx,
  rw mem_Union₂ at this,
  exact Exists₂.imp (λ c _ hc, ⟨x, hx, hc⟩) this,
end

end set

section canonically_ordered_comm_semiring
variables [canonically_ordered_comm_semiring α] [covariant_class α α (+) (<)] [nontrivial α] {a : α}

lemma odd.pos : odd a → 0 < a :=
by { rintro ⟨a, rfl⟩,
  exact add_pos_of_nonneg_of_pos (zero_le _) ((zero_le _).lt_of_ne zero_ne_one) }

end canonically_ordered_comm_semiring
