import algebra.parity
import order.symm_diff

/-!
# Order theoretic results
-/

open function set

variables {ι α β : Type*}

namespace set
variables (f : α → β) (s t : set α)

lemma subset_image_symm_diff : (f '' s) ∆ (f '' t) ⊆ f '' s ∆ t :=
(union_subset_union (subset_image_diff _ _ _) $ subset_image_diff _ _ _).trans
  (image_union _ _ _).superset

variables {s}

@[simp] lemma compl_eq_empty : sᶜ = ∅ ↔ s = univ := compl_eq_bot
@[simp] lemma compl_eq_univ : sᶜ = univ ↔ s = ∅ := compl_eq_top

end set

section pairwise
variables {a b : α} {r : α → α → Prop}

protected lemma pairwise.eq (h : pairwise r) : ¬ r a b → a = b := not_imp_comm.1 $ h _ _

end pairwise

section
variables {f : ι → set α} {s t : set ι}

lemma pairwise.subset_of_bUnion_subset_bUnion (h₀ : pairwise (disjoint on f))
  (h₁ : ∀ i ∈ s, (f i).nonempty) (h : (⋃ i ∈ s, f i) ⊆ ⋃ i ∈ t, f i) :
  s ⊆ t :=
begin
  rintro i hi,
  obtain ⟨a, hai⟩ := h₁ i hi,
  obtain ⟨j, hj, haj⟩ := mem_Union₂.1 (h $ mem_Union₂_of_mem hi hai),
  rwa h₀.eq (not_disjoint_iff.2 ⟨a, hai, haj⟩),
end

lemma pairwise.bUnion_injective (h₀ : pairwise (disjoint on f)) (h₁ : ∀ i, (f i).nonempty) :
  injective (λ s : set ι, ⋃ i ∈ s, f i) :=
λ s t h, (h₀.subset_of_bUnion_subset_bUnion (λ _ _, h₁ _) $ h.subset).antisymm $
  h₀.subset_of_bUnion_subset_bUnion (λ _ _, h₁ _) $ h.superset

end
