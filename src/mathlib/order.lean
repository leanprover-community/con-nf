import algebra.parity
import order.symm_diff
import order.zorn

/-!
# Order theoretic results
-/

open function set

variables {ι α β : Type*}

lemma csupr_neg [complete_lattice α] {p : Prop} {f : p → α} (hp : ¬ p) : (⨆ h, f h) = ⊥ :=
supr_eq_bot.2 $ λ h, (hp h).elim

namespace set
variables (f : α → β) (s t : set α)

lemma subset_image_symm_diff : (f '' s) ∆ (f '' t) ⊆ f '' s ∆ t :=
(union_subset_union (subset_image_diff _ _ _) $ subset_image_diff _ _ _).trans
  (image_union _ _ _).superset

variables {s t}

@[simp] lemma compl_eq_empty : sᶜ = ∅ ↔ s = univ := compl_eq_bot
@[simp] lemma compl_eq_univ : sᶜ = univ ↔ s = ∅ := compl_eq_top

@[simp] lemma symm_diff_nonempty : (s ∆ t).nonempty ↔ s ≠ t :=
ne_empty_iff_nonempty.symm.trans symm_diff_eq_bot.not

lemma image_sUnion (f : α → β) (S : set (set α)) : f '' ⋃₀ S = ⋃ s ∈ S, f '' s :=
by rw [sUnion_eq_bUnion, image_Union₂]

--TODO: Rename `Union_neg` to `neg_Union`
@[simp] lemma Union_pos {p : Prop} {f : p → set α} (hp : p) : (⋃ h, f h) = f hp := supr_pos hp
@[simp] lemma Union_neg' {p : Prop} {f : p → set α} (hp : ¬ p) : (⋃ h, f h) = ∅ := csupr_neg hp

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

section
variables [boolean_algebra α] {a b c : α}

lemma disjoint.le_symm_diff_sup_symm_diff_left (h : disjoint a b) : c ≤ a ∆ c ⊔ b ∆ c :=
begin
  transitivity c \ (a ⊓ b),
  { rw [h.eq_bot, sdiff_bot] },
  { rw sdiff_inf,
    exact sup_le_sup le_sup_right le_sup_right }
end

lemma disjoint.le_symm_diff_sup_symm_diff_right (h : disjoint b c) : a ≤ a ∆ b ⊔ a ∆ c :=
by { simp_rw symm_diff_comm a, exact h.le_symm_diff_sup_symm_diff_left }

end

namespace set
variables {s t u : set α}

lemma subset_symm_diff_union_symm_diff_left (h : disjoint s t) : u ≤ s ∆ u ⊔ t ∆ u :=
h.le_symm_diff_sup_symm_diff_left

lemma subset_symm_diff_union_symm_diff_right (h : disjoint t u) : s ≤ s ∆ t ⊔ s ∆ u :=
h.le_symm_diff_sup_symm_diff_right

variables (s)

@[simp] lemma empty_symm_diff : ∅ ∆ s = s := bot_symm_diff _
@[simp] lemma symm_diff_empty : s ∆ ∅ = s := symm_diff_bot _

end set

section
variables [preorder α]

open set

theorem zorn_Ici₀ (a : α)
  (ih : ∀ c ⊆ Ici a, is_chain (≤) c → ∀ y ∈ c, ∃ ub, a ≤ ub ∧ ∀ z ∈ c, z ≤ ub) (x : α)
  (hax : a ≤ x) :
  ∃ m, x ≤ m ∧ ∀ z, m ≤ z → z ≤ m :=
begin
  obtain ⟨m, hma, hxm, hm⟩ := zorn_nonempty_preorder₀ (Ici a) (by simpa using ih) x hax,
  exact ⟨m, hxm, λ z hmz, hm _ (hax.trans $ hxm.trans hmz) hmz⟩,
end

end
