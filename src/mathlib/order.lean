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
