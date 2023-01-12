import data.set.lattice

/-!
# Order theoretic results
-/

open function set

variables {ι α β : Type*}

lemma csupr_neg [complete_lattice α] {p : Prop} {f : p → α} (hp : ¬ p) : (⨆ h, f h) = ⊥ :=
supr_eq_bot.2 $ λ h, (hp h).elim

namespace set
variables (f : α → β) {s t : set α}

@[simp] lemma compl_eq_empty : sᶜ = ∅ ↔ s = univ := compl_eq_bot
@[simp] lemma compl_eq_univ : sᶜ = univ ↔ s = ∅ := compl_eq_top

lemma image_sUnion (f : α → β) (S : set (set α)) : f '' ⋃₀ S = ⋃ s ∈ S, f '' s :=
by rw [sUnion_eq_bUnion, image_Union₂]

--TODO: Rename `Union_neg` to `neg_Union`
@[simp] lemma Union_pos {p : Prop} {f : p → set α} (hp : p) : (⋃ h, f h) = f hp := supr_pos hp
@[simp] lemma Union_neg' {p : Prop} {f : p → set α} (hp : ¬ p) : (⋃ h, f h) = ∅ := csupr_neg hp

variables (s)

@[simp] lemma empty_symm_diff : ∅ ∆ s = s := bot_symm_diff _
@[simp] lemma symm_diff_empty : s ∆ ∅ = s := symm_diff_bot _

end set
