import Mathlib.Data.Set.Lattice

open scoped symmDiff

/-!
# Order theoretic results
-/

open Function Set

variable {ι α β : Type _}

theorem csupr_neg [CompleteLattice α] {p : Prop} {f : p → α} (hp : ¬p) : (⨆ h, f h) = ⊥ :=
  iSup_eq_bot.2 fun h => (hp h).elim

namespace Set

variable (f : α → β) {s t : Set α}

@[simp]
theorem compl_eq_empty : sᶜ = ∅ ↔ s = univ :=
  compl_eq_bot

@[simp]
theorem compl_eq_univ : sᶜ = univ ↔ s = ∅ :=
  compl_eq_top

theorem image_sUnion (f : α → β) (S : Set (Set α)) : f '' ⋃₀ S = ⋃ s ∈ S, f '' s := by
  rw [sUnion_eq_biUnion, image_iUnion₂]

@[simp]
theorem iUnion_pos {p : Prop} {f : p → Set α} (hp : p) : (⋃ h, f h) = f hp :=
  iSup_pos hp

@[simp]
theorem iUnion_neg' {p : Prop} {f : p → Set α} (hp : ¬p) : (⋃ h, f h) = ∅ :=
  csupr_neg hp

variable (s)

@[simp]
theorem empty_symmDiff : ∅ ∆ s = s :=
  bot_symmDiff _

@[simp]
theorem symmDiff_empty : s ∆ ∅ = s :=
  symmDiff_bot _

end Set
