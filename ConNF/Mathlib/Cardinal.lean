import ConNF.Mathlib.Order
import Mathlib.SetTheory.Cardinal.Basic

open Set

open scoped Cardinal

universe u

variable {ι α : Type u} {s : Set α}

namespace Cardinal

theorem mk_bUnion_le' (s : Set ι) (f : ∀ i ∈ s, Set α) :
    (#(⋃ (i) (hi : i ∈ s), f i hi)) ≤ (#s) * ⨆ i : s, #(f i.1 i.2) := by
  rw [biUnion_eq_iUnion]
  apply mk_iUnion_le

theorem nonempty_compl_of_mk_lt_mk (h : (#s) < (#α)) : sᶜ.Nonempty := by
  simp_rw [Set.nonempty_iff_ne_empty, ne_eq, compl_eq_empty]
  rintro rfl
  simp at h

end Cardinal
