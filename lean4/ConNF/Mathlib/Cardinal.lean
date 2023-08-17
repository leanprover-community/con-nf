import Project.Mathlib.Order
import Mathbin.SetTheory.Cardinal.Basic

#align_import mathlib.cardinal

open Set

open scoped Cardinal

universe u

variable {ι α : Type u} {s : Set α}

namespace Cardinal

theorem mk_bUnion_le' (s : Set ι) (f : ∀ i ∈ s, Set α) :
    (#⋃ (i) (hi : i ∈ s), f i hi) ≤ (#s) * ⨆ i : s, #f i.1 i.2 := by rw [bUnion_eq_Union];
  apply mk_Union_le

theorem nonempty_compl_of_mk_lt_mk (h : (#s) < (#α)) : sᶜ.Nonempty :=
  by
  simp_rw [Set.nonempty_iff_ne_empty, Ne.def, compl_eq_empty]
  rintro rfl
  simpa using h

end Cardinal

