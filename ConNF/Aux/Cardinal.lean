import Mathlib.SetTheory.Cardinal.Cofinality

universe u v

namespace Cardinal

theorem lift_isRegular (c : Cardinal.{u}) (h : IsRegular c) : IsRegular (lift.{v} c) := by
  constructor
  · rw [← lift_aleph0.{v, u}, lift_le]
    exact h.1
  · rw [← lift_ord, ← Ordinal.lift_cof, lift_le]
    exact h.2

theorem le_of_le_add {c d e : Cardinal.{u}} (h : c ≤ d + e) (hc : ℵ₀ ≤ c) (he : e < c) : c ≤ d := by
  by_contra! h'
  exact (add_lt_of_lt hc h' he).not_le h

theorem mk_ne_zero_iff_nonempty {α : Type _} (s : Set α) :
    #s ≠ 0 ↔ s.Nonempty := by
  rw [mk_ne_zero_iff]
  exact Set.nonempty_coe_sort

end Cardinal
