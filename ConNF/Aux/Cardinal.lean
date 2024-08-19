import Mathlib.SetTheory.Cardinal.Cofinality

universe u v

namespace Cardinal

theorem lift_isRegular (c : Cardinal.{u}) (h : IsRegular c) : IsRegular (lift.{v} c) := by
  constructor
  · rw [← lift_aleph0.{v, u}, lift_le]
    exact h.1
  · rw [← lift_ord, ← Ordinal.lift_cof, lift_le]
    exact h.2

end Cardinal
