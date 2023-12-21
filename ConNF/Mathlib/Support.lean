import Mathlib.GroupTheory.GroupAction.Support

open Pointwise

variable {G H α β : Type*}

namespace MulAction

variable [Group G] [MulAction G α] [MulAction G β] {s t : Set α} {b : β}

@[to_additive]
theorem Supports.smul' (g : G) (h : Supports G s b) : Supports G (g • s) (g • b) := by
  rintro g' hg'
  have := h (g⁻¹ * g' * g) ?_
  · rw [mul_smul, mul_smul, inv_smul_eq_iff] at this
    exact this
  · rintro a ha
    rw [mul_smul, mul_smul, inv_smul_eq_iff]
    exact Set.ball_image_iff.1 hg' a ha

end MulAction
