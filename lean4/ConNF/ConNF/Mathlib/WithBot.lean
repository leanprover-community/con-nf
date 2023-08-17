import Mathlib.Order.WithBot

open Function

namespace WithBot

variable {α : Type _} {C : WithBot α → Sort _} (h₁ : C ⊥) (h₂ : ∀ a : α, C ↑a)

theorem coe_ne_coe {a b : α} : (a : WithBot α) ≠ b ↔ a ≠ b :=
  coe_eq_coe.not

instance [LT α] [IsWellOrder α (· < ·)] : IsStrictTotalOrder (WithBot α) (· < ·) := by
  classical
  letI : LinearOrder α := linearOrderOfSTO (· < ·)
  infer_instance

instance [Preorder α] [IsWellOrder α (· < ·)] : IsWellOrder (WithBot α) (· < ·) where

end WithBot
