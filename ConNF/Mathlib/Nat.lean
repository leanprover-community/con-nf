import Mathlib.Data.Nat.Parity

namespace Nat

variable {n : ℕ}

@[parity_simps]
theorem odd_succ : Odd (succ n) ↔ ¬Odd n := by rw [succ_eq_add_one, odd_add]; simp [not_even_one]

theorem not_even : ¬Even n ↔ Odd n :=
  Nat.odd_iff_not_even.symm

theorem not_odd : ¬Odd n ↔ Even n :=
  Nat.even_iff_not_odd.symm

end Nat
