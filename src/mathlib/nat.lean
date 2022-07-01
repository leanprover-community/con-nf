import data.nat.parity

namespace nat
variables {n : ℕ}

@[parity_simps] lemma odd_succ : odd (succ n) ↔ ¬ odd n :=
by rw [succ_eq_add_one, odd_add]; simp [not_even_one]

lemma not_odd : ¬ odd n ↔ even n := nat.even_iff_not_odd.symm

end nat
