import combinatorics.quiver.path

universe u

lemma quiver.path.eq_of_length_zero {V : Type u} [quiver V] {a b : V} (p : quiver.path a b)
(hzero: p.length = 0) : a = b :=
begin
  induction p,
  { refl },
  { exfalso, simp at hzero, exact nat.add_one_ne_zero _ hzero }
end
