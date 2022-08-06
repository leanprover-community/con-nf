import combinatorics.quiver.path
import data.list.basic

open function quiver quiver.path

namespace quiver.path
variables {V : Type*}

section sort
variables [quiver V] {a b c : V}

/-- We can convert a path between two points in a quiver into a list, giving the path we traversed.
The list contains `a` at its head, but not `b` a priori. -/
@[simp] def to_list : Π {b : V}, path a b → list V
| b nil := []
| b (@cons _ _ _ c _ p f) := c :: p.to_list

lemma eq_of_length_zero (p : path a b) (hzero : p.length = 0) : a = b :=
by { cases p, { refl }, { cases nat.succ_ne_zero _ hzero } }

@[simp] lemma length_distrib (p1 : path a b) (p2 : path b c) :
(p1.comp p2).length = p1.length + p2.length := begin
induction p2, simp only [comp_nil, length_nil, add_zero],
simp only [comp_cons, length_cons], rw p2_ih, refl,
end

lemma comp_inj (p1 p2 : path a b) (q1 q2 : path b c) (h : q1.length = q2.length) (h_eq : p1.comp q1 = p2.comp q2) : p1 = p2 ∧ q1 = q2 := begin
intros,
refine @nat.le_induction (λ l, ∀ (a b c : V) (p1 p2 : path a b) (q1 q2 : path b c) (h : q1.length = q2.length) (h2 : q1.length = l)  (h_eq : p1.comp q1 = p2.comp q2), p1 = p2 ∧ q1 = q2) 0 _ _ (q1.length) (nat.zero_le q1.length) _ _ _ p1 p2 q1 q2 h (eq.refl _) h_eq,
intros,
cases q1_1,cases q2_1,
simp only [comp_nil] at h_eq_1, rw h_eq_1, simp only [eq_self_iff_true, and_self],
dsimp [(length)] at h_1, have := eq.symm h_1, exfalso, simp only [nat.succ_ne_zero] at this, exact this,
dsimp [(length)] at h2, exfalso, simp only [nat.succ_ne_zero] at h2, exact h2,
intros,
cases q1_1, cases q2_1,
simp only [comp_nil] at h_eq_1, rw h_eq_1, simp only [eq_self_iff_true, and_self],
simp only [length_nil, length_cons] at h_1, have := eq.symm h_1, exfalso, simp only [nat.succ_ne_zero] at this, exact this,
cases q2_1,
simp only [length_nil, length_cons] at h_1,exfalso, simp only [nat.succ_ne_zero] at h_1, exact h_1,
simp only [comp_cons] at h_eq_1,
have := h_eq_1.left, subst this,
simp only [(heq_iff_eq)] at h_eq_1,
have := h_eq_1.right.right, subst this,
simp only [length_cons, add_left_inj] at h_1,
simp only [length_cons, add_left_inj] at h2,
have := ᾰ_1 a_1 b_1 q1_1_b p1_1 p2_1 q1_1_ᾰ q2_1_ᾰ h_1 h2 h_eq_1.right.left,
rw this.left, rw this.right, simp only [eq_self_iff_true, heq_iff_eq, and_self],
end

@[simp] lemma to_list_comp (p : path a b) :
  ∀ {c : V} (q : path b c), (p.comp q).to_list = q.to_list ++ p.to_list
| c nil := by simp
| c (@cons _ _ _ d _ q f) := by simp [to_list_comp]

end sort

section prop
variables [quiver.{0} V] (a b : V)

lemma to_list_injective (a : V) : ∀ b, injective (to_list : path a b → list V)
| b nil nil h := rfl
| b nil (@cons _ _ _ c _ p f) h := (list.cons_ne_nil _ _ h.symm).elim
| b (@cons _ _ _ c _ p f) nil h := (list.cons_ne_nil _ _ h).elim
| b (@cons _ _ _ c _ p f) (@cons _ _ s t u C D) h := begin
  simp only [to_list] at h,
  obtain ⟨rfl, hAC⟩ := h,
  simp only [eq_self_iff_true, heq_iff_eq, and_true, true_and],
  exact to_list_injective _ hAC,
end

/-- In quivers with morphisms in `Prop`, a path is uniquely determined by the list of points it
passes through, due to propositional irrelevance. -/
def to_list_embedding : path a b ↪ list V := ⟨to_list, to_list_injective a b⟩

end prop
end quiver.path
