import combinatorics.quiver.path
import data.list.basic
import logic.embedding

open function quiver quiver.path

namespace quiver.path
variables {V : Type*}

/-- We can convert a path between two points in a quiver into a list, giving the path we traversed.
The list contains `a` at its head, but not `b` a priori. -/
def to_list [quiver V] {a : V} : Π {b : V}, quiver.path a b → list V
| b nil := []
| b (@cons _ _ p q r A B) := q :: A.to_list

lemma to_list_injective [quiver.{0} V] (a : V) : ∀ b, injective (to_list : path a b → list V)
| b nil nil h := rfl
| b nil (@cons _ _ p q r A B) h := (list.cons_ne_nil _ _ h.symm).elim
| b (@cons _ _ p q r A B) nil h := (list.cons_ne_nil _ _ h).elim
| b (@cons _ _ p q r A B) (@cons _ _ s t u C D) h := begin
  simp only [to_list] at h,
  obtain ⟨q_eq_t, hAC⟩ := h,
  subst q_eq_t,
  simp only [eq_self_iff_true, heq_iff_eq, and_true, true_and],
  exact to_list_injective _ hAC,
end

/-- In quivers with morphisms in `Prop`, a path is uniquely determined by the list of points it
passes through, due to propositional irrelevance. -/
def to_list_embedding [quiver.{0} V] (a b : V) : quiver.path a b ↪ list V :=
⟨to_list, to_list_injective a b⟩

lemma eq_of_length_zero [quiver V] {a b : V} (p : path a b) (hzero : p.length = 0) : a = b :=
by { cases p, { refl }, { cases nat.succ_ne_zero _ hzero } }

end quiver.path
