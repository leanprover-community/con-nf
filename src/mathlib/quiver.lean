import combinatorics.quiver.path
import logic.embedding

universe u

open quiver quiver.path

namespace quiver.path

/-- We can convert a path between two points in a quiver into a list, giving the path we traversed.
The list contains `a` at its head, but not `b` a priori. -/
def to_list {V : Type*} [quiver V] {a : V} : Π {b : V}, quiver.path a b → list V
| b (@cons _ _ p q r A B) := q :: A.to_list
| b nil := []

lemma to_list_injective_core {V : Type*} [quiver.{0} V] {a : V} :
Π {b : V} (p q : quiver.path a b), p.to_list = q.to_list → p = q
| b (@cons _ _ p q r A B) (@cons _ _ s t u C D) h := begin
  unfold quiver.path.to_list at h, simp at h,
  obtain ⟨q_eq_t, hAC⟩ := h,
  subst q_eq_t, simp,
  exact to_list_injective_core _ _ hAC
end
| b (@cons _ _ p q r A B) nil h :=
  by { exfalso, unfold quiver.path.to_list at h, simp at h, exact h }
| b nil (@cons _ _ p q r A B) h :=
  by { exfalso, unfold quiver.path.to_list at h, simp at h, exact h }
| b nil nil h := rfl

lemma to_list_injective {V : Type*} [quiver.{0} V] (a b : V) :
function.injective $ @quiver.path.to_list V _ a b := quiver.path.to_list_injective_core

/-- In quivers with morphisms in `Prop`, a path is uniquely determined by the list of points it
passes through, due to propositional irrelevance. -/
def to_list_embedding {V : Type*} [quiver.{0} V] (a b : V) :
quiver.path a b ↪ list V := ⟨quiver.path.to_list, quiver.path.to_list_injective a b⟩

lemma eq_of_length_zero {V : Type u} [quiver V] {a b : V} (p : quiver.path a b)
(hzero: p.length = 0) : a = b :=
begin
  induction p,
  { refl },
  { exfalso, simp at hzero, exact nat.add_one_ne_zero _ hzero }
end

end quiver.path
