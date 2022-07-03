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
