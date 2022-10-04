import combinatorics.quiver.path
import data.list.basic
import mathlib.logic

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

@[simp] lemma length_comp (p : path a b) :
  ∀ {c} (q : path b c), (p.comp q).length = p.length + q.length
| c nil := rfl
| c (cons q h) := congr_arg nat.succ q.length_comp

lemma comp_inj {p₁ p₂ : path a b} {q₁ q₂ : path b c} (hq : q₁.length = q₂.length) :
  p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ :=
begin
  refine ⟨λ h, _, by { rintro ⟨rfl, rfl⟩, refl }⟩,
  induction q₁ with d₁ e₁ q₁ f₁ ih generalizing q₂; obtain _ | ⟨d₂, e₂, q₂, f₂⟩ := q₂,
  { exact ⟨h, rfl⟩ },
  { cases hq },
  { cases hq },
  simp only [comp_cons] at h,
  obtain rfl := h.1,
  obtain ⟨rfl, rfl⟩ := ih (nat.succ_injective hq) h.2.1.eq,
  rw h.2.2.eq,
  exact ⟨rfl, rfl⟩,
end

lemma comp_inj' {p₁ p₂ : path a b} {q₁ q₂ : path b c} (h : p₁.length = p₂.length) :
  p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ :=
⟨λ h_eq, (comp_inj $ add_left_injective p₁.length $
  by simpa [h] using congr_arg length h_eq).1 h_eq, by { rintro ⟨rfl, rfl⟩, refl }⟩

lemma comp_injective_left (q : path b c) : injective (λ p : path a b, p.comp q) :=
λ p₁ p₂ h, ((comp_inj rfl).1 h).1

lemma comp_injective_right (p : path a b) : injective (p.comp : path b c → path a c) :=
λ q₁ q₂ h, ((comp_inj' rfl).1 h).2

@[simp] lemma comp_inj_left {p₁ p₂ : path a b} {q : path b c} : p₁.comp q = p₂.comp q ↔ p₁ = p₂ :=
q.comp_injective_left.eq_iff

@[simp] lemma comp_inj_right {p : path a b} {q₁ q₂ : path b c} : p.comp q₁ = p.comp q₂ ↔ q₁ = q₂ :=
p.comp_injective_right.eq_iff

@[simp] lemma to_list_comp (p : path a b) :
  ∀ {c : V} (q : path b c), (p.comp q).to_list = q.to_list ++ p.to_list
| c nil := rfl
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
