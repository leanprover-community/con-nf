import combinatorics.quiver.path
import data.list.basic
import mathlib.logic

open function quiver

namespace quiver.path
variables {V : Type*} [quiver V] {a b c : V}

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

end quiver.path
