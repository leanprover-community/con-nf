import Mathlib.GroupTheory.GroupAction.Basic
import ConNF.Fuzz.Hypotheses

/-!
# Coding functions
-/

open MulAction Set Sum

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions] {β : Λ} [TangleData β]

/-- The "shell" of a tangle, reducing it just to the information that it used to come from
a tangle. -/
@[ext]
structure Shell (β : Λ) [TangleData β] : Type u where
  p : Pretangle β
  h : ∃ t : Tangle β, p = toPretangle t

namespace Shell

instance : MulAction (Allowable β) (Shell β) where
  smul ρ t := ⟨ρ • t.p, by
    obtain ⟨s, hs⟩ := t.h
    refine ⟨ρ • s, ?_⟩
    rw [hs]
    rw [toPretangle_smul]⟩
  one_smul := by
    rintro ⟨p, h⟩
    refine Shell.ext _ _ ?_
    change 1 • p = p
    rw [one_smul]
  mul_smul := by
    rintro ρ₁ ρ₂ ⟨p, h⟩
    refine Shell.ext _ _ ?_
    change (ρ₁ * ρ₂) • p = ρ₁ • ρ₂ • p
    rw [mul_smul]

@[simp]
theorem smul_p (ρ : Allowable β) (t : Shell β) :
    (ρ • t).p = ρ • t.p :=
  rfl

def ofTangle (t : Tangle β) : Shell β :=
  ⟨toPretangle t, t, rfl⟩

theorem exists_eq_ofTangle (s : Shell β) :
    ∃ t : Tangle β, s = ofTangle t := by
  obtain ⟨p, t, rfl⟩ := s
  exact ⟨t, rfl⟩

@[simp]
theorem ofTangle_p (t : Tangle β) :
    (ofTangle t).p = toPretangle t :=
  rfl

theorem smul_ofTangle (ρ : Allowable β) (t : Tangle β) :
    ρ • ofTangle t = ofTangle (ρ • t) := by
  refine Shell.ext _ _ ?_
  simp only [smul_p, ofTangle_p]
  rw [toPretangle_smul]

end Shell

end ConNF
