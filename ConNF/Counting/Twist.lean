import Mathlib.GroupTheory.GroupAction.Basic
import ConNF.Counting.Hypotheses

/-!
# Coding functions
-/

open MulAction Set Sum

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions] [CountingAssumptions] {β : Λ} [LeLevel β]

namespace TangleData.TSet

def Orbit (β : Λ) [LeLevel β] : Type u :=
  MulAction.orbitRel.Quotient (Allowable β) (TSet β)

def Orbit.mk (s : TSet β) : Orbit β :=
  ⟦s⟧

protected theorem Orbit.eq {s₁ s₂ : TSet β} :
    mk s₁ = mk s₂ ↔ s₁ ∈ MulAction.orbit (Allowable β) s₂ :=
  Quotient.eq (r := _)

theorem Orbit.mk_smul (s : TSet β) (ρ : Allowable β) : Orbit.mk (ρ • s) = Orbit.mk s := by
  rw [Orbit.eq]
  exact ⟨ρ, rfl⟩

theorem Orbit.has_repr (o : Orbit β) :
    ∃ t : Tangle β, o = Orbit.mk t.set := by
  refine Quotient.inductionOn o ?_
  intro s
  obtain ⟨S, hS⟩ := s.has_support
  refine ⟨⟨s, S, hS⟩, ?_⟩
  erw [Orbit.eq]
  refine ⟨1, ?_⟩
  simp only [one_smul]
  rfl

noncomputable def Orbit.repr (o : Orbit β) : Tangle β :=
  o.has_repr.choose

theorem Orbit.repr_spec (o : Orbit β) :
    o = Orbit.mk o.repr.set :=
  o.has_repr.choose_spec

theorem has_twist (s : TSet β) :
    ∃ ρ : Allowable β, ρ • (Orbit.mk s).repr.set = s := by
  have := Orbit.repr_spec (Orbit.mk s)
  rw [Orbit.eq] at this
  exact this

/-- An allowable permutation that turns the representing tangle into `s`. -/
noncomputable def twist (s : TSet β) : Allowable β :=
  s.has_twist.choose

theorem eq_twist_smul (s : TSet β) :
    s.twist • (Orbit.mk s).repr.set = s :=
  s.has_twist.choose_spec

theorem twist_smul (s : TSet β) (ρ : Allowable β) :
    ρ • s = (ρ • s).twist • s.twist⁻¹ • s := by
  have := eq_twist_smul s
  rw [smul_eq_iff_eq_inv_smul] at this
  rw [← this]
  have := eq_twist_smul (ρ • s)
  rw [Orbit.mk_smul] at this
  exact this.symm

/-- A canonical tangle chosen for this TSet. -/
noncomputable def out (s : TSet β) : Tangle β :=
  s.twist • (Orbit.mk s).repr

theorem eq_set_out (s : TSet β) : s = s.out.set := by
  rw [out, Tangle.smul_set, eq_twist_smul]

theorem out_injective (s₁ s₂ : TSet β) (h : s₁.out = s₂.out) : s₁ = s₂ := by
  rw [eq_set_out s₁, eq_set_out s₂, h]

noncomputable def support (s : TSet β) : Support β :=
  s.twist • (Orbit.mk s).repr.support

protected theorem support_supports (s : TSet β) :
    MulAction.Supports (Allowable β) (s.support : Set (Address β)) s := by
  intro ρ hρ
  have := support_supports (Orbit.mk s).repr (s.twist⁻¹ * ρ * s.twist) ?_
  · rw [mul_smul, mul_smul, inv_smul_eq_iff] at this
    have := congr_arg Tangle.set this
    erw [Tangle.smul_set, ← eq_set_out s] at this
    exact this
  · intro a ha
    rw [mul_smul, mul_smul, inv_smul_eq_iff]
    refine hρ (a := s.twist • a) ?_
    rw [support]
    simp only [Enumeration.smul_carrier, smul_mem_smul_set_iff]
    exact ha

theorem smul_support_max (s : TSet β) (ρ : Allowable β) :
    (ρ • s).support.max = s.support.max := by
  rw [support, support, Orbit.mk_smul, Enumeration.smul_max, Enumeration.smul_max]

@[simp]
theorem smul_support (s : TSet β) (ρ : Allowable β) :
    (ρ • s).support = (ρ • s).twist • s.twist⁻¹ • s.support := by
  rw [support, support, inv_smul_smul, Orbit.mk_smul]

end TangleData.TSet

end ConNF
