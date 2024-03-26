import Mathlib.GroupTheory.GroupAction.Basic
import ConNF.Counting.Hypotheses

/-!
# Coding functions
-/

open MulAction Set Sum

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions] [CountingAssumptions] {β : Λ} [LeLevel β]

namespace Shell

protected theorem eq_toPretangle_of_mem (β : Λ) [LeLevel β] (γ : Λ) [LeLevel γ]
    (h : (γ : TypeIndex) < β) (t₁ : Shell β) (t₂ : Pretangle γ) :
    t₂ ∈ Pretangle.ofCoe t₁.p γ h → ∃ t₂' : Shell γ, t₂ = t₂'.p := by
  intro ht
  obtain ⟨t₁, rfl⟩ := t₁.exists_eq_ofTangle
  obtain ⟨t₂', ht₂'⟩ := eq_toPretangle_of_mem β γ h t₁ t₂ ht
  exact ⟨ofTangle t₂', ht₂'⟩

theorem ofTangle_eq_iff (t₁ t₂ : Tangle β) :
    toPretangle t₁ = toPretangle t₂ ↔ ofTangle t₁ = ofTangle t₂ := by
  constructor
  · intro h
    ext
    exact h
  · intro h
    exact congr_arg Shell.p h

protected theorem toPretangle_ext (β γ : Λ) [LeLevel β] [LeLevel γ] (h : (γ : TypeIndex) < β)
    (t₁ t₂ : Shell β) :
    (∀ t : Pretangle γ,
      t ∈ Pretangle.ofCoe t₁.p γ h ↔ t ∈ Pretangle.ofCoe t₂.p γ h) →
    t₁ = t₂ := by
  intro ht
  obtain ⟨t₁, rfl⟩ := t₁.exists_eq_ofTangle
  obtain ⟨t₂, rfl⟩ := t₂.exists_eq_ofTangle
  exact Shell.ext _ _ (toPretangle_ext β γ h t₁ t₂ ht)

def Orbit (β : Λ) [LeLevel β] : Type u :=
  MulAction.orbitRel.Quotient (Allowable β) (Shell β)

def Orbit.mk (s : Shell β) : Orbit β :=
  ⟦s⟧

protected theorem Orbit.eq {s₁ s₂ : Shell β} :
    mk s₁ = mk s₂ ↔ s₁ ∈ MulAction.orbit (Allowable β) s₂ :=
  Quotient.eq (r := _)

theorem Orbit.mk_smul (s : Shell β) (ρ : Allowable β) : Orbit.mk (ρ • s) = Orbit.mk s := by
  rw [Orbit.eq]
  exact ⟨ρ, rfl⟩

theorem Orbit.has_repr (o : Orbit β) :
    ∃ t : Tangle β, o = Orbit.mk (ofTangle t) := by
  refine Quotient.inductionOn o ?_
  intro s
  refine ⟨s.h.choose, ?_⟩
  erw [Orbit.eq]
  refine ⟨1, ?_⟩
  refine Shell.ext _ _ ?_
  simp only [one_smul]
  exact s.h.choose_spec.symm

noncomputable def Orbit.repr (o : Orbit β) : Tangle β :=
  o.has_repr.choose

theorem Orbit.repr_spec (o : Orbit β) :
    o = Orbit.mk (ofTangle o.repr) :=
  o.has_repr.choose_spec

theorem has_twist (s : Shell β) :
    ∃ ρ : Allowable β, ρ • ofTangle (Orbit.mk s).repr = s := by
  have := Orbit.repr_spec (Orbit.mk s)
  rw [Orbit.eq] at this
  exact this

/-- An allowable permutation that turns the representing tangle into `s`. -/
noncomputable def twist (s : Shell β) : Allowable β :=
  s.has_twist.choose

theorem eq_twist_smul (s : Shell β) :
    s.twist • ofTangle (Orbit.mk s).repr = s :=
  s.has_twist.choose_spec

theorem twist_smul (s : Shell β) (ρ : Allowable β) :
    ρ • s = (ρ • s).twist • s.twist⁻¹ • s := by
  have := eq_twist_smul s
  rw [smul_eq_iff_eq_inv_smul] at this
  rw [← this]
  have := eq_twist_smul (ρ • s)
  rw [Orbit.mk_smul] at this
  exact this.symm

/-- A canonical tangle chosen for this shell. -/
noncomputable def out (s : Shell β) : Tangle β :=
  s.twist • (Orbit.mk s).repr

theorem eq_ofTangle_out (s : Shell β) : s = ofTangle s.out := by
  rw [out, ← smul_ofTangle, eq_twist_smul]

theorem out_injective (s₁ s₂ : Shell β) (h : s₁.out = s₂.out) : s₁ = s₂ := by
  rw [eq_ofTangle_out s₁, eq_ofTangle_out s₂, h]

@[simp]
theorem out_toPretangle (s : Shell β) : toPretangle s.out = s.p := by
  conv_rhs => rw [eq_ofTangle_out s]

noncomputable def support (s : Shell β) : Support β :=
  s.twist • (Orbit.mk s).repr.support

protected theorem support_supports (s : Shell β) :
    MulAction.Supports (Allowable β) (s.support : Set (Address β)) s := by
  intro ρ hρ
  have := support_supports (Orbit.mk s).repr (s.twist⁻¹ * ρ * s.twist) ?_
  · rw [mul_smul, mul_smul, inv_smul_eq_iff] at this
    have := congr_arg ofTangle this
    erw [← smul_ofTangle, ← eq_ofTangle_out s] at this
    exact this
  · intro a ha
    rw [mul_smul, mul_smul, inv_smul_eq_iff]
    refine hρ (a := s.twist • a) ?_
    rw [support]
    simp only [Enumeration.smul_carrier, smul_mem_smul_set_iff]
    exact ha

theorem smul_support_max (s : Shell β) (ρ : Allowable β) :
    (ρ • s).support.max = s.support.max := by
  rw [support, support, Orbit.mk_smul, Enumeration.smul_max, Enumeration.smul_max]

@[simp]
theorem smul_support (s : Shell β) (ρ : Allowable β) :
    (ρ • s).support = (ρ • s).twist • s.twist⁻¹ • s.support := by
  rw [support, support, inv_smul_smul, Orbit.mk_smul]

protected noncomputable def singleton
    (β : Λ) [LeLevel β] (γ : Λ) [LeLevel γ] (h : (γ : TypeIndex) < β)
    (t : Shell γ) : Shell β :=
    ofTangle (singleton β γ h t.out)

protected theorem singleton_toPretangle
    (β : Λ) [LeLevel β] (γ : Λ) [LeLevel γ] (h : (γ : TypeIndex) < β) (t : Shell γ) :
    Pretangle.ofCoe (Shell.singleton β γ h t).p γ h = {t.p} := by
  refine (singleton_toPretangle β γ h t.out).trans ?_
  rw [out_toPretangle]

protected theorem singleton_smul
    (β : Λ) [LeLevel β] (γ : Λ) [LeLevel γ] (h : (γ : TypeIndex) < β)
    (t : Shell γ) (ρ : Allowable β) :
    ρ • Shell.singleton β γ h t =
      Shell.singleton β γ h (Allowable.comp (Quiver.Hom.toPath h) ρ • t) := by
  refine Shell.toPretangle_ext β γ h _ _ ?_
  intro s
  simp only [Shell.singleton, smul_ofTangle, singleton_smul, ofTangle_p, singleton_toPretangle,
    toPretangle_smul, out_toPretangle, mem_singleton_iff, smul_p]

protected theorem singleton_injective
    (β : Λ) [LeLevel β] (γ : Λ) [LeLevel γ] (h : (γ : TypeIndex) < β) :
    Function.Injective (Shell.singleton β γ h) := by
  intro s₁ s₂ hs
  have h₁ := Shell.singleton_toPretangle β γ h s₁
  have h₂ := Shell.singleton_toPretangle β γ h s₂
  rw [hs, h₂, singleton_eq_singleton_iff] at h₁
  exact Shell.ext _ _ h₁.symm

end Shell

end ConNF
