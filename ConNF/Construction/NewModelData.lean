import ConNF.Construction.Code

/-!
# Construction of model data

In this file, we construct model data at type `α`, given that it is defined at all types below `α`.

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal
open scoped Pointwise

namespace ConNF

variable [Params.{u}] [Level] [LtData]

@[ext]
structure NewPerm : Type u where
  sderiv : (β : TypeIndex) → [LtLevel β] → AllPerm β
  smul_fuzz {β : TypeIndex} {γ : Λ} [LtLevel β] [LtLevel γ] (hβγ : β ≠ γ) (t : Tangle β) :
    (sderiv γ)ᵁ ↘. • fuzz hβγ t = fuzz hβγ (sderiv β • t)

instance : Mul NewPerm where
  mul ρ₁ ρ₂ := ⟨λ β _ ↦ ρ₁.sderiv β * ρ₂.sderiv β, by
    intro β γ _ _ hβγ t
    simp only [allPermForget_mul, mul_smul, Tree.mul_sderivBot, NewPerm.smul_fuzz]⟩

instance : One NewPerm where
  one := ⟨λ _ _ ↦ 1, by
    intro β γ _ _ hβγ t
    simp only [allPermForget_one, one_smul, Tree.one_sderivBot]⟩

instance : Inv NewPerm where
  inv ρ := ⟨λ β _ ↦ (ρ.sderiv β)⁻¹, by
    intro β γ _ _ hβγ t
    simp only [allPermForget_inv, Tree.inv_sderivBot, inv_smul_eq_iff, NewPerm.smul_fuzz,
      smul_inv_smul]⟩

@[simp]
theorem mul_sderiv (ρ₁ ρ₂ : NewPerm) (β : TypeIndex) [LtLevel β] :
    (ρ₁ * ρ₂).sderiv β = ρ₁.sderiv β * ρ₂.sderiv β :=
  rfl

@[simp]
theorem one_sderiv (β : TypeIndex) [LtLevel β] :
    (1 : NewPerm).sderiv β = 1 :=
  rfl

@[simp]
theorem inv_sderiv (ρ : NewPerm) (β : TypeIndex) [LtLevel β] :
    ρ⁻¹.sderiv β = (ρ.sderiv β)⁻¹ :=
  rfl

instance : Group NewPerm where
  mul_assoc ρ₁ ρ₂ ρ₃ := by
    ext β : 3
    simp only [mul_sderiv, mul_assoc]
  one_mul ρ := by
    ext β : 3
    simp only [mul_sderiv, one_mul, one_sderiv]
  mul_one ρ := by
    ext β : 3
    simp only [mul_sderiv, mul_one, one_sderiv]
  inv_mul_cancel ρ := by
    ext β : 3
    simp only [mul_sderiv, inv_sderiv, inv_mul_cancel, one_sderiv]

instance : SMul NewPerm Code where
  smul ρ c := ⟨c.β, ρ.sderiv c.β • c.s, Set.smul_set_nonempty.mpr c.hs⟩

@[simp]
theorem NewPerm.smul_mk (ρ : NewPerm) (β : TypeIndex) [LtLevel β]
    (s : Set (TSet β)) (hs : s.Nonempty) :
    ρ • Code.mk β s hs = ⟨β, ρ.sderiv β • s, Set.smul_set_nonempty.mpr hs⟩ :=
  rfl

instance : MulAction NewPerm Code where
  one_smul := by
    rintro ⟨β, s, hs⟩
    simp only [NewPerm.smul_mk, one_sderiv, one_smul]
  mul_smul := by
    rintro ρ₁ ρ₂ ⟨β, s, hs⟩
    simp only [NewPerm.smul_mk, mul_sderiv, mul_smul]

theorem Cloud.smul {c d : Code} (h : Cloud c d) (ρ : NewPerm) :
    Cloud (ρ • c) (ρ • d) := by
  obtain ⟨β, γ, hβγ, s, hs⟩ := h
  convert Cloud.mk β γ hβγ (ρ.sderiv β • s) (Set.smul_set_nonempty.mpr hs) using 1
  rw [NewPerm.smul_mk, Code.mk.injEq, heq_eq_eq]
  use rfl
  ext x
  constructor
  · rintro ⟨y, ⟨N, ⟨t, ht, hN⟩, rfl⟩, rfl⟩
    refine ⟨(ρ.sderiv γ)ᵁ ↘. • N, ⟨ρ.sderiv β • t, ?_, ?_⟩, ?_⟩
    · rwa [Tangle.smul_set, Set.smul_mem_smul_set_iff]
    · rw [BasePerm.smul_nearLitter_litter, hN, NewPerm.smul_fuzz]
    · rw [← TypedNearLitters.smul_typed]
  · rintro ⟨N, ⟨t, ⟨x, hxs, hxt⟩, hN⟩, rfl⟩
    refine ⟨(ρ.sderiv γ)⁻¹ • typed N,
        ⟨(ρ.sderiv γ)ᵁ⁻¹ ↘. • N, ⟨(ρ.sderiv β)⁻¹ • t, ?_, ?_⟩, ?_⟩, ?_⟩
    · rwa [Tangle.smul_set, ← hxt, inv_smul_smul]
    · rw [Tree.inv_sderivBot, BasePerm.smul_nearLitter_litter, inv_smul_eq_iff,
        NewPerm.smul_fuzz, smul_inv_smul, hN]
    · rw [Tree.inv_sderivBot, TypedNearLitters.smul_typed, allPermForget_inv, Tree.inv_sderivBot]
    · simp only [smul_inv_smul]

@[simp]
theorem Code.smul_even {c : Code} (ρ : NewPerm) :
    (ρ • c).Even ↔ c.Even := by
  induction c using cloud_wf.induction
  case h c ih =>
    constructor
    · rintro ⟨_, hc⟩
      constructor
      intro d hd
      have := hc (ρ • d) (hd.smul ρ)
      by_contra hd'
      rw [not_odd, ← ih d hd] at hd'
      exact not_even_and_odd _ ⟨hd', this⟩
    · rintro ⟨_, hc⟩
      constructor
      intro d hd
      have hc' := hc (ρ⁻¹ • d) ?_
      · have ih' := ih (ρ⁻¹ • d) ?_
        · rw [smul_inv_smul] at ih'
          by_contra hd'
          rw [not_odd, ih'] at hd'
          exact not_even_and_odd _ ⟨hd', hc'⟩
        · have := hd.smul ρ⁻¹
          rwa [inv_smul_smul] at this
      · have := hd.smul ρ⁻¹
        rwa [inv_smul_smul] at this

theorem Represents.smul {c d : Code} (h : Represents c d) (ρ : NewPerm) :
    Represents (ρ • c) (ρ • d) := by
  obtain (⟨_, h⟩ | ⟨_, _, hc, hcd⟩) := h
  · refine .refl _ ?_
    rwa [Code.smul_even]
  · refine .cloud _ _ ?_ ?_
    · rwa [Code.smul_even]
    · exact hcd.smul ρ

def Path.untop {β γ : TypeIndex} (A : β ↝ γ) (h : β ≠ γ) :
    ((δ : {δ : TypeIndex // δ < β}) × δ ↝ γ) :=
  A.recScoderiv (motive := λ ε _ ↦ ε ≠ γ → ((δ : {δ : TypeIndex // δ < ε}) × δ ↝ γ))
    (λ h ↦ (h rfl).elim) (λ ε ζ B hζ _ h ↦ ⟨⟨ζ, hζ⟩, B⟩) h

def Path.recTop {β δ : TypeIndex} (hβδ : δ < β) {motive : Sort _}
    (scoderiv : ∀ γ (h : γ < β), γ ↝ δ → motive)
    {γ : TypeIndex} (A : β ↝ δ) : motive :=
  sorry

-- instance : SuperU NewPerm (StrPerm α) where
--   superU ρ := λ A ↦ A.recScoderiv (motive := λ β _ ↦ BasePerm) _ (λ β γ B hγβ _ ↦ _)

structure NewSet : Type u where
  c : Code
  hc : c.Even
  hS : ∃ S : Support α, ∀ ρ : NewPerm, ρᵁ • S = S → ρ • c = c

end ConNF
