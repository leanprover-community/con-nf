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

@[simp]
theorem NewPerm.smul_members (ρ : NewPerm) (c : Code) (β : TypeIndex) [LtLevel β] :
    (ρ • c).members β = ρ.sderiv β • c.members β := by
  ext x : 1
  constructor
  · rintro ⟨s, hs, hx, hc⟩
    refine ⟨(ρ.sderiv β)⁻¹ • x, ?_, smul_inv_smul _ _⟩
    refine ⟨(ρ.sderiv β)⁻¹ • s, Set.Nonempty.smul_set hs, Set.smul_mem_smul_set hx, ?_⟩
    have := hc.smul ρ⁻¹
    rwa [inv_smul_smul, smul_mk, inv_sderiv] at this
  · rintro ⟨x, ⟨s, hs, hx, hc⟩, rfl⟩
    refine ⟨ρ.sderiv β • s, Set.Nonempty.smul_set hs, Set.smul_mem_smul_set hx, ?_⟩
    exact hc.smul ρ

instance : SuperU NewPerm (StrPerm α) where
  superU ρ := λ A ↦ A.recScoderiv (motive := λ β _ ↦ β ≠ ⊥ → β ≤ α → BasePerm)
    (λ h ↦ (h rfl).elim)
    (λ _β γ B hγβ _ _ hβα ↦ letI : LtLevel γ := ⟨hγβ.trans_le hβα⟩; (ρ.sderiv γ)ᵁ B)
    WithBot.coe_ne_bot le_rfl

theorem NewPerm.forget_def (ρ : NewPerm) (A : α ↝ ⊥) :
    ρᵁ A = A.recScoderiv (motive := λ β _ ↦ β ≠ ⊥ → β ≤ α → BasePerm)
      (λ h ↦ (h rfl).elim)
      (λ _β γ B hγβ _ _ hβα ↦ letI : LtLevel γ := ⟨hγβ.trans_le hβα⟩; (ρ.sderiv γ)ᵁ B)
      WithBot.coe_ne_bot le_rfl :=
  rfl

@[simp]
theorem NewPerm.forget_sderiv (ρ : NewPerm) (β : TypeIndex) [LtLevel β] :
    ρᵁ ↘ LtLevel.elim = (ρ.sderiv β)ᵁ := by
  funext A
  rw [Tree.sderiv_apply, NewPerm.forget_def, Path.recScoderiv_scoderiv]

@[simp]
theorem NewPerm.forget_mul (ρ₁ ρ₂ : NewPerm) :
    (ρ₁ * ρ₂)ᵁ = ρ₁ᵁ * ρ₂ᵁ := by
  funext A
  cases A using Path.recScoderiv
  case scoderiv β A hβ _ =>
    haveI : LtLevel β := ⟨hβ⟩
    rw [Tree.mul_apply, ← Tree.sderiv_apply (ρ₁ * ρ₂)ᵁ,
      ← Tree.sderiv_apply ρ₁ᵁ, ← Tree.sderiv_apply ρ₂ᵁ,
      forget_sderiv, forget_sderiv, forget_sderiv,
      mul_sderiv, allPermForget_mul, Tree.mul_apply]

@[simp]
theorem NewPerm.forget_one :
    (1 : NewPerm)ᵁ = 1 := by
  funext A
  cases A using Path.recScoderiv
  case scoderiv β A hβ _ =>
    haveI : LtLevel β := ⟨hβ⟩
    rw [Tree.one_apply, ← Tree.sderiv_apply (1 : NewPerm)ᵁ, forget_sderiv,
      one_sderiv, allPermForget_one, Tree.one_apply]

@[simp]
theorem NewPerm.forget_inv (ρ : NewPerm) :
    ρ⁻¹ᵁ = ρᵁ⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← forget_mul, inv_mul_cancel, forget_one]

@[ext]
structure NewSet : Type u where
  c : Code
  hc : c.Even
  hS : ∃ S : Support α, ∀ ρ : NewPerm, ρᵁ • S = S → ρ • c = c

instance : SuperU NewSet (StrSet α) where
  superU x := StrSet.coeEquiv.symm
    λ β hβ ↦ letI : LtLevel β := ⟨hβ⟩; (·ᵁ) '' x.c.members β

theorem NewSet.forget_def (x : NewSet) :
    xᵁ = StrSet.coeEquiv.symm
      λ β hβ ↦ letI : LtLevel β := ⟨hβ⟩; (·ᵁ) '' x.c.members β :=
  rfl

theorem NewSet.typedMem_forget (x : NewSet) (β : TypeIndex) (hβ : β < α) (y : StrSet β) :
    y ∈[hβ] xᵁ ↔ letI : LtLevel β := ⟨hβ⟩; y ∈ (·ᵁ) '' x.c.members β := by
  rw [StrSet.mem_iff, forget_def, Equiv.apply_symm_apply]

theorem NewSet.mem_members (x : NewSet) (β : TypeIndex) [hβ : LtLevel β] (y : TSet β) :
    y ∈ x.c.members β ↔ yᵁ ∈[hβ.elim] xᵁ := by
  rw [typedMem_forget]
  constructor
  · apply Set.mem_image_of_mem
  · rintro ⟨z, hz, hzy⟩
    cases tSetForget_injective hzy
    exact hz

instance : SMul NewPerm NewSet where
  smul ρ x := ⟨ρ • x.c, (Code.smul_even ρ).mpr x.hc, by
    obtain ⟨S, hS⟩ := x.hS
    use ρᵁ • S
    intro ρ' hρ'
    have := hS (ρ⁻¹ * ρ' * ρ) ?_
    · rwa [mul_smul, mul_smul, inv_smul_eq_iff] at this
    · rwa [NewPerm.forget_mul, NewPerm.forget_mul, mul_smul, mul_smul,
        NewPerm.forget_inv, inv_smul_eq_iff] ⟩

@[simp]
theorem NewSet.smul_c (ρ : NewPerm) (x : NewSet) :
    (ρ • x).c = ρ • x.c :=
  rfl

instance : MulAction NewPerm NewSet where
  one_smul x := by
    ext : 1
    rw [NewSet.smul_c, one_smul]
  mul_smul ρ₁ ρ₂ x := by
    ext : 1
    simp only [NewSet.smul_c, mul_smul]

def newPreModelData : PreModelData α where
  TSet := NewSet
  AllPerm := NewPerm
  tSetForget := (·ᵁ)
  allPermForget := (·ᵁ)

theorem NewPerm.forget_injective (ρ₁ ρ₂ : NewPerm) (h : ρ₁ᵁ = ρ₂ᵁ) : ρ₁ = ρ₂ := by
  ext β hβ : 3
  apply allPermForget_injective
  have := congr_arg (· ↘ hβ.elim) h
  simp only [forget_sderiv] at this
  exact this

theorem NewSet.forget_injective (x y : NewSet) (h : xᵁ = yᵁ) : x = y := by
  ext : 1
  apply Code.ext' x.hc y.hc
  intro β _
  ext z
  rw [NewSet.mem_members, NewSet.mem_members, h]

theorem NewPerm.smul_forget (ρ : NewPerm) (x : NewSet) : (ρ • x)ᵁ = ρᵁ • xᵁ := by
  rw [StrSet.coe_ext_iff]
  intro β hβ z
  haveI : LtLevel β := ⟨hβ⟩
  rw [StrSet.mem_smul_iff, NewSet.typedMem_forget, NewSet.typedMem_forget,
    NewSet.smul_c, smul_members]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(ρ.sderiv β)⁻¹ • y, ?_, ?_⟩
    · rwa [Set.mem_smul_set_iff_inv_smul_mem] at hy
    · simp only [ConNF.ModelData.smul_forget, allPermForget_inv, forget_sderiv]
  · rintro ⟨y, hy, hyz⟩
    rw [eq_inv_smul_iff] at hyz
    cases hyz
    refine ⟨ρ.sderiv β • y, Set.smul_mem_smul_set hy, ?_⟩
    simp only [ConNF.ModelData.smul_forget, forget_sderiv]

theorem NewSet.exists_support (x : letI := newPreModelData; TSet α) :
    letI := newPreModelData
    ∃ S : Support α, S.Supports x := by
  letI := newPreModelData
  obtain ⟨S, hS⟩ := x.hS
  refine ⟨S, ?_, λ h ↦ (WithBot.bot_ne_coe.symm h).elim⟩
  intro ρ hρ
  apply NewSet.ext
  exact hS ρ hρ

def newModelData : ModelData α where
  tSetForget_injective' := NewSet.forget_injective
  allPermForget_injective' := NewPerm.forget_injective
  allPermForget_one := NewPerm.forget_one
  allPermForget_mul := NewPerm.forget_mul
  smul_forget := NewPerm.smul_forget
  exists_support := NewSet.exists_support
  __ := newPreModelData

end ConNF
