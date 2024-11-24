import Mathlib.Algebra.Group.Action.Option
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
  smul_fuzz' {β : TypeIndex} {γ : Λ} [LtLevel β] [LtLevel γ] (hβγ : β ≠ γ) (t : Tangle β) :
    (sderiv γ)ᵁ ↘. • fuzz hβγ t = fuzz hβγ (sderiv β • t)

instance : Mul NewPerm where
  mul ρ₁ ρ₂ := ⟨λ β _ ↦ ρ₁.sderiv β * ρ₂.sderiv β, by
    intro β γ _ _ hβγ t
    simp only [allPermForget_mul, mul_smul, Tree.mul_sderivBot, NewPerm.smul_fuzz']⟩

instance : One NewPerm where
  one := ⟨λ _ _ ↦ 1, by
    intro β γ _ _ hβγ t
    simp only [allPermForget_one, one_smul, Tree.one_sderivBot]⟩

instance : Inv NewPerm where
  inv ρ := ⟨λ β _ ↦ (ρ.sderiv β)⁻¹, by
    intro β γ _ _ hβγ t
    simp only [allPermForget_inv, Tree.inv_sderivBot, inv_smul_eq_iff, NewPerm.smul_fuzz',
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
    · rw [BasePerm.smul_nearLitter_litter, hN, NewPerm.smul_fuzz']
    · rw [← TypedNearLitters.smul_typed]
  · rintro ⟨N, ⟨t, ⟨x, hxs, hxt⟩, hN⟩, rfl⟩
    refine ⟨(ρ.sderiv γ)⁻¹ • typed N,
        ⟨(ρ.sderiv γ)ᵁ⁻¹ ↘. • N, ⟨(ρ.sderiv β)⁻¹ • t, ?_, ?_⟩, ?_⟩, ?_⟩
    · rwa [Tangle.smul_set, ← hxt, inv_smul_smul]
    · rw [Tree.inv_sderivBot, BasePerm.smul_nearLitter_litter, inv_smul_eq_iff,
        NewPerm.smul_fuzz', smul_inv_smul, hN]
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

theorem NewPerm.smul_fuzz {β : TypeIndex} {γ : Λ} [LtLevel β] [LtLevel γ]
    (ρ : NewPerm) (hβγ : β ≠ γ) (t : Tangle β) :
    ρᵁ ↘ (LtLevel.elim : (γ : TypeIndex) < α) ↘. • fuzz hβγ t = fuzz hβγ (ρ.sderiv β • t) := by
  rw [forget_sderiv, ρ.smul_fuzz']

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
  TSet := Option NewSet
  AllPerm := NewPerm
  tSetForget x := x.elim (StrSet.coeEquiv.symm λ _ _ ↦ ∅) (·ᵁ)
  allPermForget := (·ᵁ)

@[simp]
theorem newPreModelData.tSetForget_none :
    newPreModelData.tSetForget none = (StrSet.coeEquiv.symm λ _ _ ↦ ∅) :=
  rfl

@[simp]
theorem newPreModelData.tSetForget_some (x : NewSet) :
    newPreModelData.tSetForget (some x) = xᵁ :=
  rfl

@[simp]
theorem newPreModelData.tSetForget_none' :
    (show @TSet _ α newPreModelData from none)ᵁ = (StrSet.coeEquiv.symm λ _ _ ↦ ∅) :=
  rfl

@[simp]
theorem newPreModelData.tSetForget_some' (x : NewSet) :
    (show @TSet _ α newPreModelData from some x)ᵁ = xᵁ :=
  rfl

theorem StrSet.smul_none (π : StrPerm α) :
    π • (StrSet.coeEquiv.symm λ _ _ ↦ ∅ : StrSet α) = StrSet.coeEquiv.symm λ _ _ ↦ ∅ := by
  sorry

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
  obtain (_ | x) := x
  · use ⟨.empty, .empty⟩
    constructor
    · intros
      rfl
    · rintro ⟨⟩
  · obtain ⟨S, hS⟩ := x.hS
    refine ⟨S, ?_, λ h ↦ (WithBot.bot_ne_coe.symm h).elim⟩
    intro ρ hρ
    apply congr_arg some
    apply NewSet.ext
    exact hS ρ hρ

theorem NewSet.coe_ne_empty (x : NewSet) : xᵁ ≠ (StrSet.coeEquiv.symm λ _ _ ↦ ∅) := by
  sorry

def newModelData : ModelData α where
  tSetForget_injective' := by
    rintro (_ | x) (_ | y) h
    · rfl
    · cases NewSet.coe_ne_empty y h.symm
    · cases NewSet.coe_ne_empty x h
    · rw [NewSet.forget_injective x y h]
  tSetForget_surjective_of_bot' := by rintro ⟨⟩
  allPermForget_injective' := NewPerm.forget_injective
  allPermForget_one := NewPerm.forget_one
  allPermForget_mul := NewPerm.forget_mul
  smul_forget := by
    rintro ρ (_ | x)
    · rw [newPreModelData.tSetForget_none', StrSet.smul_none]
      rfl
    · exact NewPerm.smul_forget ρ x
  exists_support := NewSet.exists_support
  __ := newPreModelData

theorem Code.hasSet (c : Code)
    (hc : ∃ S : Support α, ∀ ρ : NewPerm, ρᵁ • S = S → ρ • c = c) :
    ∃ x : NewSet, Represents x.c c := by
  obtain ⟨d, hd⟩ := represents_cofunctional.surjective c
  refine ⟨⟨d, hd.even, ?_⟩, hd⟩
  obtain ⟨S, hS⟩ := hc
  use S
  intro ρ hρ
  have := hS ρ hρ
  have hρd := hd.smul ρ
  rw [this] at hρd
  rw [← represents_cofunctional.injective hd hρd]

def Code.toSet (c : Code)
    (hc : ∃ S : Support α, ∀ ρ : NewPerm, ρᵁ • S = S → ρ • c = c) :
    NewSet :=
  (c.hasSet hc).choose

theorem Code.toSet_spec (c : Code)
    (hc : ∃ S : Support α, ∀ ρ : NewPerm, ρᵁ • S = S → ρ • c = c) :
    Represents (c.toSet hc).c c :=
  (c.hasSet hc).choose_spec

def NearLitter.code (N : NearLitter) : Code :=
  ⟨⊥, {x | StrSet.botEquiv xᵁ ∈ Nᴬ}, by
    have : #Nᴬ ≠ 0 := sorry
    rw [Cardinal.mk_ne_zero_iff_nonempty] at this
    obtain ⟨a, ha⟩ := this
    obtain ⟨x, hx⟩ := tSetForget_surjective (StrSet.botEquiv.symm a)
    use x
    rwa [Set.mem_setOf_eq, hx, Equiv.apply_symm_apply]⟩

def newTyped (N : NearLitter) : NewSet :=
  N.code.toSet sorry

def newSingleton {γ : Λ} [LtLevel γ] (x : TSet γ) : NewSet :=
  sorry

local instance : ModelData α := newModelData

theorem mem_newSingleton_iff {γ : Λ} [LtLevel γ] (x y : TSet γ) :
    y ∈[LtLevel.elim] (show TSet α from some (newSingleton x)) ↔ y = x :=
  sorry

theorem not_mem_none {β : TypeIndex} [LtLevel β] (z : TSet β) :
    ¬z ∈[LtLevel.elim] (show TSet α from none) := by
  unfold TypedMem.typedMem instTypedMemTSet
  change zᵁ ∉ _
  erw [Equiv.apply_symm_apply]
  exact id

theorem newModelData_ext (β : Λ) [LtLevel β] (x y : TSet α)
    (h : ∀ z : TSet β, z ∈[LtLevel.elim] x ↔ z ∈[LtLevel.elim] y) :
    x = y := by
  obtain (_ | x) := x <;> obtain (_ | y) := y
  · rfl
  · obtain ⟨z, hz⟩ := Code.members_nonempty y.hc β
    rw [NewSet.mem_members] at hz
    cases not_mem_none z ((h z).mpr hz)
  · obtain ⟨z, hz⟩ := Code.members_nonempty x.hc β
    rw [NewSet.mem_members] at hz
    cases not_mem_none z ((h z).mp hz)
  · apply congr_arg some
    apply NewSet.ext
    apply Code.ext x.hc y.hc β
    ext z
    rw [NewSet.mem_members, NewSet.mem_members]
    exact h z

def newPositionDeny (t : Tangle α) : Set μ :=
  pos '' {N | t.set = some (newTyped N)} ∪
    pos '' (t.supportᴬ.image Prod.snd : Set Atom) ∪
    pos '' (t.supportᴺ.image Prod.snd : Set NearLitter)

theorem card_newPositionDeny (t : Tangle α) :
    #(newPositionDeny t) < (#μ).ord.cof := sorry

def newPosition (h : #(Tangle α) ≤ #μ) : Position (Tangle α) where
  pos := ⟨funOfDeny h newPositionDeny card_newPositionDeny, funOfDeny_injective _ _ _⟩

theorem pos_atom_lt_newPosition (h : #(Tangle α) ≤ #μ) (t : Tangle α) (a : Atom)
    (A : α ↝ ⊥) (ha : a ∈ (t.support ⇘. A)ᴬ) :
    pos a < (newPosition h).pos t := by
  apply funOfDeny_gt_deny
  obtain ⟨i, hi⟩ := ha
  refine Or.inl (Or.inr ⟨_, ?_, rfl⟩)
  exact ⟨i, ⟨A, a⟩, hi, rfl⟩

theorem pos_nearLitter_lt_newPosition (h : #(Tangle α) ≤ #μ) (t : Tangle α) (N : NearLitter)
    (A : α ↝ ⊥) (hN : N ∈ (t.support ⇘. A)ᴺ) :
    pos N < (newPosition h).pos t := by
  apply funOfDeny_gt_deny
  obtain ⟨i, hi⟩ := hN
  refine Or.inr ⟨_, ?_, rfl⟩
  exact ⟨i, ⟨A, N⟩, hi, rfl⟩

def newTypedNearLitters (h : #(Tangle α) ≤ #μ) :
    letI := newPosition h; TypedNearLitters α :=
  letI := newPosition h
  {
    typed := some ∘ newTyped
    typed_injective := sorry
    pos_le_pos_of_typed := sorry
    smul_typed := sorry
  }

end ConNF
