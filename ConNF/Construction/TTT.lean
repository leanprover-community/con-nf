import ConNF.Construction.Externalise

/-!
# New file

In this file...

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal

open scoped Pointwise

namespace ConNF

variable [Params.{u}]

/-- A redefinition of the derivative of allowable permutations that is invariant of level,
but still has nice definitional properties. -/
@[default_instance 200]
instance {β γ : TypeIndex} : Derivative (AllPerm β) (AllPerm γ) β γ where
  deriv ρ A :=
    A.recSderiv
    (motive := λ (δ : TypeIndex) (A : β ↝ δ) ↦
      letI : Level := ⟨δ.recBotCoe (Nonempty.some inferInstance) id⟩
      letI : LeLevel δ := ⟨δ.recBotCoe (λ _ ↦ bot_le) (λ _ h ↦ WithBot.coe_le_coe.mpr h.le)
        (show δ.recBotCoe (Nonempty.some inferInstance) id = Level.α from rfl)⟩
      AllPerm δ)
    ρ (λ δ ε A h ρ ↦
      letI : Level := ⟨δ.recBotCoe (Nonempty.some inferInstance) id⟩
      letI : LeLevel δ := ⟨δ.recBotCoe (λ _ ↦ bot_le) (λ _ h ↦ WithBot.coe_le_coe.mpr h.le)
        (show δ.recBotCoe (Nonempty.some inferInstance) id = Level.α from rfl)⟩
      letI : LeLevel ε := ⟨h.le.trans LeLevel.elim⟩
      PreCoherentData.allPermSderiv h ρ)

@[simp]
theorem allPerm_deriv_nil' {β : TypeIndex}
    (ρ : AllPerm β) :
    ρ ⇘ (.nil : β ↝ β) = ρ :=
  rfl

@[simp]
theorem allPerm_deriv_sderiv' {β γ δ : TypeIndex}
    (ρ : AllPerm β) (A : β ↝ γ) (h : δ < γ) :
    ρ ⇘ (A ↘ h) = ρ ⇘ A ↘ h :=
  rfl

def Symmetric {α β : Λ} (s : Set (TSet β)) (hβ : (β : TypeIndex) < α) : Prop :=
  ∃ S : Support α, ∀ ρ : AllPerm α, ρᵁ • S = S → ρ ↘ hβ • s = s

def newSetEquiv {α : Λ} :
    letI : Level := ⟨α⟩
    @TSet _ α newModelData.toPreModelData ≃ TSet α :=
  letI : Level := ⟨α⟩
  castTSet (D₁ := newModelData) (D₂ := globalModelData) rfl
    (by rw [globalModelData, motive_eq, constructMotive, globalLtData_eq])

@[simp]
theorem newSetEquiv_forget {α : Λ}
    (x : letI : Level := ⟨α⟩; @TSet _ α newModelData.toPreModelData) :
    (newSetEquiv x)ᵁ = xᵁ :=
  letI : Level := ⟨α⟩
  castTSet_forget (D₁ := newModelData) (D₂ := globalModelData) _ x

def allPermEquiv {α : Λ} :
    letI : Level := ⟨α⟩
    NewPerm ≃ AllPerm α :=
  letI : Level := ⟨α⟩
  castAllPerm (D₁ := newModelData) (D₂ := globalModelData) rfl
    (by rw [globalModelData, motive_eq, constructMotive, globalLtData_eq])

@[simp]
theorem allPermEquiv_forget {α : Λ} (ρ : letI : Level := ⟨α⟩; NewPerm) :
    (allPermEquiv ρ)ᵁ = ρᵁ :=
  letI : Level := ⟨α⟩
  castAllPerm_forget (D₁ := newModelData) (D₂ := globalModelData) _ ρ

theorem allPermEquiv_sderiv {α β : Λ}
    (ρ : letI : Level := ⟨α⟩; NewPerm) (hβ : (β : TypeIndex) < α) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨hβ⟩
    allPermEquiv ρ ↘ hβ = ρ.sderiv β := by
  letI : Level := ⟨α⟩
  letI : LeLevel α := ⟨le_rfl⟩
  letI : LtLevel β := ⟨hβ⟩
  apply allPermForget_injective
  rw [allPermSderiv_forget, allPermEquiv_forget, NewPerm.forget_sderiv]

theorem TSet.exists_of_symmetric {α β : Λ} (s : Set (TSet β)) (hβ : (β : TypeIndex) < α)
    (hs : Symmetric s hβ) :
    ∃ x : TSet α, ∀ y : TSet β, y ∈[hβ] x ↔ y ∈ s := by
  letI : Level := ⟨α⟩
  letI : LtLevel β := ⟨hβ⟩
  suffices ∃ x : (@TSet _ α newModelData.toPreModelData), ∀ y : TSet β, yᵁ ∈[hβ] xᵁ ↔ y ∈ s by
    obtain ⟨x, hx⟩ := this
    use newSetEquiv x
    intro y
    rw [← hx, ← TSet.forget_mem_forget, newSetEquiv_forget]
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · use none
    intro y
    simp only [Set.mem_empty_iff_false, iff_false]
    exact not_mem_none y
  · use some (Code.toSet ⟨β, s, hs'⟩ ?_)
    · intro y
      erw [mem_some_iff]
      exact Code.mem_toSet _
    · obtain ⟨S, hS⟩ := hs
      use S
      intro ρ hρS
      have := hS (allPermEquiv ρ) ?_
      · simp only [NewPerm.smul_mk, Code.mk.injEq, heq_eq_eq, true_and]
        rwa [allPermEquiv_sderiv] at this
      · rwa [allPermEquiv_forget]

theorem TSet.symmetric {α β : Λ} (x : TSet α) (hβ : (β : TypeIndex) < α) :
    Symmetric {y : TSet β | y ∈[hβ] x} hβ := by
  letI : Level := ⟨α⟩
  letI : LtLevel β := ⟨hβ⟩
  set y := newSetEquiv.symm x with hy
  rw [Equiv.eq_symm_apply] at hy
  clear_value y
  cases hy
  simp only [← forget_mem_forget, newSetEquiv_forget]
  cases y
  case none =>
    use ⟨.empty, .empty⟩
    intro ρ hρ
    ext z
    constructor
    · rintro ⟨z, hz, rfl⟩
      cases not_mem_none z hz
    · intro hz
      cases not_mem_none z hz
  case some y =>
    obtain ⟨S, hS⟩ := y.hS
    use S
    intro ρ hρ
    have hc := hS (allPermEquiv.symm ρ) (by rwa [← allPermEquiv_forget, Equiv.apply_symm_apply])
    have hc' := NewPerm.smul_members (allPermEquiv.symm ρ) y.c β
    rw [hc, ← allPermEquiv_sderiv _ hβ, Equiv.apply_symm_apply, Set.ext_iff] at hc'
    simp only [NewSet.mem_members, Set.mem_smul_set_iff_inv_smul_mem] at hc'
    ext z
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hc' (ρ ↘ hβ • z)).mpr (by rwa [inv_smul_smul])
    · intro hz
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      exact (hc' z).mp hz

end ConNF
