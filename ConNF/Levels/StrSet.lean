import ConNF.Levels.StrPerm

/-!
# Structural sets

In this file, we define structural sets, which serve as the environment inside which we will
construct the types of our model

## Main declarations

* `ConNF.StrSet`: The type family of structural sets.
-/

universe u

open scoped Pointwise

namespace ConNF

variable [Params.{u}]

def StrSet : TypeIndex → Type u
  | ⊥ => Atom
  | (α : Λ) => (β : TypeIndex) → β < α → Set (StrSet β)
termination_by α => α

namespace StrSet

theorem bot_eq :
    StrSet ⊥ = Atom := by
  unfold StrSet
  rfl

theorem coe_eq (α : Λ) :
    StrSet α = ((β : TypeIndex) → β < α → Set (StrSet β)) := by
  unfold StrSet
  rfl

def botEquiv :
    StrSet ⊥ ≃ Atom :=
  Equiv.cast bot_eq

def coeEquiv {α : Λ} :
    StrSet α ≃ ((β : TypeIndex) → β < α → Set (StrSet β)) :=
  Equiv.cast (coe_eq α)

/-- Extensionality for structural sets at proper type indices. If two structural sets have the same
extensions at every lower type index, then they are the same. -/
theorem coe_ext_iff' {α : Λ} {x y : StrSet α} :
    x = y ↔ ∀ β hβ z, z ∈ coeEquiv x β hβ ↔ z ∈ coeEquiv y β hβ := by
  constructor
  · rintro rfl
    simp only [implies_true, forall_const]
  · intro h
    apply coeEquiv.injective
    ext β hβ t
    exact h β hβ t

def strPerm_smul : {α : TypeIndex} → StrPerm α → StrSet α → StrSet α
  | ⊥, π, x => botEquiv.symm <| π Path.nil • botEquiv x
  | (α : Λ), π, x => coeEquiv.symm <| λ β hβ ↦ strPerm_smul (π ↘ hβ) '' coeEquiv x β hβ
termination_by α => α

theorem strPerm_smul_bot_def (π : StrPerm ⊥) (x : StrSet ⊥) :
    strPerm_smul π x = botEquiv.symm (π .nil • botEquiv x) := by
  unfold strPerm_smul
  rfl

theorem strPerm_smul_coe_def {α : Λ} (π : StrPerm α) (x : StrSet α) :
    strPerm_smul π x = coeEquiv.symm (λ β hβ ↦ strPerm_smul (π ↘ hβ) '' coeEquiv x β hβ) := by
  conv_lhs => unfold strPerm_smul

instance {α : TypeIndex} : SMul (StrPerm α) (StrSet α) where
  smul := strPerm_smul

theorem strPerm_smul_bot_def' (π : StrPerm ⊥) (x : StrSet ⊥) :
    π • x = botEquiv.symm (π .nil • botEquiv x) :=
  strPerm_smul_bot_def π x

theorem strPerm_smul_coe_def' {α : Λ} (π : StrPerm α) (x : StrSet α) :
    π • x = coeEquiv.symm (λ β hβ ↦ strPerm_smul (π ↘ hβ) '' coeEquiv x β hβ) :=
  strPerm_smul_coe_def π x

@[simp]
theorem strPerm_smul_bot (π : StrPerm ⊥) (x : StrSet ⊥) :
    botEquiv (π • x) = π .nil • botEquiv x := by
  rw [strPerm_smul_bot_def', Equiv.apply_symm_apply]

@[simp]
theorem strPerm_smul_coe {α : Λ} (π : StrPerm α) (x : StrSet α) :
    coeEquiv (π • x) = λ β hβ ↦ π ↘ hβ • coeEquiv x β hβ := by
  rw [strPerm_smul_coe_def', Equiv.apply_symm_apply]
  rfl

theorem one_strPerm_smul {α : TypeIndex} (x : StrSet α) : strPerm_smul 1 x = x := by
  induction α using WellFoundedLT.induction
  case ind α ih =>
    cases α using WithBot.recBotCoe
    case bot => rw [strPerm_smul_bot_def, Tree.one_apply, one_smul, Equiv.symm_apply_apply]
    case coe α =>
      rw [strPerm_smul_coe_def, coe_ext_iff']
      intro β hβ y
      simp only [Tree.one_sderiv, Equiv.apply_symm_apply, ih β hβ, Set.image_id']

theorem mul_strPerm_smul {α : TypeIndex} (π₁ π₂ : StrPerm α) (x : StrSet α) :
    strPerm_smul (π₁ * π₂) x = strPerm_smul π₁ (strPerm_smul π₂ x) := by
  induction α using WellFoundedLT.induction
  case ind α ih =>
    cases α using WithBot.recBotCoe
    case bot =>
      simp only [strPerm_smul_bot_def, Tree.mul_apply, mul_smul, Equiv.apply_symm_apply]
    case coe α =>
      simp only [strPerm_smul_coe_def, coe_ext_iff']
      intro β hβ y
      simp only [Tree.mul_sderiv, Equiv.apply_symm_apply, Set.mem_image, exists_exists_and_eq_and,
        ih β hβ]

instance {α : TypeIndex} : MulAction (StrPerm α) (StrSet α) where
  one_smul := one_strPerm_smul
  mul_smul := mul_strPerm_smul

theorem smul_none {α : Λ} (π : StrPerm α) :
    π • (StrSet.coeEquiv.symm λ _ _ ↦ ∅ : StrSet α) = StrSet.coeEquiv.symm λ _ _ ↦ ∅ := by
  simp only [Equiv.eq_symm_apply, strPerm_smul_coe, Equiv.apply_symm_apply, Set.smul_set_empty]

end StrSet

/-!
## Notation for typed membership
-/

class TypedMem (X Y : Type _) (β α : outParam TypeIndex) where
  typedMem : β < α → X → Y → Prop

notation:50 x:50 " ∈[" h "] " y:50 => TypedMem.typedMem h x y
notation:50 x:50 " ∈' " y:50 => TypedMem.typedMem (by assumption) x y

instance {β α : TypeIndex} : TypedMem (StrSet β) (StrSet α) β α where
  typedMem h x y :=
    match α with
    | ⊥ => (not_lt_bot h).elim
    | (α : Λ) => x ∈ StrSet.coeEquiv y β h

theorem StrSet.mem_iff {α : Λ} {β : TypeIndex} {x : StrSet β} {y : StrSet α} (h : β < α) :
    x ∈[h] y ↔ x ∈ coeEquiv y β h :=
  Iff.rfl

/-- Extensionality for structural sets at proper type indices. If two structural sets have the same
extensions at every lower type index, then they are the same. -/
theorem StrSet.coe_ext_iff {α : Λ} {x y : StrSet α} :
    x = y ↔ ∀ β : TypeIndex, ∀ hβ : β < α, ∀ z : StrSet β, z ∈[hβ] x ↔ z ∈[hβ] y :=
  StrSet.coe_ext_iff'

theorem StrSet.mem_smul_iff {α β : TypeIndex} {x : StrSet β} {y : StrSet α}
    (h : β < α) (π : StrPerm α) :
    x ∈[h] π • y ↔ (π ↘ h)⁻¹ • x ∈[h] y := by
  cases α using WithBot.recBotCoe
  case bot => cases not_lt_bot h
  case coe α => rw [mem_iff, mem_iff, strPerm_smul_coe, Set.mem_smul_set_iff_inv_smul_mem]

end ConNF
