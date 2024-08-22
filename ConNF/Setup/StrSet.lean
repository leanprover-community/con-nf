import ConNF.Setup.StrPerm

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
theorem coe_ext_iff {α : Λ} {x y : StrSet α} :
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

end StrSet

end ConNF
