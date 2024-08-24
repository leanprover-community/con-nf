import ConNF.Setup.StrSet
import ConNF.Setup.Support

/-!
# Model data

In this file, we define what model data at a type index means.

## Main declarations

* `ConNF.ModelData`: The type of model data at a given type index.
-/

universe u

open Cardinal

namespace ConNF

variable [Params.{u}]

/-- The same as `ModelData` but without the propositions. -/
class PreModelData (α : TypeIndex) where
  TSet : Type u
  AllPerm : Type u
  [allPermGroup : Group AllPerm]
  [allAction : MulAction AllPerm TSet]
  tSetForget : TSet → StrSet α
  allPermForget : AllPerm → StrPerm α

export PreModelData (TSet AllPerm)

attribute [instance] PreModelData.allPermGroup PreModelData.allAction

instance {α : TypeIndex} [PreModelData α] : SuperU (TSet α) (StrSet α) where
  superU := PreModelData.tSetForget

instance {α : TypeIndex} [PreModelData α] : SuperU (AllPerm α) (StrPerm α) where
  superU := PreModelData.allPermForget

structure Support.Supports {X : Type _} {α : TypeIndex} [PreModelData α] [MulAction (AllPerm α) X]
    (S : Support α) (x : X) : Prop where
  supports (ρ : AllPerm α) : ρᵁ • S = S → ρ • x = x
  nearLitters_eq_empty_of_bot : α = ⊥ → Sᴺ = .empty

class ModelData (α : TypeIndex) extends PreModelData α where
  allPermForget_one : (1 : AllPerm)ᵁ = 1
  allPermForget_mul (ρ₁ ρ₂ : AllPerm) : (ρ₁ * ρ₂)ᵁ = ρ₁ᵁ * ρ₂ᵁ
  smul_forget (ρ : AllPerm) (x : TSet) : (ρ • x)ᵁ = ρᵁ • xᵁ
  exists_support (x : TSet) : ∃ S : Support α, S.Supports x

@[ext]
structure Tangle (α : TypeIndex) [ModelData α] where
  set : TSet α
  support : Support α
  support_supports : support.Supports set

/-!
## Criteria for supports
-/

theorem Support.supports_coe {α : Λ} {X : Type _} [PreModelData α] [MulAction (AllPerm α) X]
    (S : Support α) (x : X)
    (h : ∀ ρ : AllPerm α,
      (∀ A : α ↝ ⊥, ∀ a ∈ (S ⇘. A)ᴬ, ρᵁ A • a = a) →
      (∀ A : α ↝ ⊥, ∀ N ∈ (S ⇘. A)ᴺ, ρᵁ A • N = N) → ρ • x = x) :
    S.Supports x := by
  constructor
  · intro ρ h'
    apply h
    · intro A a ha
      exact Enumeration.smul_eq_of_mem_of_smul_eq (smul_atoms_eq_of_smul_eq h') A a ha
    · intro A N hN
      exact Enumeration.smul_eq_of_mem_of_smul_eq (smul_nearLitters_eq_of_smul_eq h') A N hN
  · intro h
    cases h

theorem Support.supports_bot {X : Type _} [PreModelData ⊥] [MulAction (AllPerm ⊥) X]
    (E : Enumeration (⊥ ↝ ⊥ × Atom)) (x : X)
    (h : ∀ ρ : AllPerm ⊥, (∀ A : ⊥ ↝ ⊥, ∀ x : Atom, (A, x) ∈ E → ρᵁ A • x = x) → ρ • x = x) :
    (⟨E, .empty⟩ : Support ⊥).Supports x := by
  constructor
  · intro ρ h'
    apply h
    intro A x hx
    exact Enumeration.smul_eq_of_mem_of_smul_eq (smul_atoms_eq_of_smul_eq h') A x hx
  · intro
    rfl

/-!
## Model data at level `⊥`
-/

def botPreModelData : PreModelData ⊥ where
  TSet := Atom
  AllPerm := BasePerm
  tSetForget := StrSet.botEquiv.symm
  allPermForget ρ _ := ρ

def botModelData : ModelData ⊥ where
  allPermForget_one := rfl
  allPermForget_mul _ _ := rfl
  smul_forget ρ x := by
    apply StrSet.botEquiv.injective
    have : ∀ x : TSet ⊥, xᵁ = StrSet.botEquiv.symm x := λ _ ↦ rfl
    simp only [this, Equiv.apply_symm_apply, StrSet.strPerm_smul_bot]
    rfl
  exists_support x := by
    use ⟨.singleton (Path.nil, x), .empty⟩
    apply Support.supports_bot
    intro ρ hc
    apply hc Path.nil x
    rw [Enumeration.mem_singleton_iff]
  __ := botPreModelData

end ConNF
