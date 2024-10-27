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

theorem Support.Supports.mono {X : Type _} {α : TypeIndex} [PreModelData α]
    [MulAction (AllPerm α) X] {S T : Support α} {x : X}
    (hS : S.Supports x) (h : S ≤ T) (hT : α = ⊥ → Tᴺ = .empty) :
    T.Supports x := by
  constructor
  · intro ρ hρ
    apply hS.supports
    rw [Support.smul_eq_iff] at hρ ⊢
    intro A
    constructor
    · intro a ha
      exact (hρ A).1 a ((h A).1 a ha)
    · intro N hN
      exact (hρ A).2 N ((h A).2 N hN)
  · exact hT

class ModelData (α : TypeIndex) extends PreModelData α where
  allPermForget_injective' : Function.Injective allPermForget
  allPermForget_one : (1 : AllPerm)ᵁ = 1
  allPermForget_mul (ρ₁ ρ₂ : AllPerm) : (ρ₁ * ρ₂)ᵁ = ρ₁ᵁ * ρ₂ᵁ
  smul_forget (ρ : AllPerm) (x : TSet) : (ρ • x)ᵁ = ρᵁ • xᵁ
  exists_support (x : TSet) : ∃ S : Support α, S.Supports x

export ModelData (allPermForget_injective' allPermForget_one allPermForget_mul
  smul_forget exists_support)

attribute [simp] allPermForget_one allPermForget_mul smul_forget

theorem allPermForget_injective {α : TypeIndex} [ModelData α] {ρ₁ ρ₂ : AllPerm α}
    (h : ρ₁ᵁ = ρ₂ᵁ) : ρ₁ = ρ₂ :=
  allPermForget_injective' h

@[simp]
theorem allPermForget_inv {α : TypeIndex} [ModelData α] (ρ : AllPerm α) : ρ⁻¹ᵁ = ρᵁ⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← allPermForget_mul, inv_mul_cancel, allPermForget_one]

@[simp]
theorem allPermForget_npow {α : TypeIndex} [ModelData α] (ρ : AllPerm α) (n : ℕ) :
    (ρ ^ n)ᵁ = ρᵁ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, allPermForget_one]
  | succ n h => rw [pow_succ, pow_succ, allPermForget_mul, h]

@[simp]
theorem allPermForget_zpow {α : TypeIndex} [ModelData α] (ρ : AllPerm α) (n : ℤ) :
    (ρ ^ n)ᵁ = ρᵁ ^ n := by
  induction n using Int.negInduction with
  | nat n => rw [zpow_natCast, zpow_natCast, allPermForget_npow]
  | neg n h => simpa only [zpow_neg, zpow_natCast, allPermForget_inv, inv_inj] using h

theorem Support.Supports.smul_eq_smul {X : Type _} {α : TypeIndex}
    [ModelData α] [MulAction (AllPerm α) X]
    {S : Support α} {x : X} (h : S.Supports x) {ρ₁ ρ₂ : AllPerm α} (hρ : ρ₁ᵁ • S = ρ₂ᵁ • S) :
    ρ₁ • x = ρ₂ • x := by
  have := h.supports (ρ₂⁻¹ * ρ₁) ?_
  · rwa [mul_smul, inv_smul_eq_iff] at this
  · rwa [allPermForget_mul, mul_smul, allPermForget_inv, inv_smul_eq_iff]

theorem Support.Supports.smul_eq_of_smul_eq {X : Type _} {α : TypeIndex}
    [ModelData α] [MulAction (AllPerm α) X]
    {S : Support α} {x : X} (h : S.Supports x) {ρ : AllPerm α} (hρ : ρᵁ • S = S) :
    ρ • x = x := by
  have := smul_eq_smul (ρ₁ := ρ) (ρ₂ := 1) h ?_
  · rwa [one_smul] at this
  · rwa [allPermForget_one, one_smul]

theorem Support.Supports.smul {X : Type _} {α : TypeIndex}
    [ModelData α] [MulAction (AllPerm α) X]
    {S : Support α} {x : X} (h : S.Supports x) (ρ : AllPerm α) :
    (ρᵁ • S).Supports (ρ • x) := by
  constructor
  · intro σ hσ
    rw [smul_smul, ← allPermForget_mul] at hσ
    have := h.smul_eq_smul hσ
    rwa [mul_smul] at this
  · intro h'
    rw [smul_nearLitters, h.nearLitters_eq_empty_of_bot h']
    rfl

instance {β α : TypeIndex} [ModelData β] [ModelData α] : TypedMem (TSet β) (TSet α) β α where
  typedMem h y x := yᵁ ∈[h] xᵁ

theorem TSet.forget_mem_forget {β α : TypeIndex} [ModelData β] [ModelData α] (h : β < α)
    {x : TSet β} {y : TSet α} :
    xᵁ ∈[h] yᵁ ↔ x ∈[h] y :=
  Iff.rfl

@[ext]
structure Tangle (α : TypeIndex) [ModelData α] where
  set : TSet α
  support : Support α
  support_supports : support.Supports set

instance {α : TypeIndex} [ModelData α] : SMul (AllPerm α) (Tangle α) where
  smul ρ t := ⟨ρ • t.set, ρᵁ • t.support, t.support_supports.smul ρ⟩

@[simp]
theorem Tangle.smul_set {α : TypeIndex} [ModelData α] (ρ : AllPerm α) (t : Tangle α) :
    (ρ • t).set = ρ • t.set :=
  rfl

@[simp]
theorem Tangle.smul_support {α : TypeIndex} [ModelData α] (ρ : AllPerm α) (t : Tangle α) :
    (ρ • t).support = ρᵁ • t.support :=
  rfl

theorem Tangle.smul_eq_smul {α : TypeIndex} [ModelData α] {ρ₁ ρ₂ : AllPerm α} {t : Tangle α}
    (h : ρ₁ᵁ • t.support = ρ₂ᵁ • t.support) :
    ρ₁ • t = ρ₂ • t :=
  Tangle.ext (t.support_supports.smul_eq_smul h) h

instance {α : TypeIndex} [ModelData α] : MulAction (AllPerm α) (Tangle α) where
  one_smul t := by
    ext : 1
    · rw [Tangle.smul_set, one_smul]
    · rw [Tangle.smul_support, allPermForget_one, one_smul]
  mul_smul ρ₁ ρ₂ t := by
    ext : 1
    · rw [Tangle.smul_set, Tangle.smul_set, Tangle.smul_set, mul_smul]
    · rw [Tangle.smul_support, Tangle.smul_support, Tangle.smul_support,
        allPermForget_mul, mul_smul]

theorem Tangle.smul_eq {α : TypeIndex} [ModelData α] {ρ : AllPerm α} {t : Tangle α}
    (h : ρᵁ • t.support = t.support) :
    ρ • t = t := by
  have := smul_eq_smul (ρ₁ := ρ) (ρ₂ := 1) (t := t) (by rwa [allPermForget_one, one_smul])
  rwa [one_smul] at this

theorem Tangle.smul_atom_eq_of_mem_support {α : TypeIndex} [ModelData α]
    {ρ₁ ρ₂ : AllPerm α} {t : Tangle α} (h : ρ₁ • t = ρ₂ • t)
    {a : Atom} {A : α ↝ ⊥} (ha : a ∈ (t.support ⇘. A)ᴬ) :
    ρ₁ᵁ A • a = ρ₂ᵁ A • a :=
  Enumeration.eq_of_smul_eq_smul (congr_arg (λ t ↦ (t.support ⇘. A)ᴬ) h) a ha

theorem Tangle.smul_nearLitter_eq_of_mem_support {α : TypeIndex} [ModelData α]
    {ρ₁ ρ₂ : AllPerm α} {t : Tangle α} (h : ρ₁ • t = ρ₂ • t)
    {N : NearLitter} {A : α ↝ ⊥} (hN : N ∈ (t.support ⇘. A)ᴺ) :
    ρ₁ᵁ A • N = ρ₂ᵁ A • N :=
  Enumeration.eq_of_smul_eq_smul (congr_arg (λ t ↦ (t.support ⇘. A)ᴺ) h) N hN

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
  allPermForget_injective' _ _ h := congr_fun h Path.nil
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
