import ConNF.Setup.PathEnumeration

/-!
# Supports

In this file, we define the notion of a support.

## Main declarations

* `ConNF.BaseSupport`: The type of supports of atoms.
* `ConNF.Support`: The type of supports of objects of arbitrary type indices.
-/

universe u

open Cardinal

namespace ConNF

variable [Params.{u}]

/-!
## Base supports
-/

structure BaseSupport where
  atoms : Enumeration Atom
  nearLitters : Enumeration NearLitter

namespace BaseSupport

instance : SuperA BaseSupport (Enumeration Atom) where
  superA := atoms

instance : SuperN BaseSupport (Enumeration NearLitter) where
  superN := nearLitters

theorem atoms_congr {S T : BaseSupport} (h : S = T) :
    Sᴬ = Tᴬ :=
  h ▸ rfl

theorem nearLitters_congr {S T : BaseSupport} (h : S = T) :
    Sᴺ = Tᴺ :=
  h ▸ rfl

@[ext]
theorem ext {S T : BaseSupport} (h₁ : Sᴬ = Tᴬ) (h₂ : Sᴺ = Tᴺ) : S = T := by
  obtain ⟨SA, SN⟩ := S
  obtain ⟨TA, TN⟩ := T
  cases h₁
  cases h₂
  rfl

end BaseSupport

def baseSupportEquiv : BaseSupport ≃ Enumeration Atom × Enumeration NearLitter where
  toFun S := (Sᴬ, Sᴺ)
  invFun S := ⟨S.1, S.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_baseSupport : #BaseSupport = #μ := by
  rw [Cardinal.eq.mpr ⟨baseSupportEquiv⟩, mk_prod, lift_id, lift_id,
    card_enumeration_eq card_atom, card_enumeration_eq card_nearLitter, mul_eq_self aleph0_lt_μ.le]

/-!
## Structural supports
-/

structure Support (α : TypeIndex) where
  atoms : Enumeration (α ↝ ⊥ × Atom)
  nearLitters : Enumeration (α ↝ ⊥ × NearLitter)

namespace Support

variable {α β : TypeIndex}

instance : SuperA (Support α) (Enumeration (α ↝ ⊥ × Atom)) where
  superA := atoms

instance : SuperN (Support α) (Enumeration (α ↝ ⊥ × NearLitter)) where
  superN := nearLitters

@[simp]
theorem mk_atoms (E : Enumeration (α ↝ ⊥ × Atom)) (F : Enumeration (α ↝ ⊥ × NearLitter)) :
    (⟨E, F⟩ : Support α)ᴬ = E :=
  rfl

@[simp]
theorem mk_nearLitters (E : Enumeration (α ↝ ⊥ × Atom)) (F : Enumeration (α ↝ ⊥ × NearLitter)) :
    (⟨E, F⟩ : Support α)ᴺ = F :=
  rfl

instance : Derivative (Support α) (Support β) α β where
  deriv S A := ⟨Sᴬ ⇘ A, Sᴺ ⇘ A⟩

instance : Coderivative (Support β) (Support α) α β where
  coderiv S A := ⟨Sᴬ ⇗ A, Sᴺ ⇗ A⟩

instance : BotDerivative (Support α) BaseSupport α where
  botDeriv S A := ⟨Sᴬ ⇘. A, Sᴺ ⇘. A⟩
  botSderiv S := ⟨Sᴬ ↘., Sᴺ ↘.⟩
  botDeriv_single S h := by dsimp only; rw [botDeriv_single, botDeriv_single]

theorem ext' {S T : Support α} (h₁ : Sᴬ = Tᴬ) (h₂ : Sᴺ = Tᴺ) : S = T := by
  obtain ⟨SA, SN⟩ := S
  obtain ⟨TA, TN⟩ := T
  cases h₁
  cases h₂
  rfl

@[ext]
theorem ext {S T : Support α} (h : ∀ A, S ⇘. A = T ⇘. A) : S = T := by
  obtain ⟨SA, SN⟩ := S
  obtain ⟨TA, TN⟩ := T
  rw [mk.injEq]
  constructor
  · apply Enumeration.ext_path
    intro A
    exact BaseSupport.atoms_congr (h A)
  · apply Enumeration.ext_path
    intro A
    exact BaseSupport.nearLitters_congr (h A)

instance {α : TypeIndex} : SMul (StrPerm α) (Support α) where
  smul π S := ⟨π • Sᴬ, π • Sᴺ⟩

@[simp]
theorem smul_atoms {α : TypeIndex} (π : StrPerm α) (S : Support α) :
    (π • S)ᴬ = π • Sᴬ :=
  rfl

@[simp]
theorem smul_nearLitters {α : TypeIndex} (π : StrPerm α) (S : Support α) :
    (π • S)ᴺ = π • Sᴺ :=
  rfl

@[simp]
theorem smul_atoms_eq_of_smul_eq {α : TypeIndex} {π : StrPerm α} {S : Support α}
    (h : π • S = S) :
    π • Sᴬ = Sᴬ := by
  rw [← smul_atoms, h]

@[simp]
theorem smul_nearLitters_eq_of_smul_eq {α : TypeIndex} {π : StrPerm α} {S : Support α}
    (h : π • S = S) :
    π • Sᴺ = Sᴺ := by
  rw [← smul_nearLitters, h]

instance {α : TypeIndex} : MulAction (StrPerm α) (Support α) where
  one_smul S := by
    apply ext'
    · rw [smul_atoms, one_smul]
    · rw [smul_nearLitters, one_smul]
  mul_smul π₁ π₂ S := by
    apply ext'
    · rw [smul_atoms, smul_atoms, smul_atoms, mul_smul]
    · rw [smul_nearLitters, smul_nearLitters, smul_nearLitters, mul_smul]

end Support

def supportEquiv {α : TypeIndex} : Support α ≃
    Enumeration (α ↝ ⊥ × Atom) × Enumeration (α ↝ ⊥ × NearLitter) where
  toFun S := (Sᴬ, Sᴺ)
  invFun S := ⟨S.1, S.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_support {α : TypeIndex} : #(Support α) = #μ := by
  rw [Cardinal.eq.mpr ⟨supportEquiv⟩, mk_prod, lift_id, lift_id,
    card_enumeration_eq, card_enumeration_eq, mul_eq_self aleph0_lt_μ.le]
  · rw [mk_prod, lift_id, lift_id, card_nearLitter,
      mul_eq_right aleph0_lt_μ.le (card_path_lt' α ⊥).le (card_path_ne_zero α)]
  · rw [mk_prod, lift_id, lift_id, card_atom,
      mul_eq_right aleph0_lt_μ.le (card_path_lt' α ⊥).le (card_path_ne_zero α)]

end ConNF
