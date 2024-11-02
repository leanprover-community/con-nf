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

@[simp]
theorem mk_atoms {a : Enumeration Atom} {N : Enumeration NearLitter} :
    (BaseSupport.mk a N)ᴬ = a :=
  rfl

@[simp]
theorem mk_nearLitters {a : Enumeration Atom} {N : Enumeration NearLitter} :
    (BaseSupport.mk a N)ᴺ = N :=
  rfl

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

instance : SMul BasePerm BaseSupport where
  smul π S := ⟨π • Sᴬ, π • Sᴺ⟩

@[simp]
theorem smul_atoms (π : BasePerm) (S : BaseSupport) :
    (π • S)ᴬ = π • Sᴬ :=
  rfl

@[simp]
theorem smul_nearLitters (π : BasePerm) (S : BaseSupport) :
    (π • S)ᴺ = π • Sᴺ :=
  rfl

@[simp]
theorem smul_atoms_eq_of_smul_eq {π : BasePerm} {S : BaseSupport}
    (h : π • S = S) :
    π • Sᴬ = Sᴬ := by
  rw [← smul_atoms, h]

@[simp]
theorem smul_nearLitters_eq_of_smul_eq {π : BasePerm} {S : BaseSupport}
    (h : π • S = S) :
    π • Sᴺ = Sᴺ := by
  rw [← smul_nearLitters, h]

instance : MulAction BasePerm BaseSupport where
  one_smul S := by
    apply ext
    · rw [smul_atoms, one_smul]
    · rw [smul_nearLitters, one_smul]
  mul_smul π₁ π₂ S := by
    apply ext
    · rw [smul_atoms, smul_atoms, smul_atoms, mul_smul]
    · rw [smul_nearLitters, smul_nearLitters, smul_nearLitters, mul_smul]

theorem smul_eq_smul_iff (π₁ π₂ : BasePerm) (S : BaseSupport) :
    π₁ • S = π₂ • S ↔ (∀ a ∈ Sᴬ, π₁ • a = π₂ • a) ∧ (∀ N ∈ Sᴺ, π₁ • N = π₂ • N) := by
  constructor
  · intro h
    constructor
    · rintro a ⟨i, ha⟩
      have := congr_arg (·ᴬ.rel i (π₁ • a)) h
      simp only [smul_atoms, Enumeration.smul_rel, inv_smul_smul, eq_iff_iff] at this
      have := Sᴬ.rel_coinjective.coinjective ha (this.mp ha)
      rw [eq_inv_smul_iff] at this
      rw [this]
    · rintro N ⟨i, hN⟩
      have := congr_arg (·ᴺ.rel i (π₁ • N)) h
      simp only [smul_nearLitters, Enumeration.smul_rel, inv_smul_smul, eq_iff_iff] at this
      have := Sᴺ.rel_coinjective.coinjective hN (this.mp hN)
      rw [eq_inv_smul_iff] at this
      rw [this]
  · intro h
    ext : 2
    · rfl
    · ext i a : 3
      rw [smul_atoms, smul_atoms, Enumeration.smul_rel, Enumeration.smul_rel]
      constructor
      · intro ha
        have := h.1 _ ⟨i, ha⟩
        rw [smul_inv_smul, ← inv_smul_eq_iff] at this
        rwa [this]
      · intro ha
        have := h.1 _ ⟨i, ha⟩
        rw [smul_inv_smul, smul_eq_iff_eq_inv_smul] at this
        rwa [← this]
    · rfl
    · ext i a : 3
      rw [smul_nearLitters, smul_nearLitters, Enumeration.smul_rel, Enumeration.smul_rel]
      constructor
      · intro hN
        have := h.2 _ ⟨i, hN⟩
        rw [smul_inv_smul, ← inv_smul_eq_iff] at this
        rwa [this]
      · intro hN
        have := h.2 _ ⟨i, hN⟩
        rw [smul_inv_smul, smul_eq_iff_eq_inv_smul] at this
        rwa [← this]

theorem smul_eq_iff (π : BasePerm) (S : BaseSupport) :
    π • S = S ↔ (∀ a ∈ Sᴬ, π • a = a) ∧ (∀ N ∈ Sᴺ, π • N = N) := by
  have := smul_eq_smul_iff π 1 S
  simp only [one_smul] at this
  exact this

noncomputable instance : Add BaseSupport where
  add S T := ⟨Sᴬ + Tᴬ, Sᴺ + Tᴺ⟩

@[simp]
theorem add_atoms (S T : BaseSupport) :
    (S + T)ᴬ = Sᴬ + Tᴬ :=
  rfl

@[simp]
theorem add_nearLitters (S T : BaseSupport) :
    (S + T)ᴺ = Sᴺ + Tᴺ :=
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

@[simp]
theorem deriv_atoms {α β : TypeIndex} (S : Support α) (A : α ↝ β) :
    Sᴬ ⇘ A = (S ⇘ A)ᴬ :=
  rfl

@[simp]
theorem deriv_nearLitters {α β : TypeIndex} (S : Support α) (A : α ↝ β) :
    Sᴺ ⇘ A = (S ⇘ A)ᴺ :=
  rfl

@[simp]
theorem coderiv_atoms {α β : TypeIndex} (S : Support β) (A : α ↝ β) :
    Sᴬ ⇗ A = (S ⇗ A)ᴬ :=
  rfl

@[simp]
theorem coderiv_nearLitters {α β : TypeIndex} (S : Support β) (A : α ↝ β) :
    Sᴺ ⇗ A = (S ⇗ A)ᴺ :=
  rfl

@[simp]
theorem derivBot_atoms {α : TypeIndex} (S : Support α) (A : α ↝ ⊥) :
    Sᴬ ⇘. A = (S ⇘. A)ᴬ :=
  rfl

@[simp]
theorem derivBot_nearLitters {α : TypeIndex} (S : Support α) (A : α ↝ ⊥) :
    Sᴺ ⇘. A = (S ⇘. A)ᴺ :=
  rfl

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

@[simp]
theorem deriv_derivBot {α : TypeIndex} (S : Support α)
    (A : α ↝ β) (B : β ↝ ⊥) :
    S ⇘ A ⇘. B = S ⇘. (A ⇘ B) :=
  rfl

@[simp]
theorem coderiv_deriv_eq {α β : TypeIndex} (S : Support β) (A : α ↝ β) :
    S ⇗ A ⇘ A = S :=
  ext' (Sᴬ.coderiv_deriv_eq A) (Sᴺ.coderiv_deriv_eq A)

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

theorem smul_atoms_eq_of_smul_eq {α : TypeIndex} {π : StrPerm α} {S : Support α}
    (h : π • S = S) :
    π • Sᴬ = Sᴬ := by
  rw [← smul_atoms, h]

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

@[simp]
theorem smul_derivBot {α : TypeIndex} (π : StrPerm α) (S : Support α) (A : α ↝ ⊥) :
    (π • S) ⇘. A = π A • (S ⇘. A) :=
  rfl

theorem smul_eq_smul_iff (π₁ π₂ : StrPerm β) (S : Support β) :
    π₁ • S = π₂ • S ↔
      ∀ A, (∀ a ∈ (S ⇘. A)ᴬ, π₁ A • a = π₂ A • a) ∧ (∀ N ∈ (S ⇘. A)ᴺ, π₁ A • N = π₂ A • N) := by
  constructor
  · intro h A
    have := congr_arg (· ⇘. A) h
    simp only [smul_derivBot, BaseSupport.smul_eq_smul_iff] at this
    exact this
  · intro h
    apply ext
    intro A
    simp only [smul_derivBot, BaseSupport.smul_eq_smul_iff]
    exact h A

theorem smul_eq_iff (π : StrPerm β) (S : Support β) :
    π • S = S ↔ ∀ A, (∀ a ∈ (S ⇘. A)ᴬ, π A • a = a) ∧ (∀ N ∈ (S ⇘. A)ᴺ, π A • N = N) := by
  have := smul_eq_smul_iff π 1 S
  simp only [one_smul, Tree.one_apply] at this
  exact this

noncomputable instance : Add (Support α) where
  add S T := ⟨Sᴬ + Tᴬ, Sᴺ + Tᴺ⟩

@[simp]
theorem add_derivBot (S T : Support α) (A : α ↝ ⊥) :
    (S + T) ⇘. A = (S ⇘. A) + (T ⇘. A) :=
  rfl

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

/-!
## Orders on supports
-/

instance : LE BaseSupport where
  le S T := (∀ a ∈ Sᴬ, a ∈ Tᴬ) ∧ (∀ N ∈ Sᴺ, N ∈ Tᴺ)

instance : Preorder BaseSupport where
  le_refl S := ⟨λ _ ↦ id, λ _ ↦ id⟩
  le_trans S T U h₁ h₂ := ⟨λ a h ↦ h₂.1 _ (h₁.1 a h), λ N h ↦ h₂.2 _ (h₁.2 N h)⟩

theorem BaseSupport.smul_le_smul {S T : BaseSupport} (h : S ≤ T) (π : BasePerm) :
    π • S ≤ π • T := by
  constructor
  · intro a
    exact h.1 (π⁻¹ • a)
  · intro N
    exact h.2 (π⁻¹ • N)

def BaseSupport.Subsupport (S T : BaseSupport) : Prop :=
  Sᴬ.rel ≤ Tᴬ.rel ∧ Sᴺ.rel ≤ Tᴺ.rel

theorem BaseSupport.smul_subsupport_smul {S T : BaseSupport} (h : S.Subsupport T) (π : BasePerm) :
    (π • S).Subsupport (π • T) := by
  constructor
  · intro i a ha
    exact h.1 i _ ha
  · intro i N hN
    exact h.2 i _ hN

instance {α : TypeIndex} : LE (Support α) where
  le S T := ∀ A, S ⇘. A ≤ T ⇘. A

instance {α : TypeIndex} : Preorder (Support α) where
  le_refl S := λ A ↦ le_rfl
  le_trans S T U h₁ h₂ := λ A ↦ (h₁ A).trans (h₂ A)

theorem Support.smul_le_smul {α : TypeIndex} {S T : Support α} (h : S ≤ T) (π : StrPerm α) :
    π • S ≤ π • T :=
  λ A ↦ BaseSupport.smul_le_smul (h A) (π A)

theorem le_add_right {α : TypeIndex} {S T : Support α} :
    S ≤ S + T := by
  intro A
  constructor
  · intro a ha
    simp only [Support.add_derivBot, BaseSupport.add_atoms, Enumeration.mem_add_iff]
    exact Or.inl ha
  · intro N hN
    simp only [Support.add_derivBot, BaseSupport.add_nearLitters, Enumeration.mem_add_iff]
    exact Or.inl hN

theorem le_add_left {α : TypeIndex} {S T : Support α} :
    S ≤ T + S := by
  intro A
  constructor
  · intro a ha
    simp only [Support.add_derivBot, BaseSupport.add_atoms, Enumeration.mem_add_iff]
    exact Or.inr ha
  · intro N hN
    simp only [Support.add_derivBot, BaseSupport.add_nearLitters, Enumeration.mem_add_iff]
    exact Or.inr hN

def Support.Subsupport {α : TypeIndex} (S T : Support α) : Prop :=
  ∀ A, (S ⇘. A).Subsupport (T ⇘. A)

theorem Support.smul_subsupport_smul {α : TypeIndex} {S T : Support α}
    (h : S.Subsupport T) (π : StrPerm α) :
    (π • S).Subsupport (π • T) :=
  λ A ↦ BaseSupport.smul_subsupport_smul (h A) (π A)

theorem subsupport_add {α : TypeIndex} {S T : Support α} :
    S.Subsupport (S + T) := by
  intro A
  constructor
  · intro i a ha
    simp only [Support.add_derivBot, BaseSupport.add_atoms, Enumeration.rel_add_iff]
    exact Or.inl ha
  · intro i N hN
    simp only [Support.add_derivBot, BaseSupport.add_atoms, Enumeration.rel_add_iff]
    exact Or.inl hN

theorem smul_eq_of_subsupport {α : TypeIndex} {S T : Support α} {π : StrPerm α}
    (h₁ : S.Subsupport T) (h₂ : S.Subsupport (π • T)) :
    π • S = S := by
  rw [Support.smul_eq_iff]
  intro A
  constructor
  · rintro a ⟨i, hi⟩
    have hi₁ := (h₁ A).1 i a hi
    have hi₂ := (h₂ A).1 i a hi
    have := (T ⇘. A)ᴬ.rel_coinjective.coinjective hi₁ hi₂
    dsimp only at this
    rwa [smul_eq_iff_eq_inv_smul]
  · rintro N ⟨i, hi⟩
    have hi₁ := (h₁ A).2 i N hi
    have hi₂ := (h₂ A).2 i N hi
    have := (T ⇘. A)ᴺ.rel_coinjective.coinjective hi₁ hi₂
    dsimp only at this
    rwa [smul_eq_iff_eq_inv_smul]

end ConNF
