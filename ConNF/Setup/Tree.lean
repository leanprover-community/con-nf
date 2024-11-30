import ConNF.Setup.Path

/-!
# Trees

In this file, we define the notion of a tree on a type.

## Main declarations

* `ConNF.Tree`: The type family of trees parametrised by a given type.
-/

universe u

open Cardinal

namespace ConNF

variable [Params.{u}] {X Y : Type _} {α β γ : TypeIndex}

/-- An `α`-tree of `X` associates an object of type `X` to each path `α ↝ ⊥`. -/
def Tree (X : Type _) (α : TypeIndex) :=
  (α ↝ ⊥) → X

namespace Tree

instance : Derivative (Tree X α) (Tree X β) α β where
  deriv T A B := T (A ⇘ B)

@[simp]
theorem deriv_apply (T : Tree X α) (A : α ↝ β) (B : β ↝ ⊥) :
    (T ⇘ A) B = T (A ⇘ B) :=
  rfl

@[simp]
theorem deriv_nil (T : Tree X α) :
    T ⇘ .nil = T := by
  funext A
  rw [deriv_apply, Path.nil_deriv]

theorem deriv_deriv (T : Tree X α) (A : α ↝ β) (B : β ↝ γ) :
    T ⇘ A ⇘ B = T ⇘ (A ⇘ B) := by
  funext C
  simp only [deriv_apply, Path.deriv_assoc]

theorem deriv_sderiv (T : Tree X α) (A : α ↝ β) (h : γ < β) :
    T ⇘ A ↘ h = T ⇘ (A ↘ h) := by
  rw [← Derivative.deriv_single, ← Derivative.deriv_single, deriv_deriv]

@[simp]
theorem sderiv_apply (T : Tree X α) (h : β < α) (B : β ↝ ⊥) :
    (T ↘ h) B = T (B ↗ h) :=
  rfl

instance : BotDerivative (Tree X α) X α where
  botDeriv T A := T A
  botSderiv T := T <| Path.nil ↘.
  botDeriv_single T h := by
    cases α using WithBot.recBotCoe with
      | bot => cases lt_irrefl ⊥ h
      | coe => rfl

@[simp]
theorem botDeriv_eq (T : Tree X α) (A : α ↝ ⊥) :
    T ⇘. A = T A :=
  rfl

theorem botSderiv_eq (T : Tree X α) :
    T ↘. = T (Path.nil ↘.) :=
  rfl

/-- The group structure on the type of `α`-trees of `X` is given by "branchwise" multiplication,
given by `Pi.group`. -/
instance group [Group X] : Group (Tree X α) :=
  Pi.group

@[simp]
theorem one_apply [Group X] (A : α ↝ ⊥) :
    (1 : Tree X α) A = 1 :=
  rfl

@[simp]
theorem one_deriv [Group X] (A : α ↝ β) :
    (1 : Tree X α) ⇘ A = 1 :=
  rfl

@[simp]
theorem one_sderiv [Group X] (h : β < α) :
    (1 : Tree X α) ↘ h = 1 :=
  rfl

@[simp]
theorem one_sderivBot [Group X] :
    (1 : Tree X α) ↘. = 1 :=
  rfl

@[simp]
theorem mul_apply [Group X] (T₁ T₂ : Tree X α) (A : α ↝ ⊥) :
    (T₁ * T₂) A = T₁ A * T₂ A :=
  rfl

@[simp]
theorem mul_deriv [Group X] (T₁ T₂ : Tree X α) (A : α ↝ β) :
    (T₁ * T₂) ⇘ A = T₁ ⇘ A * T₂ ⇘ A :=
  rfl

@[simp]
theorem mul_sderiv [Group X] (T₁ T₂ : Tree X α) (h : β < α) :
    (T₁ * T₂) ↘ h = T₁ ↘ h * T₂ ↘ h :=
  rfl

@[simp]
theorem mul_sderivBot [Group X] (T₁ T₂ : Tree X α) :
    (T₁ * T₂) ↘. = T₁ ↘. * T₂ ↘. :=
  rfl

@[simp]
theorem inv_apply [Group X] (T : Tree X α) (A : α ↝ ⊥) :
    T⁻¹ A = (T A)⁻¹ :=
  rfl

@[simp]
theorem inv_deriv [Group X] (T : Tree X α) (A : α ↝ β) :
    T⁻¹ ⇘ A = (T ⇘ A)⁻¹ :=
  rfl

@[simp]
theorem inv_sderiv [Group X] (T : Tree X α) (h : β < α) :
    T⁻¹ ↘ h = (T ↘ h)⁻¹ :=
  rfl

@[simp]
theorem inv_sderivBot [Group X] (T : Tree X α) :
    T⁻¹ ↘. = (T ↘.)⁻¹ :=
  rfl

@[simp]
theorem npow_apply [Group X] (T : Tree X α) (A : α ↝ ⊥) (n : ℕ) :
    (T ^ n) A = (T A) ^ n :=
  rfl

@[simp]
theorem zpow_apply [Group X] (T : Tree X α) (A : α ↝ ⊥) (n : ℤ) :
    (T ^ n) A = (T A) ^ n :=
  rfl

/-- The partial order on the type of `α`-trees of `X` is given by "branchwise" comparison. -/
instance partialOrder [PartialOrder X] : PartialOrder (Tree X α) :=
  Pi.partialOrder

theorem le_iff [PartialOrder X] (T₁ T₂ : Tree X α) :
    T₁ ≤ T₂ ↔ ∀ A, T₁ A ≤ T₂ A :=
  Iff.rfl

end Tree

/-!
## Cardinality bounds on trees
-/

theorem card_tree_le (h : #X ≤ #μ) : #(Tree X α) ≤ #μ := by
  rw [Tree, ← power_def]
  apply (power_le_power_right h).trans
  exact pow_le_of_lt_ord_cof μ_isStrongLimit (card_path_lt α ⊥)

theorem card_tree_lt (h : #X < #μ) : #(Tree X α) < #μ := by
  rw [Tree, ← power_def]
  exact pow_lt_of_lt μ_isStrongLimit h ((card_path_lt α ⊥).trans_le (Ordinal.cof_ord_le #μ))

theorem card_tree_eq (h : #X = #μ) : #(Tree X α) = #μ := by
  apply le_antisymm
  · exact card_tree_le h.le
  · rw [← h]
    apply mk_le_of_injective (f := λ x _ ↦ x)
    intro x y h
    exact congr_fun h (Path.nil ↘.)

end ConNF
