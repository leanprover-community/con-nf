import Mathlib.GroupTheory.GroupAction.Sum
import Mathlib.GroupTheory.GroupAction.Support
import ConNF.Structural.StructPerm
import ConNF.Structural.Enumeration

/-!
# Supports

In this file, we define support conditions and supports.

## Main declarations

* `ConNF.SupportCondition`: The type of support conditions.
* `ConNF.Support`: The type of small supports made of support conditions.
-/

open Cardinal Equiv Sum

open scoped Cardinal Pointwise

universe u

namespace ConNF

variable [Params.{u}] {α : TypeIndex}

/-- A *support condition* is an extended type index together with an atom or a near-litter.
This represents an object in the base type (the atom or near-litter) together with the path
detailing how we descend from type `α` to type `⊥` by looking at elements of elements and so on
in the model. -/
@[ext]
structure SupportCondition (α : TypeIndex) : Type u
    where
  path : ExtendedIndex α
  value : Atom ⊕ NearLitter

def supportCondition_equiv : SupportCondition α ≃ ExtendedIndex α × (Atom ⊕ NearLitter)
    where
  toFun c := ⟨c.path, c.value⟩
  invFun c := ⟨c.1, c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- There are `μ` support conditions. -/
@[simp]
theorem mk_supportCondition (α : TypeIndex) : #(SupportCondition α) = #μ := by
  rw [mk_congr supportCondition_equiv]
  simp only [SupportCondition, mk_prod, mk_sum, mk_atom, lift_id, mk_nearLitter]
  rw [add_eq_left (Params.κ_isRegular.aleph0_le.trans Params.κ_lt_μ.le) le_rfl]
  exact mul_eq_right
    (Params.κ_isRegular.aleph0_le.trans Params.κ_lt_μ.le)
    (le_trans (mk_extendedIndex α) <| le_of_lt <| lt_trans Params.Λ_lt_κ Params.κ_lt_μ)
    (mk_ne_zero _)

namespace StructPerm

variable {π π' : StructPerm α} {c : SupportCondition α}

/-- Structural permutations act on support conditions by following the derivative given in the
condition. -/
instance : MulAction (StructPerm α) (SupportCondition α)
    where
  smul π c := ⟨c.path, π c.path • c.value⟩
  one_smul := by rintro ⟨A, a | N⟩ <;> rfl
  mul_smul _ _ := by rintro ⟨A, a | N⟩ <;> rfl

/-!
We have a form of the next three lemmas for `StructPerm`, `NearLitterPerm`,
`Allowable`, and `NewAllowable`.
-/

theorem smul_supportCondition :
    π • c = ⟨c.path, π c.path • c.value⟩ :=
  rfl

@[simp]
theorem smul_supportCondition_eq_iff :
    π • c = c ↔ π c.path • c.value = c.value := by
  obtain ⟨A, x⟩ := c
  simp only [smul_supportCondition, SupportCondition.mk.injEq, true_and]

@[simp]
theorem smul_supportCondition_eq_smul_iff :
    π • c = π' • c ↔ π c.path • c.value = π' c.path • c.value := by
  obtain ⟨A, x⟩ := c
  simp only [smul_supportCondition, SupportCondition.mk.injEq, true_and]

end StructPerm

namespace NearLitterPerm

variable {π π' : NearLitterPerm} {c : SupportCondition ⊥}

instance : MulAction NearLitterPerm (SupportCondition ⊥)
    where
  smul π c := ⟨c.path, π • c.value⟩
  one_smul := by rintro ⟨A, a | N⟩ <;> rfl
  mul_smul _ _ := by rintro ⟨A, a | N⟩ <;> rfl

theorem smul_supportCondition :
    π • c = ⟨c.path, π • c.value⟩ :=
  rfl

@[simp]
theorem smul_supportCondition_eq_iff :
    π • c = c ↔ π • c.value = c.value := by
  obtain ⟨A, x⟩ := c
  simp only [smul_supportCondition, SupportCondition.mk.injEq, true_and]

@[simp]
theorem smul_supportCondition_eq_smul_iff :
    π • c = π' • c ↔ π • c.value = π' • c.value := by
  obtain ⟨A, x⟩ := c
  simp only [smul_supportCondition, SupportCondition.mk.injEq, true_and]

end NearLitterPerm

/-- A *support* is a function from an initial segment of κ to the type of support conditions,
such that if `N₁, N₂` are near-litters near the same litter, any atoms in their symmetric difference
are included in the enumeration. -/
@[ext]
structure Support (α : TypeIndex) where
  enum : Enumeration (SupportCondition α)
  mem_of_mem_symmDiff' (A : ExtendedIndex α) (N₁ N₂ : NearLitter) (a : Atom) :
    N₁.1 = N₂.1 → a ∈ (N₁ : Set Atom) ∆ N₂ →
    ⟨A, inr N₁⟩ ∈ enum → ⟨A, inr N₂⟩ ∈ enum → ⟨A, inl a⟩ ∈ enum

def Support.max (S : Support α) : κ :=
  S.enum.max

def Support.f (S : Support α) : (i : κ) → i < S.max → SupportCondition α :=
  S.enum.f

instance : CoeTC (Support α) (Set (SupportCondition α)) where
  coe S := S.enum

instance : Membership (SupportCondition α) (Support α) where
  mem c S := c ∈ S.enum

theorem Support.mem_of_mem_symmDiff (S : Support α) (A : ExtendedIndex α)
    (N₁ N₂ : NearLitter) (a : Atom) :
    N₁.1 = N₂.1 → a ∈ (N₁ : Set Atom) ∆ N₂ →
    ⟨A, inr N₁⟩ ∈ S → ⟨A, inr N₂⟩ ∈ S → ⟨A, inl a⟩ ∈ S :=
  S.mem_of_mem_symmDiff' A N₁ N₂ a

theorem Support.small (S : Support α) : Small (S : Set (SupportCondition α)) :=
  S.enum.small

@[simp]
theorem Support.mk_f (E : Enumeration (SupportCondition α)) (h) :
    (Support.mk E h).f = E.f :=
  rfl

@[simp]
theorem Support.mem_mk (E : Enumeration (SupportCondition α)) (h) (c : SupportCondition α) :
    c ∈ Support.mk E h ↔ c ∈ E :=
  Iff.rfl

@[simp]
theorem Support.mem_iff (c : SupportCondition α) (S : Support α) :
    c ∈ S ↔ ∃ i, ∃ (h : i < S.max), c = S.f i h :=
  Iff.rfl

theorem Support.mem_of_mem_symmDiff_smul (S : Support α) (π : StructPerm α) (A : ExtendedIndex α)
    (N₁ N₂ : NearLitter) (a : Atom) :
    N₁.1 = N₂.1 → a ∈ (N₁ : Set Atom) ∆ N₂ →
    ⟨A, inr N₁⟩ ∈ π • S.enum → ⟨A, inr N₂⟩ ∈ π • S.enum → ⟨A, inl a⟩ ∈ π • S.enum := by
  intro hN ha hN₁ hN₂
  have := S.mem_of_mem_symmDiff A ((π A)⁻¹ • N₁) ((π A)⁻¹ • N₂) ((π A)⁻¹ • a) ?_ ?_ ?_ ?_
  · obtain ⟨i, hi, h⟩ := this
    refine ⟨i, hi, ?_⟩
    rw [Enumeration.smul_f, ← inv_smul_eq_iff]
    exact h
  · simp only [NearLitterPerm.smul_nearLitter_fst, smul_left_cancel_iff]
    exact hN
  · rw [NearLitterPerm.smul_nearLitter_coe, NearLitterPerm.smul_nearLitter_coe,
      ← Set.smul_set_symmDiff, Set.smul_mem_smul_set_iff]
    exact ha
  · obtain ⟨i, hi, h⟩ := hN₁
    refine ⟨i, hi, ?_⟩
    rw [Enumeration.smul_f, ← inv_smul_eq_iff] at h
    exact h
  · obtain ⟨i, hi, h⟩ := hN₂
    refine ⟨i, hi, ?_⟩
    rw [Enumeration.smul_f, ← inv_smul_eq_iff] at h
    exact h

instance : MulAction (StructPerm α) (Support α) where
  smul π S := ⟨π • S.enum, S.mem_of_mem_symmDiff_smul π⟩
  one_smul S := by
    ext : 1
    exact one_smul _ S.enum
  mul_smul π₁ π₂ S := by
    ext : 1
    exact mul_smul π₁ π₂ S.enum

@[simp]
theorem Support.smul_max (π : StructPerm α) (S : Support α) :
    (π • S).max = S.max :=
  rfl

@[simp]
theorem Support.smul_f (π : StructPerm α) (S : Support α) (i : κ) (hi : i < S.max) :
    (π • S).f i hi = π • S.f i hi :=
  rfl

@[simp]
theorem Support.smul_coe (π : StructPerm α) (S : Support α) :
    (π • S : Support α) = π • (S : Set (SupportCondition α)) :=
  Enumeration.smul_coe _ _

theorem Support.smul_mem_smul {S : Support α} {c : SupportCondition α}
    (h : c ∈ S) (π : StructPerm α) : π • c ∈ π • S :=
  Enumeration.smul_mem_smul h π

theorem Support.smul_eq_of_smul_eq {S : Support α} {π : StructPerm α}
    (hS : π • S = S) {c : SupportCondition α} (hc : c ∈ S) : π • c = c :=
  Enumeration.smul_eq_of_smul_eq (congr_arg Support.enum hS) hc

def Support.singleton (c : SupportCondition α) : Support α where
  enum := ⟨1, fun _ _ => c⟩
  mem_of_mem_symmDiff' := by
    intro _ N₁ N₂ b _ hb hN₁ hN₂
    simp only [Enumeration.mem_iff, κ_lt_one_iff, exists_prop, exists_eq_left] at hN₁ hN₂
    rw [← hN₂] at hN₁
    simp only [SupportCondition.mk.injEq, inr.injEq, true_and] at hN₁
    subst hN₁
    cases hb with
    | inl hb => cases hb.2 hb.1
    | inr hb => cases hb.2 hb.1

@[simp]
theorem Support.singleton_enum (c : SupportCondition α) :
    (Support.singleton c).enum = ⟨1, fun _ _ => c⟩ :=
  rfl

@[simp]
theorem Support.mem_singleton_iff (c d : SupportCondition α) : c ∈ Support.singleton d ↔ c = d := by
  unfold singleton
  simp only [mem_mk, Enumeration.mem_iff, κ_lt_one_iff, exists_prop, exists_eq_left]

@[simp]
theorem Support.singleton_injective :
    Function.Injective (Support.singleton : SupportCondition α → Support α) := by
  unfold singleton
  intro c d h
  simp only [mk.injEq, Enumeration.mk.injEq, heq_eq_eq, true_and] at h
  exact congr_fun₂ h 0 κ_zero_lt_one

/-- There are exactly `μ` supports. -/
@[simp]
theorem mk_support : #(Support α) = #μ := by
  refine le_antisymm ?_ ?_
  · rw [← mk_enumeration (mk_supportCondition α)]
    refine ⟨⟨Support.enum, ?_⟩⟩
    intro S₁ S₂ h
    ext : 1
    exact h
  · rw [← mk_atom]
    refine ⟨⟨fun a => Support.singleton ⟨default, inl a⟩, ?_⟩⟩
    intro a₁ a₂ h
    have := Support.singleton_injective h
    simp only [SupportCondition.mk.injEq, inl.injEq, true_and] at this
    exact this

end ConNF
