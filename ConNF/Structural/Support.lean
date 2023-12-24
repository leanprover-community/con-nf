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

/-- `S` is a *completion* of an enumeration of support conditions `E` if it extends `E`,
and every support condition in the extension is an atom contained in the symmetric difference of
two near-litters in `E`. -/
structure Support.IsCompletion (S : Support α) (E : Enumeration (SupportCondition α)) : Prop where
  le : E ≤ S.enum
  eq_atom (i : κ) (hi₁ : i < S.max) (hi₂ : E.max ≤ i) :
    ∃ A : ExtendedIndex α, ∃ a : Atom, ∃ N₁ N₂ : NearLitter,
    N₁.1 = N₂.1 ∧ a ∈ (N₁ : Set Atom) ∆ N₂ ∧
    ⟨A, inr N₁⟩ ∈ E ∧ ⟨A, inr N₂⟩ ∈ E ∧ S.f i hi₁ = ⟨A, inl a⟩

theorem Support.IsCompletion.smul {S : Support α} {E : Enumeration (SupportCondition α)}
    (h : S.IsCompletion E) (π : StructPerm α) : (π • S).IsCompletion (π • E) := by
  constructor
  · exact Enumeration.smul_le_smul h.le π
  · intro i hi₁ hi₂
    obtain ⟨A, a, N₁, N₂, hN, ha, hN₁, hN₂, h⟩ := h.eq_atom i hi₁ hi₂
    refine ⟨A, π A • a, π A • N₁, π A • N₂, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [NearLitterPerm.smul_nearLitter_fst, smul_left_cancel_iff]
      exact hN
    · rw [NearLitterPerm.smul_nearLitter_coe, NearLitterPerm.smul_nearLitter_coe,
        ← Set.smul_set_symmDiff, Set.smul_mem_smul_set_iff]
      exact ha
    · obtain ⟨i, hi, h⟩ := hN₁
      refine ⟨i, hi, ?_⟩
      rw [Enumeration.smul_f, ← h]
      rfl
    · obtain ⟨i, hi, h⟩ := hN₂
      refine ⟨i, hi, ?_⟩
      rw [Enumeration.smul_f, ← h]
      rfl
    · rw [smul_f, h]
      rfl

/-- The set of support conditions that we need to add to `s` to make it a support. -/
def completionToAdd (s : Set (SupportCondition α)) : Set (SupportCondition α) :=
  {x | ∃ N₁ N₂ : NearLitter, N₁.1 = N₂.1 ∧ ∃ a : Atom, x.2 = inl a ∧ a ∈ (N₁ : Set Atom) ∆ N₂ ∧
    ⟨x.1, inr N₁⟩ ∈ s ∧ ⟨x.1, inr N₂⟩ ∈ s}

theorem nearLitter_not_mem_completionToAdd (A : ExtendedIndex α) (N : NearLitter)
    (s : Set (SupportCondition α)) : ⟨A, inr N⟩ ∉ completionToAdd s := by
  rintro ⟨_, _, _, a, h, _⟩
  cases h

def completionToAdd' (s : Set (SupportCondition α)) (A : ExtendedIndex α) : Set Atom :=
  ⋃ (N₁ : NearLitter) (_ : N₁ ∈ (fun N => ⟨A, inr N⟩) ⁻¹' s)
    (N₂ : NearLitter) (_ : N₂ ∈ (fun N => ⟨A, inr N⟩) ⁻¹' s)
    (_ : N₁.1 = N₂.1),
  (N₁ : Set Atom) ∆ N₂

theorem completionToAdd'_small (s : Set (SupportCondition α)) (hs : Small s) (A : ExtendedIndex α) :
    Small (completionToAdd' s A) := by
  have : Function.Injective (fun N => (⟨A, inr N⟩ : SupportCondition α))
  · intro N₁ N₂ h
    simp only [SupportCondition.mk.injEq, inr.injEq, true_and] at h
    exact h
  refine Small.bUnion (Small.preimage this hs) (fun N₁ _ => ?_)
  refine Small.bUnion (Small.preimage this hs) (fun N₂ _ => ?_)
  refine small_iUnion_Prop (fun h => ?_)
  refine N₁.2.prop.symm.trans ?_
  rw [h]
  exact N₂.2.prop

theorem completionToAdd_eq_completionToAdd' (s : Set (SupportCondition α)) :
    completionToAdd s = ⋃ (A : ExtendedIndex α), (⟨A, inl ·⟩) '' completionToAdd' s A := by
  simp only [completionToAdd, completionToAdd']
  aesop

theorem completionToAdd_small (s : Set (SupportCondition α)) (hs : Small s) :
    Small (completionToAdd s) := by
  rw [completionToAdd_eq_completionToAdd']
  refine small_iUnion ?_ ?_
  · exact (mk_extendedIndex α).trans_lt Params.Λ_lt_κ
  · intro A
    exact Small.image (completionToAdd'_small s hs A)

noncomputable def completeEnum (E : Enumeration (SupportCondition α)) :
    Enumeration (SupportCondition α) :=
  E + Enumeration.ofSet (completionToAdd E) (completionToAdd_small _ E.small)

@[simp]
theorem mem_completeEnum (E : Enumeration (SupportCondition α)) (c : SupportCondition α) :
    c ∈ completeEnum E ↔ c ∈ E ∨ c ∈ completionToAdd E :=
  by rw [completeEnum, Enumeration.mem_add_iff, Enumeration.mem_ofSet_iff]

theorem completeEnum_mem_of_mem_symmDiff (E : Enumeration (SupportCondition α))
    (A : ExtendedIndex α) (N₁ N₂ : NearLitter) (a : Atom) :
    N₁.1 = N₂.1 → a ∈ (N₁ : Set Atom) ∆ N₂ →
    ⟨A, inr N₁⟩ ∈ completeEnum E → ⟨A, inr N₂⟩ ∈ completeEnum E → ⟨A, inl a⟩ ∈ completeEnum E := by
  intro hN ha hN₁ hN₂
  rw [mem_completeEnum] at hN₁ hN₂ ⊢
  obtain (hN₁ | hN₁) := hN₁
  · obtain (hN₂ | hN₂) := hN₂
    · exact Or.inr ⟨N₁, N₂, hN, a, rfl, ha, hN₁, hN₂⟩
    · cases nearLitter_not_mem_completionToAdd A N₂ _ hN₂
  · cases nearLitter_not_mem_completionToAdd A N₁ _ hN₁

/-- Extend an enumeration to a support. -/
noncomputable def Support.complete (E : Enumeration (SupportCondition α)) : Support α where
  enum := completeEnum E
  mem_of_mem_symmDiff' := completeEnum_mem_of_mem_symmDiff E

theorem Support.complete_isCompletion (E : Enumeration (SupportCondition α)) :
    (complete E).IsCompletion E := by
  constructor
  · exact Enumeration.le_add _ _
  · intro i hi₁ hi₂
    have := Enumeration.f_mem _ (i - E.max) (κ_sub_lt hi₁ hi₂)
    rw [← Enumeration.add_f_right hi₁ hi₂, Enumeration.mem_ofSet_iff] at this
    obtain ⟨N₁, N₂, hN, a, ha₁, ha₂, hN₁, hN₂⟩ := this
    refine ⟨_, a, N₁, N₂, hN, ha₂, hN₁, hN₂, ?_⟩
    rw [← ha₁]
    rfl

/-- `S` is a *sum* of `S₁` and `S₂` if it is a completion of `S₁ + S₂`. -/
def Support.IsSum (S S₁ S₂ : Support α) : Prop := S.IsCompletion (S₁.enum + S₂.enum)

theorem Support.IsSum.smul {S S₁ S₂ : Support α} (h : S.IsSum S₁ S₂) (π : StructPerm α) :
    (π • S).IsSum (π • S₁) (π • S₂) := by
  have := IsCompletion.smul h π
  rw [Enumeration.smul_add] at this
  exact this

theorem Support.exists_isSum (S₁ S₂ : Support α) : ∃ S : Support α, S.IsSum S₁ S₂ :=
  ⟨_, Support.complete_isCompletion _⟩

end ConNF
