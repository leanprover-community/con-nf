import Mathlib.GroupTheory.GroupAction.Sum
import Mathlib.GroupTheory.GroupAction.Support
import ConNF.Structural.StructPerm

/-!
# Supports

In this file, we define support conditions and supports.

## Main declarations

* `ConNF.SupportCondition`: The type of support conditions.
* `ConNF.Support`: The type of small supports made of support conditions.
-/

open Cardinal Equiv

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

/-- A *support* is a function from an initial segment of κ to the type of support conditions. -/
@[ext]
structure Support (α : TypeIndex) where
  max : κ
  f : (i : κ) → i < max → SupportCondition α

def Support.carrier (S : Support α) : Set (SupportCondition α) :=
  { c | ∃ i, ∃ (h : i < S.max), c = S.f i h }

instance : CoeTC (Support α) (Set (SupportCondition α)) where
  coe S := S.carrier

instance : Membership (SupportCondition α) (Support α) where
  mem c S := c ∈ S.carrier

@[simp]
theorem Support.mem_carrier_iff (c : SupportCondition α) (S : Support α) :
    c ∈ S.carrier ↔ ∃ i, ∃ (h : i < S.max), c = S.f i h :=
  Iff.rfl

@[simp]
theorem Support.mem_iff (c : SupportCondition α) (S : Support α) :
    c ∈ S ↔ ∃ i, ∃ (h : i < S.max), c = S.f i h :=
  Iff.rfl

theorem Support.carrier_small (S : Support α) : Small S.carrier := by
  refine lt_of_le_of_lt (b := #(Set.Iio S.max)) ?_ (card_typein_lt (· < ·) S.max Params.κ_ord.symm)
  refine mk_le_of_surjective (f := fun x => ⟨S.f x x.prop, x, x.prop, rfl⟩) ?_
  rintro ⟨_, i, h, rfl⟩
  exact ⟨⟨i, h⟩, rfl⟩

theorem Support.small (S : Support α) : Small (S : Set (SupportCondition α)) :=
  S.carrier_small

def supportEquiv : Support α ≃ Σ max : κ, Set.Iio max → SupportCondition α where
  toFun S := ⟨S.max, fun x => S.f x x.prop⟩
  invFun S := ⟨S.1, fun i h => S.2 ⟨i, h⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def funMap (α β : Type _) [LT β] (f : α → β) :
    { S : Set β // #S ≤ #α } × (α → α → Prop) :=
  ⟨⟨Set.range f, mk_range_le⟩, InvImage (· < ·) f⟩

theorem funMap_injective {α β : Type _} [LinearOrder β] [IsWellOrder β (· < ·)] :
    Function.Injective (funMap α β) := by
  intro f g h
  simp only [funMap, Prod.mk.injEq, Subtype.mk.injEq] at h
  suffices : ∀ y : β, ∀ x : α, f x = y → g x = y
  · ext x : 1
    rw [this]
    rfl
  intro y
  refine IsWellFounded.induction (· < ·) (C := fun y => ∀ x : α, f x = y → g x = y) y ?_
  clear y
  rintro y ih x rfl
  obtain ⟨y, h₁⟩ : f x ∈ Set.range g
  · rw [← h.1]
    exact ⟨x, rfl⟩
  rw [← h₁]
  obtain (h₂ | h₂ | h₂) := lt_trichotomy (g x) (g y)
  · obtain ⟨z, h₃⟩ : g x ∈ Set.range f
    · rw [h.1]
      exact ⟨x, rfl⟩
    rw [h₁, ← h₃] at h₂
    have h₄ := ih (f z) h₂ z rfl
    have := congr_fun₂ h.2 z x
    simp only [InvImage, h₂, eq_iff_iff, true_iff] at this
    rw [h₄, h₃] at this
    cases lt_irrefl _ this
  · exact h₂
  · have := congr_fun₂ h.2 y x
    simp only [InvImage, eq_iff_iff] at this
    rw [← this] at h₂
    have := ih (f y) h₂ y rfl
    have := h₂.trans_eq (h₁.symm.trans this)
    cases lt_irrefl _ this

theorem mk_fun_le {α β : Type u} :
    #(α → β) ≤ #({ S : Set β // #S ≤ #α } × (α → α → Prop)) := by
  classical
  obtain ⟨r, hr⟩ := IsWellOrder.subtype_nonempty (σ := β)
  let _ := linearOrderOfSTO r
  exact ⟨⟨funMap α β, funMap_injective⟩⟩

theorem pow_le_of_isStrongLimit' {α β : Type u} [Infinite α] [Infinite β]
    (h₁ : IsStrongLimit #β) (h₂ : #α < (#β).ord.cof) : #β ^ #α ≤ #β := by
  refine le_trans mk_fun_le ?_
  simp only [mk_prod, lift_id, mk_pi, mk_fintype, Fintype.card_prop, Nat.cast_ofNat, prod_const,
    lift_id', lift_two]
  have h₃ : #{ S : Set β // #S ≤ #α } ≤ #β
  · rw [← mk_subset_mk_lt_cof h₁.2]
    refine ⟨⟨fun S => ⟨S, S.prop.trans_lt h₂⟩, ?_⟩⟩
    intro S T h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.coe_injective h
  have h₄ : (2 ^ #α) ^ #α ≤ #β
  · rw [← power_mul, mul_eq_self (Cardinal.infinite_iff.mp inferInstance)]
    refine (h₁.2 _ ?_).le
    exact h₂.trans_le (Ordinal.cof_ord_le #β)
  refine le_trans (mul_le_max _ _) ?_
  simp only [ge_iff_le, le_max_iff, max_le_iff, le_aleph0_iff_subtype_countable, h₃, h₄, and_self,
    aleph0_le_mk]

theorem pow_le_of_isStrongLimit {κ μ : Cardinal.{u}} (h₁ : IsStrongLimit μ) (h₂ : κ < μ.ord.cof) :
    μ ^ κ ≤ μ := by
  by_cases h : κ < ℵ₀
  · exact pow_le h₁.isLimit.aleph0_le h
  · revert h₁ h₂ h
    refine inductionOn₂ κ μ ?_
    intro α β h₁ h₂ h
    have := Cardinal.infinite_iff.mpr (le_of_not_lt h)
    have := Cardinal.infinite_iff.mpr h₁.isLimit.aleph0_le
    exact pow_le_of_isStrongLimit' h₁ h₂

/-- There are exactly `μ` supports. -/
@[simp]
theorem mk_support : #(Support α) = #μ := by
  refine le_antisymm ?_ ?_
  · rw [Cardinal.mk_congr supportEquiv]
    simp only [mk_sigma, mk_pi, mk_supportCondition, prod_const, lift_id]
    refine le_trans (sum_le_sum _ (fun _ => #μ) ?_) ?_
    · intro i
      refine pow_le_of_isStrongLimit Params.μ_isStrongLimit ?_
      refine lt_of_lt_of_le ?_ Params.κ_le_μ_ord_cof
      exact card_typein_lt (· < ·) i Params.κ_ord.symm
    · simp only [sum_const, lift_id, mul_mk_eq_max, ge_iff_le, max_le_iff, le_refl, and_true]
      exact Params.κ_lt_μ.le
  · rw [← mk_atom]
    refine ⟨⟨fun a => ⟨1, fun _ _ => ⟨default, Sum.inl a⟩⟩, ?_⟩⟩
    intro a₁ a₂ h
    simp only [Support.mk.injEq, heq_eq_eq, true_and] at h
    have := congr_fun₂ h 0 κ_zero_lt_one
    simp only [SupportCondition.mk.injEq, Sum.inl.injEq, true_and] at this
    exact this

instance {G : Type _} [SMul G (SupportCondition α)] : SMul G (Support α) where
  smul g S := ⟨S.max, fun i hi => g • S.f i hi⟩

@[simp]
theorem smul_max {G : Type _} [SMul G (SupportCondition α)] (g : G) (S : Support α) :
    (g • S).max = S.max :=
  rfl

@[simp]
theorem smul_f {G : Type _} [SMul G (SupportCondition α)]
    (g : G) (S : Support α) (i : κ) (hi : i < S.max) :
    (g • S).f i hi = g • S.f i hi :=
  rfl

@[simp]
theorem smul_carrier {G : Type _} [SMul G (SupportCondition α)] (g : G) (S : Support α) :
    (g • S).carrier = g • S.carrier := by
  ext x : 1
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨_, ⟨i, hi, rfl⟩, h.symm⟩
  · rintro ⟨_, ⟨i, hi, rfl⟩, h⟩
    exact ⟨i, hi, h.symm⟩

@[simp]
theorem smul_coe {G : Type _} [SMul G (SupportCondition α)] (g : G) (S : Support α) :
    (g • S : Support α) = g • (S : Set (SupportCondition α)) :=
  smul_carrier g S

instance {G : Type _} [Monoid G] [MulAction G (SupportCondition α)] : MulAction G (Support α) where
  one_smul := by
    rintro ⟨i, f⟩
    ext
    · rfl
    · refine heq_of_eq (funext₂ ?_)
      intro j hj
      simp only [smul_f, one_smul]
  mul_smul g h := by
    rintro ⟨i, f⟩
    ext
    · rfl
    · refine heq_of_eq (funext₂ ?_)
      intro j hj
      simp only [smul_f, mul_smul]

/-- Note: In the paper, the sum of supports requires an additional step of closing over atoms in
certain intersections of near-litters. We'll try to get away without adding this for as long as
possible. -/
instance : Add (Support α) where
  add S T := ⟨S.max + T.max, fun i hi =>
    if hi' : i < S.max then
      S.f i hi'
    else
      T.f (i - S.max) (κ_sub_lt hi (not_lt.mp hi'))⟩

theorem Support.add_f_eq {S T : Support α} {i : κ} (hi : i < (S + T).max) :
    (S + T).f i hi =
      if hi' : i < S.max then
        S.f i hi'
      else
        T.f (i - S.max) (κ_sub_lt hi (not_lt.mp hi')) :=
  rfl

@[simp]
theorem Support.add_max {S T : Support α} : (S + T).max = S.max + T.max :=
  rfl

theorem Support.add_f_left {S T : Support α} {i : κ} (h : i < S.max) :
    (S + T).f i (h.trans_le (κ_le_self_add _ _)) = S.f i h :=
  by rw [add_f_eq, dif_pos h]

theorem Support.add_f_right {S T : Support α} {i : κ} (h₁ : i < (S + T).max) (h₂ : S.max ≤ i) :
    (S + T).f i h₁ = T.f (i - S.max) (κ_sub_lt h₁ h₂) :=
  by rw [add_f_eq, dif_neg (not_lt.mpr h₂)]

theorem Support.add_f_right_add {S T : Support α} {i : κ} (h : i < T.max) :
    (S + T).f (S.max + i) (add_lt_add_left h S.max) = T.f i h := by
  rw [add_f_right]
  simp only [κ_add_sub_cancel]
  exact κ_le_self_add _ _

theorem Support.add_coe (S T : Support α) :
    (S + T : Set (SupportCondition α)) = (S : Set _) ∪ T := by
  ext c
  simp only [mem_carrier_iff, Set.mem_union]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases hi' : i < S.max
    · refine Or.inl ⟨i, hi', ?_⟩
      rw [add_f_left]
    · refine Or.inr ⟨i - S.max, κ_sub_lt hi (not_lt.mp hi'), ?_⟩
      rw [add_f_right]
      exact not_lt.mp hi'
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · refine ⟨i, hi.trans_le (κ_le_self_add _ _), ?_⟩
      rw [add_f_left]
    · refine ⟨S.max + i, add_lt_add_left hi S.max, ?_⟩
      rw [add_f_right_add]

end ConNF
