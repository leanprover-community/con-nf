import Mathlib.Tactic.Have
import ConNF.Mathlib.Cardinal
import ConNF.Mathlib.Order
import ConNF.Mathlib.Ordinal
import ConNF.Mathlib.WithBot
import Mathlib.SetTheory.Cardinal.Cofinality

/-!
# Parameters of the construction

We describe the various parameters to the model construction.
-/

open Cardinal

open scoped Classical

universe u

namespace ConNF

/--
The parameters of the construction. We collect them all in one class for simplicity.
Note that the ordinal `λ` in the paper is instead referred to here as `Λ`, since the symbol `λ` is
used for lambda abstractions.

Ordinals and cardinals are represented here as arbitrary types (not sets) with certain properties.
For instance, `Λ` is an arbitrary type that has an ordering `<`, which is assumed to be a
well-ordering (the `Λ_isWellOrder` term is a proof of this fact).

The prefix `#` denotes the cardinality of a type.
-/
class Params where
  /--
  The type indexing the levels of our model.
  This type is well-ordered.
  We inductively construct each type level by induction over `Λ`.
  Its cardinality is smaller than `μ`.
  -/
  Λ : Type u
  [Λ_linearOrder : LinearOrder Λ]
  [Λ_isWellOrder : IsWellOrder Λ (· < ·)]
  [Λ_zero : Zero Λ]
  [Λ_succ : SuccOrder Λ]
  Λ_zero_le (α : Λ) : 0 ≤ α
  Λ_isLimit : (Ordinal.type ((· < ·) : Λ → Λ → Prop)).IsLimit
  /--
  The type indexing the atoms in each litter.
  It is uncountable, well-ordered, has regular cardinality, and is smaller than `μ`.
  It also has an additive monoid structure induced by its well-ordering.
  -/
  κ : Type u
  aleph0_lt_mk_κ : ℵ₀ < #κ
  [κ_linearOrder : LinearOrder κ]
  [κ_isWellOrder : IsWellOrder κ (· < ·)]
  κ_ord : Ordinal.type ((· < ·) : κ → κ → Prop) = (#κ).ord
  κ_isRegular : (#κ).IsRegular
  [κ_succ : SuccOrder κ]
  [κ_addMonoid : AddMonoid κ]
  [κ_sub : Sub κ]
  κ_add_typein (i j : κ) : Ordinal.typein (· < ·) (i + j : κ) =
    Ordinal.typein (· < ·) i + Ordinal.typein (· < ·) j
  κ_sub_typein (i j : κ) : Ordinal.typein (· < ·) (i - j : κ) =
    Ordinal.typein (· < ·) i - Ordinal.typein (· < ·) j
  /--
  A large type used in indexing the litters.
  This type is well-ordered.
  Its cardinality is a strong limit, at least as large as `Λ` and strictly larger than `κ`.
  The cofinality of the order type of `μ` is at least `κ` and at least `Λ`.
  -/
  μ : Type u
  [μ_linearOrder : LinearOrder μ]
  [μ_isWellOrder : IsWellOrder μ (· < ·)]
  μ_ord : Ordinal.type ((· < ·) : μ → μ → Prop) = (#μ).ord
  μ_isStrongLimit : (#μ).IsStrongLimit
  type_Λ_le : Ordinal.type ((· < ·) : Λ → Λ → Prop) ≤ (#μ).ord.cof.ord
  κ_lt_μ : #κ < #μ
  κ_le_μ_ord_cof : #κ ≤ (#μ).ord.cof

export Params (Λ κ μ)

/-!
## Explicit parameters

There exist valid parameters for the model. The smallest such parameters are
* `Λ := ℵ_0`
* `κ := ℵ_1`
* `μ = ℶ_{ω_1}`.

We begin by creating a few instances that allow us to use cardinals to satisfy the model parameters.
-/

theorem noMaxOrder_of_ordinal_type_eq {α : Type u} [Preorder α] [Infinite α] [IsWellOrder α (· < ·)]
    (h : (Ordinal.type ((· < ·) : α → α → Prop)).IsLimit) : NoMaxOrder α := by
  refine ⟨fun a => ?_⟩
  have := (Ordinal.succ_lt_of_isLimit h).mpr (Ordinal.typein_lt_type (· < ·) a)
  obtain ⟨b, hb⟩ := Ordinal.typein_surj (· < ·) this
  refine ⟨b, ?_⟩
  have := Order.lt_succ (Ordinal.typein (fun x y => x < y) a)
  rw [← hb, Ordinal.typein_lt_typein] at this
  exact this

noncomputable def succOrderOfIsWellOrder {α : Type u} [Preorder α] [Infinite α]
    [inst : IsWellOrder α (· < ·)] (h : (Ordinal.type ((· < ·) : α → α → Prop)).IsLimit) :
    SuccOrder α where
  succ := inst.toIsWellFounded.wf.succ
  le_succ a := le_of_lt (WellFounded.lt_succ _ ((noMaxOrder_of_ordinal_type_eq h).exists_gt a))
  max_of_succ_le ha hb :=
    (ha.not_lt (WellFounded.lt_succ _ ((noMaxOrder_of_ordinal_type_eq h).exists_gt _))).elim
  succ_le_of_lt := by
    intro a b ha
    by_contra hb
    obtain hab | hab | hab :=
      inst.toIsTrichotomous.trichotomous (inst.toIsWellFounded.wf.succ a) b
    · exact hb hab.le
    · exact hb hab.le
    · rw [WellFounded.lt_succ_iff ((noMaxOrder_of_ordinal_type_eq h).exists_gt a)] at hab
      obtain (hab | hab) := hab
      exact ha.not_lt hab
      exact ha.ne hab.symm
  le_of_lt_succ := by
    intro a b ha
    rw [WellFounded.lt_succ_iff ((noMaxOrder_of_ordinal_type_eq h).exists_gt _)] at ha
    obtain (ha | ha) := ha
    exact ha.le
    exact ha.le

theorem typein_add_lt_of_type_eq_ord {α : Type _}
    [Infinite α] [LinearOrder α] [IsWellOrder α (· < ·)]
    (h : Ordinal.type ((· < ·) : α → α → Prop) = (#α).ord) (x y : α) :
    Ordinal.typein (· < ·) x + Ordinal.typein (· < ·) y <
      Ordinal.type ((· < ·) : α → α → Prop) := by
  have h₁ := Ordinal.typein_lt_type (· < ·) x
  have h₂ := Ordinal.typein_lt_type (· < ·) y
  rw [h, lt_ord] at h₁ h₂ ⊢
  exact add_lt_of_lt (infinite_iff.mp inferInstance) h₁ h₂

noncomputable def add_of_type_eq_ord {α : Type _}
    [Infinite α] [LinearOrder α] [IsWellOrder α (· < ·)]
    (h : Ordinal.type ((· < ·) : α → α → Prop) = (#α).ord) : Add α where
  add x y := Ordinal.enum (· < ·)
    (Ordinal.typein (· < ·) x + Ordinal.typein (· < ·) y) (typein_add_lt_of_type_eq_ord h x y)

noncomputable def _root_.IsWellFounded.bot
    (α : Type _) [Nonempty α] (r : α → α → Prop) [i : IsWellFounded α r] : α :=
  i.wf.min Set.univ Set.univ_nonempty

theorem _root_.IsWellFounded.not_lt_bot
    (α : Type _) [Nonempty α] (r : α → α → Prop) [IsWellFounded α r] (x : α) :
    ¬r x (IsWellFounded.bot α r) :=
  IsWellFounded.wf.not_lt_min _ _ (Set.mem_univ _)

theorem _root_.Ordinal.typein_eq_zero_iff
    {α : Type _} {r : α → α → Prop} [Nonempty α] [IsWellOrder α r] {x : α} :
    Ordinal.typein r x = 0 ↔ ∀ y ≠ x, r x y := by
  constructor
  · intro h y
    rw [← Ordinal.typein_lt_typein r, h, Ordinal.pos_iff_ne_zero, ← h]
    exact (Ordinal.typein_injective r).ne
  · intro h
    have : 0 < Ordinal.type r
    · rw [Ordinal.pos_iff_ne_zero, ne_eq, Ordinal.type_eq_zero_iff_isEmpty]
      exact not_isEmpty_of_nonempty α
    obtain ⟨y, hy⟩ := Ordinal.typein_surj r this
    have : y = x
    · by_contra hyx
      have := (Ordinal.typein_lt_typein r).mpr (h y hyx)
      rw [hy, lt_iff_not_ge] at this
      exact this (Ordinal.zero_le _)
    subst this
    exact hy

theorem _root_.Ordinal.typein_bot
    {α : Type _} [Nonempty α] [LinearOrder α] [IsWellOrder α (· < ·)] :
    Ordinal.typein (· < ·) (IsWellFounded.bot α (· < ·)) = 0 := by
  rw [Ordinal.typein_eq_zero_iff]
  intro x hx
  rw [← lt_or_lt_iff_ne] at hx
  cases hx with
  | inl hx => cases IsWellFounded.not_lt_bot α (· < ·) x hx
  | inr hx => exact hx

noncomputable def addZeroClass_of_type_eq_ord {α : Type _}
    [Infinite α] [LinearOrder α] [IsWellOrder α (· < ·)]
    (h : Ordinal.type ((· < ·) : α → α → Prop) = (#α).ord) : AddZeroClass α where
  zero := IsWellFounded.bot α (· < ·)
  zero_add x := by
    change Ordinal.enum _ (Ordinal.typein (· < ·) (IsWellFounded.bot α (· < ·)) + _) _ = _
    simp_rw [Ordinal.typein_bot]
    simp only [zero_add, Ordinal.enum_typein]
  add_zero x := by
    change Ordinal.enum _ (_ + Ordinal.typein (· < ·) (IsWellFounded.bot α (· < ·))) _ = _
    simp_rw [Ordinal.typein_bot]
    simp only [add_zero, Ordinal.enum_typein]
  __ := add_of_type_eq_ord h

noncomputable def addMonoid_of_type_eq_ord {α : Type _}
    [Infinite α] [LinearOrder α] [IsWellOrder α (· < ·)]
    (h : Ordinal.type ((· < ·) : α → α → Prop) = (#α).ord) : AddMonoid α where
  add_assoc x y z := by
    change
      Ordinal.enum _ (Ordinal.typein _ (Ordinal.enum _ _ _) + _) _ =
      Ordinal.enum _ (_ + Ordinal.typein _ (Ordinal.enum _ _ _)) _
    simp only [Ordinal.typein_enum, Ordinal.enum_inj, add_assoc]
  nsmul := nsmulRec
  __ := addZeroClass_of_type_eq_ord h

noncomputable def sub_of_isWellOrder {α : Type _}
    [LinearOrder α] [IsWellOrder α (· < ·)] : Sub α where
  sub x y := Ordinal.enum (· < ·)
    (Ordinal.typein (· < ·) x - Ordinal.typein (· < ·) y)
      ((Ordinal.sub_le_self _ _).trans_lt (Ordinal.typein_lt_type _ _))

/-- The smallest set of valid parameters for the model.
They are instantiated in Lean's minimal universe `0`. -/
noncomputable def minimalParams : Params.{0} where
  Λ := ℕ
  Λ_zero_le := zero_le
  Λ_isLimit := by
    rw [Ordinal.type_nat_lt]
    exact Ordinal.omega_isLimit
  κ := (aleph 1).ord.out.α
  aleph0_lt_mk_κ := by
    simp only [mk_ordinal_out, card_ord]
    exact aleph0_lt_aleph_one
  κ_ord := by simp
  κ_isRegular := by
    simp only [Cardinal.card_ord, Cardinal.mk_ordinal_out]
    exact isRegular_aleph_one
  κ_succ :=
    let _ : Infinite (aleph 1).ord.out.α :=
      by simp only [Cardinal.infinite_iff, mk_ordinal_out, card_ord, aleph0_le_aleph]
    succOrderOfIsWellOrder (by rw [Ordinal.type_lt]; exact ord_aleph_isLimit 1)
  κ_addMonoid :=
    let _ : Infinite (aleph 1).ord.out.α :=
      by simp only [Cardinal.infinite_iff, mk_ordinal_out, card_ord, aleph0_le_aleph]
    addMonoid_of_type_eq_ord (by simp)
  κ_sub := sub_of_isWellOrder
  κ_add_typein i j := Ordinal.typein_enum _ _
  κ_sub_typein i j := Ordinal.typein_enum _ _
  μ := (beth <| ord <| aleph 1).ord.out.α
  μ_ord := by simp
  μ_isStrongLimit := by
    simp only [Cardinal.card_ord, Cardinal.mk_ordinal_out]
    exact isStrongLimit_beth (Ordinal.IsLimit.isSuccLimit (ord_aleph_isLimit _))
  type_Λ_le := by
    simp only [Ordinal.type_nat_lt, mk_ordinal_out, card_ord]
    refine le_of_lt ?_
    rw [beth_normal.cof_eq (ord_isLimit <| aleph0_le_aleph 1), lt_ord, Ordinal.card_omega]
    exact lt_of_lt_of_le aleph0_lt_aleph_one isRegular_aleph_one.2
  κ_lt_μ := by
    simp only [mk_out, mk_ordinal_out, card_ord]
    exact (aleph_le_beth _).trans_lt (beth_strictMono (ord_aleph_isLimit _).one_lt)
  κ_le_μ_ord_cof := by
    simp only [mk_out, mk_ordinal_out, card_ord]
    rw [beth_normal.cof_eq (ord_isLimit <| aleph0_le_aleph 1)]
    exact isRegular_aleph_one.2

variable [Params.{u}] {ι α β : Type u}

/-! Here, we unpack the hypotheses on `Λ`, `κ`, `μ` into instances that Lean can see. -/

theorem aleph0_le_mk_Λ : ℵ₀ ≤ #Λ := by
  have := Ordinal.card_le_card (Ordinal.omega_le_of_isLimit Params.Λ_isLimit)
  simp only [Ordinal.card_omega, Ordinal.card_type] at this
  exact this

theorem mk_Λ_ne_zero : #Λ ≠ 0 :=
  fun h => Cardinal.aleph0_pos.not_le (aleph0_le_mk_Λ.trans h.le)

theorem Λ_le_μ : #Λ ≤ #μ := by
  have := Ordinal.card_le_card Params.type_Λ_le
  simp only [Ordinal.card_type, card_ord] at this
  refine this.trans ?_
  have := Ordinal.ord_cof_le (#μ).ord
  rw [ord_le] at this
  refine this.trans ?_
  rw [card_ord]

instance : LinearOrder Λ := Params.Λ_linearOrder
instance : IsWellOrder Λ (· < ·) := Params.Λ_isWellOrder
instance : Zero Λ := Params.Λ_zero
instance : Inhabited Λ := ⟨0⟩
instance : Infinite Λ := Cardinal.infinite_iff.mpr aleph0_le_mk_Λ
instance : SuccOrder Λ := Params.Λ_succ
instance : NoMaxOrder Λ := noMaxOrder_of_ordinal_type_eq Params.Λ_isLimit

instance : LinearOrder κ := Params.κ_linearOrder
instance : IsWellOrder κ (· < ·) := Params.κ_isWellOrder
instance : SuccOrder κ := Params.κ_succ
instance : AddMonoid κ := Params.κ_addMonoid
instance : Sub κ := Params.κ_sub
instance : Inhabited κ := ⟨0⟩
instance : Infinite κ := Cardinal.infinite_iff.mpr Params.κ_isRegular.aleph0_le
instance : NoMaxOrder κ := by
  have := Cardinal.ord_isLimit Params.κ_isRegular.aleph0_le
  rw [← Params.κ_ord] at this
  exact noMaxOrder_of_ordinal_type_eq this

instance : LinearOrder μ := Params.μ_linearOrder
instance : IsWellOrder μ (· < ·) := Params.μ_isWellOrder
instance : Nonempty μ := mk_ne_zero_iff.1 Params.μ_isStrongLimit.1
instance : Infinite μ := Cardinal.infinite_iff.mpr Params.μ_isStrongLimit.isLimit.aleph0_le
instance : NoMaxOrder μ := by
  have := Cardinal.ord_isLimit Params.μ_isStrongLimit.isLimit.aleph0_le
  rw [← Params.μ_ord] at this
  exact noMaxOrder_of_ordinal_type_eq this

/-!
## The ordered structure on `κ`
-/

def κ_ofNat : ℕ → κ
  | 0 => 0
  | n + 1 => Order.succ (κ_ofNat n)

instance (n : ℕ) : OfNat κ n := ⟨κ_ofNat n⟩

instance : CovariantClass κ κ (· + ·) (· ≤ ·) := by
  constructor
  intro i j k h
  rw [← not_lt, ← Ordinal.typein_le_typein (· < ·)] at h ⊢
  rw [Params.κ_add_typein, Params.κ_add_typein]
  exact add_le_add_left h _

instance : CovariantClass κ κ (Function.swap (· + ·)) (· ≤ ·) := by
  constructor
  intro i j k h
  rw [← not_lt, ← Ordinal.typein_le_typein (· < ·)] at h ⊢
  rw [Params.κ_add_typein, Params.κ_add_typein]
  exact add_le_add_right h _

instance : ContravariantClass κ κ (· + ·) (· ≤ ·) := by
  constructor
  intro i j k h
  rw [← not_lt, ← Ordinal.typein_le_typein (· < ·)] at h ⊢
  rw [Params.κ_add_typein, Params.κ_add_typein, add_le_add_iff_left] at h
  exact h

@[simp]
theorem κ_typein_zero : Ordinal.typein ((· < ·) : κ → κ → Prop) 0 = 0 := by
  have := add_zero (0 : κ)
  rw [← Ordinal.typein_inj (· < ·), Params.κ_add_typein] at this
  conv at this => rhs; rw [← add_zero (Ordinal.typein _ _)]
  rw [Ordinal.add_left_cancel] at this
  exact this

theorem κ_le_zero_iff (i : κ) : i ≤ 0 ↔ i = 0 :=
  by rw [← not_lt, ← Ordinal.typein_le_typein (· < ·), κ_typein_zero, Ordinal.le_zero,
    ← κ_typein_zero, Ordinal.typein_inj]

theorem κ_not_lt_zero (i : κ) : ¬i < 0 := by
  obtain (h | h | h) := lt_trichotomy i 0
  · cases h.ne ((κ_le_zero_iff i).mp h.le)
  · exact h.not_lt
  · exact h.not_lt

theorem κ_pos (i : κ) : 0 ≤ i := by
  rw [← not_lt]
  exact κ_not_lt_zero i

@[simp]
theorem κ_add_eq_zero_iff (i j : κ) : i + j = 0 ↔ i = 0 ∧ j = 0 :=
  by rw [← Ordinal.typein_inj (α := κ) (· < ·), ← Ordinal.typein_inj (α := κ) (· < ·),
    ← Ordinal.typein_inj (α := κ) (· < ·), Params.κ_add_typein, κ_typein_zero, Ordinal.add_eq_zero_iff]

@[simp]
theorem κ_succ_typein (i : κ) :
    Ordinal.typein ((· < ·) : κ → κ → Prop) (Order.succ i) =
    Ordinal.typein ((· < ·) : κ → κ → Prop) i + 1 := by
  refine le_antisymm ?_ ?_
  · have : i < Ordinal.enum (· < ·) (Ordinal.typein ((· < ·) : κ → κ → Prop) i + 1) ?_
    · conv_lhs => rw [← Ordinal.enum_typein ((· < ·) : κ → κ → Prop) i]
      rw [Ordinal.enum_lt_enum (r := (· < ·))]
      · exact lt_add_one _
    have := Order.succ_le_of_lt this
    conv at this => lhs; rw [← Ordinal.enum_typein ((· < ·) : κ → κ → Prop) (Order.succ i)]
    rw [← not_lt, Ordinal.enum_le_enum] at this
    exact this
    · have := Order.lt_succ i
      rw [← Ordinal.typein_lt_typein ((· < ·) : κ → κ → Prop)] at this
      exact (Order.succ_le_of_lt this).trans_lt (Ordinal.typein_lt_type _ _)
  · simp only [Ordinal.add_one_eq_succ, Order.succ_le_iff, Ordinal.typein_lt_typein,
      Order.lt_succ_iff_not_isMax, gt_iff_lt, not_isMax, not_false_eq_true]

theorem κ_zero_lt_one : (0 : κ) < 1 := by
  rw [← Ordinal.typein_lt_typein ((· < ·) : κ → κ → Prop)]
  exact lt_of_lt_of_eq (lt_add_one _) (κ_succ_typein 0).symm

@[simp]
theorem κ_lt_one_iff (i : κ) : i < 1 ↔ i = 0 := by
  constructor
  · rw [← κ_le_zero_iff]
    exact SuccOrder.le_of_lt_succ
  · rintro rfl
    exact κ_zero_lt_one

theorem κ_le_self_add (i j : κ) : i ≤ i + j := by
  rw [← not_lt, ← Ordinal.typein_le_typein (· < ·), Params.κ_add_typein]
  exact Ordinal.le_add_right _ _

theorem κ_le_add_self (i j : κ) : i ≤ j + i := by
  rw [← not_lt, ← Ordinal.typein_le_typein (· < ·), Params.κ_add_typein]
  exact Ordinal.le_add_left _ _

theorem κ_add_sub_cancel (i j : κ) : i + j - i = j := by
  rw [← Ordinal.typein_inj (· < ·), Params.κ_sub_typein, Params.κ_add_typein]
  exact Ordinal.add_sub_cancel _ _

theorem κ_sub_lt_iff {i j k : κ} (h : j ≤ i) : i - j < k ↔ i < j + k := by
  rw [← Ordinal.typein_lt_typein (α := κ) (· < ·), ← Ordinal.typein_lt_typein (α := κ) (· < ·)]
  rw [← not_lt, ← Ordinal.typein_le_typein (· < ·)] at h
  rw [Params.κ_add_typein, ← Ordinal.sub_lt_of_le h, Params.κ_sub_typein]

theorem κ_sub_lt {i j k : κ} (h₁ : i < j + k) (h₂ : j ≤ i) : i - j < k := by
  rw [κ_sub_lt_iff h₂]
  exact h₁

theorem κ_lt_sub_iff {i j k : κ} : k < i - j ↔ j + k < i := by
  rw [← Ordinal.typein_lt_typein (α := κ) (· < ·), ← Ordinal.typein_lt_typein (α := κ) (· < ·)]
  rw [Params.κ_add_typein, Params.κ_sub_typein, Ordinal.lt_sub]

instance : IsLeftCancelAdd κ := by
  constructor
  intro i j k h
  have := congr_arg (Ordinal.typein (· < ·)) h
  rw [Params.κ_add_typein, Params.κ_add_typein, Ordinal.add_left_cancel] at this
  exact Ordinal.typein_injective _ this

/-!
## Type indices
-/

/-- Either the base type or a proper type index (an element of `Λ`).
The base type is written `⊥`. -/
@[reducible]
def TypeIndex :=
  WithBot Λ

/-! Since `Λ` is well-ordered, so is `Λ` together with the base type `⊥`.
This allows well founded recursion on type indices. -/

instance : WellFoundedRelation Λ :=
  IsWellOrder.toHasWellFounded

instance : WellFoundedRelation TypeIndex :=
  IsWellOrder.toHasWellFounded

/-- There are exactly `Λ` type indices. -/
@[simp]
theorem mk_typeIndex : #TypeIndex = #Λ :=
  mk_option.trans <| add_eq_left aleph0_le_mk_Λ <| one_le_aleph0.trans aleph0_le_mk_Λ

/-- Sets of the form `{y | y < x}` have cardinality `< μ`. -/
theorem card_Iio_lt_μ (x : μ) : #(Set.Iio x) < #μ :=
  card_typein_lt (· < ·) x Params.μ_ord.symm

/-- Sets of the form `{y | y ≤ x}` have cardinality `< μ`. -/
theorem card_Iic_lt_μ (x : μ) : #(Set.Iic x) < #μ := by
  rw [← Set.Iio_union_right, mk_union_of_disjoint, mk_singleton]
  refine add_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le ?_ ?_
  · exact card_Iio_lt_μ x
  · exact one_lt_aleph0.trans_le Params.μ_isStrongLimit.isLimit.aleph0_le
  · simp only [Set.disjoint_singleton_right, Set.mem_Iio, lt_self_iff_false, not_false_eq_true]

theorem card_typein_lt' {α : Type _} {κ : Cardinal} (r : α → α → Prop) [IsWellOrder α r] (x : α)
    (h : Ordinal.type r ≤ ord κ) :
    Ordinal.card (Ordinal.typein r x) < κ := by
  rw [← lt_ord]
  exact (Ordinal.typein_lt_type r x).trans_le h

theorem card_Iio_lt_Λ (x : Λ) : #(Set.Iio x) < (#μ).ord.cof :=
  card_typein_lt' (· < ·) x Params.type_Λ_le

theorem card_Iic_lt_Λ (x : Λ) : #(Set.Iic x) < (#μ).ord.cof := by
  rw [← Set.Iio_union_right, mk_union_of_disjoint, mk_singleton]
  refine add_lt_of_lt ?_ ?_ ?_
  · rw [Ordinal.aleph0_le_cof]
    exact ord_isLimit Params.μ_isStrongLimit.isLimit.aleph0_le
  · exact card_Iio_lt_Λ x
  · refine one_lt_aleph0.trans_le ?_
    rw [Ordinal.aleph0_le_cof]
    exact ord_isLimit Params.μ_isStrongLimit.isLimit.aleph0_le
  · simp only [Set.disjoint_singleton_right, Set.mem_Iio, lt_self_iff_false, not_false_eq_true]

theorem card_Iio_lt_typeIndex (x : TypeIndex) : #(Set.Iio x) < (#μ).ord.cof := by
  induction x using WithBot.recBotCoe with
  | bot =>
    rw [Set.Iio_bot, mk_eq_zero, pos_iff_ne_zero, ne_eq, Ordinal.cof_eq_zero, ← ord_zero]
    intro h
    exact Params.μ_isStrongLimit.isLimit.ne_zero (ord_injective h)
  | coe x =>
    have : Set.Iio (x : TypeIndex) = WithBot.some '' Set.Iio x ∪ {⊥}
    · ext y
      induction y using WithBot.recBotCoe <;> simp
    rw [this]
    refine (mk_union_le _ _).trans_lt ?_
    refine add_lt_of_lt ?_ ?_ ?_
    · rw [Ordinal.aleph0_le_cof]
      exact ord_isLimit Params.μ_isStrongLimit.isLimit.aleph0_le
    · refine mk_image_le.trans_lt ?_
      exact card_Iio_lt_Λ x
    · simp only [mk_fintype, Fintype.card_ofSubsingleton, Nat.cast_one]
      refine lt_of_lt_of_le ?_ Params.κ_le_μ_ord_cof
      exact one_lt_aleph0.trans Params.aleph0_lt_mk_κ

theorem card_Iic_lt_typeIndex (x : TypeIndex) : #(Set.Iic x) < (#μ).ord.cof := by
  rw [← Set.Iio_union_right, mk_union_of_disjoint, mk_singleton]
  refine add_lt_of_lt ?_ ?_ ?_
  · rw [Ordinal.aleph0_le_cof]
    exact ord_isLimit Params.μ_isStrongLimit.isLimit.aleph0_le
  · exact card_Iio_lt_typeIndex x
  · refine one_lt_aleph0.trans_le ?_
    rw [Ordinal.aleph0_le_cof]
    exact ord_isLimit Params.μ_isStrongLimit.isLimit.aleph0_le
  · simp only [Set.disjoint_singleton_right, Set.mem_Iio, lt_self_iff_false, not_false_eq_true]

end ConNF
