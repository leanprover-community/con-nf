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
For instance, `Λ` is an arbitrary type that has an ordering `Λr`, which is assumed to be a
well-ordering (the `Λwo` term is a proof of this fact). If `Λr a b` holds, then we can say `a < b`.

The prefix `#` denotes the cardinality of a type.
-/
class Params where
  /--
  The type indexing the levels of our model.
  This type is well-ordered.
  We inductively construct each type level by induction over `Λ`.
  Its cardinality is smaller than `κ` and `μ`.
  -/
  Λ : Type u
  Λr : Λ → Λ → Prop
  [Λwo : IsWellOrder Λ Λr]
  Λ_isLimit : (Ordinal.type Λr).IsLimit
  /--
  The type indexing the atoms in each litter.
  Its cardinality is regular, and is larger than `Λ` but smaller than `κ`.
  -/
  κ : Type u
  κ_isRegular : (#κ).IsRegular
  Λ_lt_κ : #Λ < #κ
  /--
  A large type used in indexing the litters.
  This type is well-ordered.
  Its cardinality is a strong limit, larger than `Λ` and `κ`.
  The cofinality of the order type of `μ` is at least `κ`.
  -/
  μ : Type u
  μr : μ → μ → Prop
  [μwo : IsWellOrder μ μr]
  μ_ord : Ordinal.type μr = (#μ).ord
  μ_isStrongLimit : (#μ).IsStrongLimit
  κ_lt_μ : #κ < #μ
  κ_le_μ_ord_cof : #κ ≤ (#μ).ord.cof

export Params (Λ Λr Λwo Λ_isLimit κ κ_isRegular Λ_lt_κ μ μr μwo μ_ord μr μ_isStrongLimit
  κ_lt_μ κ_le_μ_ord_cof)

/-!
### Explicit parameters

There exist valid parameters for the model. The smallest such parameters are
* `Λ := ℵ_0`
* `κ := ℵ_1`
* `μ = ℶ_{ω_1}`.
-/

example : Params.{0} where
  Λ := ℕ
  Λr := (· < ·)
  Λwo := inferInstance
  Λ_isLimit := by rw [Ordinal.type_nat_lt]; exact Ordinal.omega_isLimit
  κ := (aleph 1).out
  κ_isRegular := by rw [mk_out]; exact isRegular_aleph_one
  Λ_lt_κ := by rw [mk_denumerable, mk_out]; exact aleph0_lt_aleph_one
  μ := (beth <| ord <| aleph 1).ord.out.α
  μr := (beth <| ord <| aleph 1).ord.out.r
  μwo := (beth <| ord <| aleph 1).ord.out.wo
  μ_ord := by simp
  μ_isStrongLimit := by
    simp only [Cardinal.card_ord, Cardinal.mk_ordinal_out]
    exact isStrongLimit_beth (Ordinal.IsLimit.isSuccLimit (ord_aleph_isLimit _))
  κ_lt_μ := by
    simp only [mk_out, mk_ordinal_out, card_ord]
    exact (aleph_le_beth _).trans_lt (beth_strictMono (ord_aleph_isLimit _).one_lt)
  κ_le_μ_ord_cof := by
    simp only [mk_out, mk_ordinal_out, card_ord]
    rw [beth_normal.cof_eq (ord_isLimit <| aleph0_le_aleph 1)]
    exact isRegular_aleph_one.2

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

variable [Params.{u}] {ι α β : Type u}

/-! To allow Lean's type checker to see that the ordering `Λr` is a well-ordering without having to
explicitly write `Λwo` everywhere, we declare it as an instance. -/

instance : IsWellOrder Λ Λr :=
  Λwo

instance : IsWellOrder μ μr :=
  μwo

/-! `Λ` is linearly ordered by `Λwo`. -/

noncomputable instance : LinearOrder Λ :=
  linearOrderOfSTO Λr

noncomputable instance : LinearOrder μ :=
  linearOrderOfSTO μr

instance : IsWellOrder Λ (· < ·) :=
  Λwo

instance : IsWellOrder μ (· < ·) :=
  μwo

/-! `Λ` and `μ` have well-founded relations given by their orders. -/

instance : WellFoundedRelation Λ :=
  IsWellOrder.toHasWellFounded (hwo := Λwo)

instance : WellFoundedRelation μ :=
  IsWellOrder.toHasWellFounded (hwo := μwo)

theorem κ_le_μ : #κ ≤ #μ :=
  κ_lt_μ.le

/-! The types `Λ`, `κ`, `μ` are inhabited and infinite. -/

theorem aleph0_le_mk_Λ : ℵ₀ ≤ #Λ := by
  have := Ordinal.card_le_card (Ordinal.omega_le_of_isLimit Λ_isLimit)
  simp only [Ordinal.card_omega, Ordinal.card_type] at this
  exact this

theorem mk_Λ_ne_zero : #Λ ≠ 0 :=
  fun h => Cardinal.aleph0_pos.not_le (aleph0_le_mk_Λ.trans h.le)

instance : Nonempty Λ :=
  mk_ne_zero_iff.1 mk_Λ_ne_zero

instance : Nonempty κ :=
  mk_ne_zero_iff.1 κ_isRegular.pos.ne'

instance : Nonempty μ :=
  mk_ne_zero_iff.1 μ_isStrongLimit.1

noncomputable instance : Inhabited Λ :=
  Classical.inhabited_of_nonempty inferInstance

noncomputable instance : Inhabited κ :=
  Classical.inhabited_of_nonempty inferInstance

noncomputable instance : Inhabited μ :=
  Classical.inhabited_of_nonempty inferInstance

instance : Infinite Λ :=
  Cardinal.infinite_iff.mpr aleph0_le_mk_Λ

instance : Infinite κ :=
  Cardinal.infinite_iff.mpr κ_isRegular.aleph0_le

instance : Infinite μ :=
  Cardinal.infinite_iff.mpr μ_isStrongLimit.isLimit.aleph0_le

instance : NoMaxOrder Λ :=
  noMaxOrder_of_ordinal_type_eq Λ_isLimit

instance : NoMaxOrder μ := by
  have := Cardinal.ord_isLimit μ_isStrongLimit.isLimit.aleph0_le
  rw [← μ_ord] at this
  exact noMaxOrder_of_ordinal_type_eq this

noncomputable instance : SuccOrder Λ :=
  succOrderOfIsWellOrder Λ_isLimit

noncomputable instance : SuccOrder μ := by
  have := Cardinal.ord_isLimit μ_isStrongLimit.isLimit.aleph0_le
  rw [← μ_ord] at this
  exact succOrderOfIsWellOrder this

/-- Either the base type or a proper type index (an element of `Λ`).
The base type is written `⊥`. -/
@[reducible]
def TypeIndex :=
  WithBot Λ

@[simp]
theorem mk_typeIndex : #TypeIndex = #Λ :=
  mk_option.trans <| add_eq_left aleph0_le_mk_Λ <| one_le_aleph0.trans aleph0_le_mk_Λ

/-! Since `Λ` is well-ordered, so is `Λ` together with the base type `⊥`.
This allows well founded recursion on type indices. -/

noncomputable instance : LinearOrder TypeIndex :=
  linearOrderOfSTO (· < ·)

noncomputable instance : WellFoundedRelation TypeIndex :=
  IsWellOrder.toHasWellFounded

noncomputable instance : WellFoundedLT TypeIndex :=
  inferInstance

/-- Principal segments (sets of the form `{y | y < x}`) have cardinality `< μ`. -/
theorem card_Iio_lt (x : μ) : #(Set.Iio x) < #μ :=
  card_typein_lt (· < ·) x μ_ord.symm

/-- Initial segments (sets of the form `{y | y ≤ x}`) have cardinality `< μ`. -/
theorem card_Iic_lt (x : μ) : #(Set.Iic x) < #μ := by
  rw [← Set.Iio_union_right, mk_union_of_disjoint, mk_singleton]
  -- TODO: This isn't the morally correct proof because it uses the fact `μ` is a limit cardinal.
  · exact (add_one_le_succ _).trans_lt (μ_isStrongLimit.isLimit.succ_lt (card_Iio_lt x))
  · simp

end ConNF
