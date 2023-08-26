import ConNF.Mathlib.Cardinal
import ConNF.Mathlib.Order
import ConNF.Mathlib.Ordinal
import ConNF.Mathlib.WithBot
import Mathlib.SetTheory.Cardinal.Cofinality

/-!
# Parameters of the construction
-/

open Cardinal

open scoped Classical

universe u

namespace ConNF

/--
The parameters of the constructions. We collect them all in one class for simplicity.
Note that the ordinal `λ` in the paper is instead referred to here as `Λ`, since the symbol `λ` is
used for lambda abstractions.

Ordinals and cardinals are represented here as arbitrary types (not sets) with certain properties.
For instance, `Λ` is an arbitrary type that has an ordering `Λr`, which is assumed to be a
well-ordering (the `Λwf` term is a proof of this fact). If `Λr a b` holds, then we can say `a < b`.

The prefix `#` denotes the cardinality of a type.

Where possible, we use `<` and `≤` instead of `>` and `≥`. Human readers can easily convert between
the two, but it is not as immediately transparent for Lean. For simplicity, we keep with the
convention of using only `<` and `≤`.
-/
class Params where
  Λ : Type u
  Λr : Λ → Λ → Prop
  [Λwf : IsWellOrder Λ Λr]
  Λ_ord : Ordinal.type Λr = (#Λ).ord
  Λ_limit : (#Λ).IsLimit
  κ : Type u
  κ_regular : (#κ).IsRegular
  Λ_lt_κ : #Λ < #κ
  μ : Type u
  μr : μ → μ → Prop
  [μwf : IsWellOrder μ μr]
  μ_ord : Ordinal.type μr = (#μ).ord
  μ_strong_limit : (#μ).IsStrongLimit
  κ_lt_μ : #κ < #μ
  κ_le_μ_cof : #κ ≤ (#μ).ord.cof

export Params (Λ Λr Λwf Λ_ord Λ_limit κ κ_regular Λ_lt_κ μ μr μwf μ_ord μr μ_strong_limit
  κ_lt_μ κ_le_μ_cof)

/-!
### Explicit parameters

There exists valid parameters for the model. The smallest parameters are
* `Λ := ℵ_0`
* `κ := ℵ_1`
* `μ = ℶ_{ω_1}`.
-/

example : Params.{0} where
  Λ := ℕ
  Λr := (· < ·)
  Λwf := inferInstance
  Λ_ord := by simp only [mk_denumerable, ord_aleph0, Ordinal.type_nat_lt]
  Λ_limit := by rw [mk_denumerable]; exact isLimit_aleph0
  κ := (aleph 1).out
  κ_regular := by rw [mk_out]; exact isRegular_aleph_one
  Λ_lt_κ := by rw [mk_denumerable, mk_out]; exact aleph0_lt_aleph_one
  μ := (beth <| ord <| aleph 1).ord.out.α
  μr := (beth <| ord <| aleph 1).ord.out.r
  μwf := (beth <| ord <| aleph 1).ord.out.wo
  μ_ord := by simp
  μ_strong_limit := by
    simp only [Cardinal.card_ord, Cardinal.mk_ordinal_out]
    exact isStrongLimit_beth (Ordinal.IsLimit.isSuccLimit (ord_aleph_isLimit _))
  κ_lt_μ := by
    simp only [mk_out, mk_ordinal_out, card_ord]
    exact (aleph_le_beth _).trans_lt (beth_strictMono (ord_aleph_isLimit _).one_lt)
  κ_le_μ_cof := by
    simp only [mk_out, mk_ordinal_out, card_ord]
    rw [beth_normal.cof_eq (ord_isLimit <| aleph0_le_aleph 1)]
    exact isRegular_aleph_one.2

theorem noMaxOrder_of_ordinal_type_eq {α : Type u} [Preorder α] [Infinite α] [IsWellOrder α (· < ·)]
    (h : Ordinal.type ((· < ·) : α → α → Prop) = (#α).ord) : NoMaxOrder α := by
  refine ⟨fun a => ?_⟩
  have := (Ordinal.succ_lt_of_isLimit ?_).mpr (Ordinal.typein_lt_type (· < ·) a)
  · obtain ⟨b, hb⟩ := Ordinal.typein_surj (· < ·) this
    refine ⟨b, ?_⟩
    have := Order.lt_succ (Ordinal.typein (fun x y => x < y) a)
    rw [← hb, Ordinal.typein_lt_typein] at this
    exact this
  · rw [h]
    exact Cardinal.ord_isLimit (Cardinal.infinite_iff.mp inferInstance)

noncomputable def succOrderOfIsWellOrder (α : Type u) [Preorder α] [Infinite α]
    [inst : IsWellOrder α (· < ·)] (h : Ordinal.type ((· < ·) : α → α → Prop) = (#α).ord) :
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

/-- To allow Lean's type checker to see that the ordering `Λr` is a well-ordering without having to
explicitly write `Λwf` everywhere, we declare it as an instance. -/
instance : IsWellOrder Λ Λr :=
  Λwf

instance : IsWellOrder μ μr :=
  μwf

/-- We can deduce from the well-ordering `Λwf` that `Λ` is linearly ordered. -/
noncomputable instance : LinearOrder Λ :=
  linearOrderOfSTO Λr

noncomputable instance : LinearOrder μ :=
  linearOrderOfSTO μr

instance : IsWellOrder Λ (· < ·) :=
  Λwf

instance : IsWellOrder μ (· < ·) :=
  μwf

/-- We deduce that `Λ` has a well-founded relation. -/
instance : WellFoundedRelation Λ :=
  IsWellOrder.toHasWellFounded (hwo := Λwf)

instance : WellFoundedRelation μ :=
  IsWellOrder.toHasWellFounded (hwo := μwf)

theorem κ_le_μ : (#κ) ≤ (#μ) :=
  κ_lt_μ.le

noncomputable instance : Inhabited Λ :=
  @Classical.inhabited_of_nonempty _ <| mk_ne_zero_iff.1 Λ_limit.1

noncomputable instance : Inhabited κ :=
  @Classical.inhabited_of_nonempty _ <| mk_ne_zero_iff.1 κ_regular.pos.ne'

noncomputable instance : Inhabited μ :=
  @Classical.inhabited_of_nonempty _ <| mk_ne_zero_iff.1 μ_strong_limit.1

instance : Infinite Λ :=
  Cardinal.infinite_iff.mpr Λ_limit.aleph0_le

instance : Infinite κ :=
  Cardinal.infinite_iff.mpr κ_regular.aleph0_le

instance : Infinite μ :=
  Cardinal.infinite_iff.mpr μ_strong_limit.isLimit.aleph0_le

instance : NoMaxOrder Λ :=
  noMaxOrder_of_ordinal_type_eq Λ_ord

instance : NoMaxOrder μ :=
  noMaxOrder_of_ordinal_type_eq μ_ord

noncomputable instance : SuccOrder Λ :=
  succOrderOfIsWellOrder Λ Λ_ord

noncomputable instance : SuccOrder μ :=
  succOrderOfIsWellOrder μ μ_ord

/-- Either the base type or a proper type index (an element of `Λ`).
The base type is written `⊥`. -/
@[reducible]
def TypeIndex :=
  WithBot Λ

@[simp]
theorem mk_typeIndex : #TypeIndex = #Λ :=
  mk_option.trans <| add_eq_left Λ_limit.aleph0_le <| one_le_aleph0.trans Λ_limit.aleph0_le

/- Since `Λ` is well-ordered, so is `Λ` together with the base type `⊥`.
This allows well founded recursion on type indices. -/
noncomputable instance : LinearOrder TypeIndex :=
  linearOrderOfSTO (· < ·)

noncomputable instance : WellFoundedRelation TypeIndex :=
  IsWellOrder.toHasWellFounded

noncomputable instance : WellFoundedLT TypeIndex :=
  inferInstance

end ConNF
