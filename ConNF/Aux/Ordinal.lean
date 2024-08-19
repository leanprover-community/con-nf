import ConNF.Aux.WellOrder
import Mathlib.SetTheory.Cardinal.Ordinal

noncomputable section
universe u

open Cardinal

namespace Ordinal

theorem card_Iio (o : Ordinal.{u}) : #(Set.Iio o) = Cardinal.lift.{u + 1} o.card := by
  rw [Cardinal.eq.mpr ⟨o.enumIsoOut.toEquiv.trans Equiv.ulift.{u + 1, u}.symm⟩,
    mk_uLift, mk_ordinal_out, lift_card]

instance {o : Ordinal.{u}} : LtWellOrder (Set.Iio o) where

theorem type_Iio (o : Ordinal.{u}) :
    type ((· < ·) : Set.Iio o → Set.Iio o → Prop) = lift.{u + 1} o := by
  have := Ordinal.lift_type_eq.{u + 1, u, u + 1}
    (r := ((· < ·) : Set.Iio o → Set.Iio o → Prop)) (s := o.out.r)
  rw [lift_id, type_out] at this
  rw [this]
  exact ⟨o.enumIsoOut.toRelIsoLT⟩

def withBot_orderIso {α : Type u} [Preorder α] [IsWellOrder α (· < ·)] :
    ((· < ·) : WithBot α → WithBot α → Prop) ≃r
      Sum.Lex (EmptyRelation (α := PUnit)) ((· < ·) : α → α → Prop) where
  toFun := WithBot.recBotCoe (Sum.inl PUnit.unit) Sum.inr
  invFun := Sum.elim (λ _ ↦ ⊥) (λ x ↦ x)
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl
  map_rel_iff' {x y} := by cases x <;> cases y <;>
    simp only [Equiv.coe_fn_mk, WithBot.recBotCoe_bot, WithBot.recBotCoe_coe,
    WithBot.coe_lt_coe, WithBot.bot_lt_coe, empty_relation_apply, lt_self_iff_false, not_lt_bot,
    Sum.lex_inl_inl, Sum.lex_inr_inl, Sum.lex_inr_inr, Sum.Lex.sep]

@[simp]
theorem type_withBot {α : Type u} [Preorder α] [IsWellOrder α (· < ·)] :
    type ((· < ·) : WithBot α → WithBot α → Prop) = 1 + type ((· < ·) : α → α → Prop) := by
  change _ = type EmptyRelation + _
  rw [← type_sum_lex, type_eq]
  exact ⟨withBot_orderIso⟩

theorem noMaxOrder_of_isLimit {α : Type u} [Preorder α] [IsWellOrder α (· < ·)]
    (h : (type ((· < ·) : α → α → Prop)).IsLimit) : NoMaxOrder α := by
  constructor
  intro a
  have := (succ_lt_of_isLimit h).mpr (typein_lt_type (· < ·) a)
  obtain ⟨b, hb⟩ := typein_surj (· < ·) this
  use b
  have := Order.lt_succ (typein ((· < ·) : α → α → Prop) a)
  rw [← hb, typein_lt_typein] at this
  exact this

theorem isLimit_of_noMaxOrder {α : Type u} [Nonempty α] [Preorder α] [IsWellOrder α (· < ·)]
    (h : NoMaxOrder α) : (type ((· < ·) : α → α → Prop)).IsLimit := by
  constructor
  · simp only [ne_eq, type_eq_zero_iff_isEmpty, not_isEmpty_of_nonempty, not_false_eq_true]
  · intro o ho
    obtain ⟨x, hx⟩ := h.exists_gt (enum ((· < ·) : α → α → Prop) o ho)
    refine lt_of_le_of_lt ?_ (typein_lt_type ((· < ·) : α → α → Prop) x)
    rw [← typein_lt_typein ((· < ·) : α → α → Prop), typein_enum] at hx
    rwa [Order.succ_le_iff]

theorem isLimit_iff_noMaxOrder {α : Type u} [Nonempty α] [Preorder α] [IsWellOrder α (· < ·)] :
    (type ((· < ·) : α → α → Prop)).IsLimit ↔ NoMaxOrder α :=
  ⟨noMaxOrder_of_isLimit, isLimit_of_noMaxOrder⟩

variable {c : Cardinal.{u}} (h : ℵ₀ ≤ c)

theorem add_lt_ord (h : ℵ₀ ≤ c) {x y : Ordinal.{u}}
    (hx : x < c.ord) (hy : y < c.ord) : x + y < c.ord := by
  rw [lt_ord] at hx hy ⊢
  rw [card_add]
  exact Cardinal.add_lt_of_lt h hx hy

def iioAdd : Add (Set.Iio c.ord) where
  add x y := ⟨x + y, add_lt_ord h x.prop y.prop⟩

def iioSub (o : Ordinal) : Sub (Set.Iio o) where
  sub x y := ⟨x - y, (sub_le_self x y).trans_lt x.prop⟩

theorem ord_pos (h : ℵ₀ ≤ c) : 0 < c.ord := by
  rw [lt_ord, card_zero]
  exact aleph0_pos.trans_le h

def iioZero : Zero (Set.Iio c.ord) where
  zero := ⟨0, ord_pos h⟩

@[simp]
theorem iioAdd_def (x y : Set.Iio c.ord) :
    letI := iioAdd h
    ((x + y : Set.Iio c.ord) : Ordinal) = x + y :=
  rfl

def iioAddMonoid : AddMonoid (Set.Iio c.ord) where
  add_assoc x y z := by
    apply Subtype.val_injective
    rw [iioAdd_def, iioAdd_def, add_assoc]
    rfl
  zero_add x := by
    apply Subtype.val_injective
    rw [iioAdd_def]
    exact zero_add x.val
  add_zero x := by
    apply Subtype.val_injective
    rw [iioAdd_def]
    exact add_zero x.val
  nsmul := nsmulRec
  __ := iioAdd h
  __ := iioZero h

end Ordinal
