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

theorem type_iio (o : Ordinal.{u}) :
    type ((· < ·) : Set.Iio o → Set.Iio o → Prop) = lift.{u + 1} o := by
  have := Ordinal.lift_type_eq.{u + 1, u, u + 1}
    (r := ((· < ·) : Set.Iio o → Set.Iio o → Prop)) (s := o.out.r)
  rw [lift_id, type_out] at this
  rw [this]
  exact ⟨o.enumIsoOut.toRelIsoLT⟩

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
