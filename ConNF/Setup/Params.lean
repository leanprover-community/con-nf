import Mathlib.Order.Interval.Set.Infinite
import ConNF.Aux.Cardinal
import ConNF.Aux.Ordinal
import ConNF.Aux.Transfer
import ConNF.Aux.WellOrder

/-!
# Model parameters

In this file, we define the parameters that we will use to construct our model of tangled type
theory.

## Main declarations
* `ConNF.Params`: The type of model parameters.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

class Params where
  Λ : Type u
  κ : Type u
  μ : Type u
  [Λ_nonempty : Nonempty Λ]
  [ΛWellOrder : LtWellOrder Λ]
  [Λ_noMaxOrder : NoMaxOrder Λ]
  aleph0_lt_κ : ℵ₀ < #κ
  κ_isRegular : (#κ).IsRegular
  μ_isStrongLimit : (#μ).IsStrongLimit
  κ_lt_μ : #κ < #μ
  κ_le_cof_μ : #κ ≤ (#μ).ord.cof
  Λ_type_le_cof_μ : type ((· < ·) : Λ → Λ → Prop) ≤ (#μ).ord.cof.ord

def minimalParams : Params where
  Λ := ℕ
  κ := (aleph 1).out
  μ := (beth (aleph 1).ord).out
  aleph0_lt_κ := by
    rw [mk_out]
    exact aleph0_lt_aleph_one
  κ_isRegular := by
    rw [mk_out]
    exact isRegular_aleph_one
  μ_isStrongLimit := by
    rw [mk_out]
    exact isStrongLimit_beth <| IsLimit.isSuccLimit <| ord_aleph_isLimit 1
  κ_lt_μ := by
    rw [mk_out, mk_out]
    apply (aleph_le_beth 1).trans_lt
    rw [beth_strictMono.lt_iff_lt]
    exact (ord_aleph_isLimit 1).one_lt
  κ_le_cof_μ := by
    rw [mk_out, mk_out]
    have := beth_normal.cof_le (aleph 1).ord
    rwa [isRegular_aleph_one.cof_eq] at this
  Λ_type_le_cof_μ := by
    rw [type_nat_lt, mk_out]
    have := beth_normal.cof_le (aleph 1).ord
    rw [isRegular_aleph_one.cof_eq, ← ord_le_ord] at this
    exact (omega_le_of_isLimit (ord_aleph_isLimit 1)).trans this

def inaccessibleParams.{v} : Params where
  Λ := (Cardinal.univ.{v, v + 1}).ord.out.α
  κ := ULift.{v + 1, v} (aleph 1).out
  μ := Cardinal.univ.{v, v + 1}.out
  Λ_nonempty := by
    rw [ord_univ, out_nonempty_iff_ne_zero, Ordinal.univ_id]
    simp only [ne_eq, type_eq_zero_iff_isEmpty, not_isEmpty_of_nonempty, not_false_eq_true]
  Λ_noMaxOrder := by
    apply noMaxOrder_of_isLimit
    change (type (Cardinal.univ.{v, v + 1}).ord.out.r).IsLimit
    rw [type_out]
    apply ord_isLimit
    exact univ_inaccessible.1.le
  aleph0_lt_κ := by
    rw [mk_uLift, mk_out, ← lift_aleph0.{v + 1, v}, lift_strictMono.lt_iff_lt]
    exact aleph0_lt_aleph_one
  κ_isRegular := by
    rw [mk_uLift, mk_out]
    apply lift_isRegular
    exact isRegular_aleph_one
  μ_isStrongLimit := by
    rw [mk_out]
    exact univ_inaccessible.2.2
  κ_lt_μ := by
    rw [mk_uLift, mk_out, mk_out]
    exact lift_lt_univ _
  κ_le_cof_μ := by
    rw [mk_uLift, mk_out, mk_out, univ_inaccessible.2.1.cof_eq]
    exact (lift_lt_univ _).le
  Λ_type_le_cof_μ := by
    change type (Cardinal.univ.{v, v + 1}).ord.out.r ≤ _
    rw [type_out, mk_out, univ_inaccessible.2.1.cof_eq]

export Params (Λ κ μ aleph0_lt_κ κ_isRegular μ_isStrongLimit κ_lt_μ κ_le_cof_μ Λ_type_le_cof_μ)

variable [Params.{u}]

instance : Nonempty Λ := Params.Λ_nonempty
instance : LtWellOrder Λ := Params.ΛWellOrder
instance : NoMaxOrder Λ := Params.Λ_noMaxOrder

theorem aleph0_lt_μ : ℵ₀ < #μ :=
  aleph0_lt_κ.trans κ_lt_μ

theorem Λ_type_le_μ_ord : type ((· < ·) : Λ → Λ → Prop) ≤ (#μ).ord :=
  Λ_type_le_cof_μ.trans <| ord_cof_le (#μ).ord

theorem Λ_le_cof_μ : #Λ ≤ (#μ).ord.cof := by
  have := card_le_of_le_ord Λ_type_le_cof_μ
  rwa [card_type] at this

theorem Λ_le_μ : #Λ ≤ #μ := by
  have := card_le_of_le_ord Λ_type_le_μ_ord
  rwa [card_type] at this

theorem κ_le_μ : #κ ≤ #μ :=
  κ_lt_μ.le

@[irreducible]
def κEquiv : κ ≃ Set.Iio (#κ).ord := by
  apply Equiv.ulift.{u + 1, u}.symm.trans
  apply Nonempty.some
  rw [← Cardinal.eq, mk_uLift, card_Iio, card_ord]

@[irreducible]
def μEquiv : μ ≃ Set.Iio (#μ).ord := by
  apply Equiv.ulift.{u + 1, u}.symm.trans
  apply Nonempty.some
  rw [← Cardinal.eq, mk_uLift, card_Iio, card_ord]

instance : LtWellOrder κ := Equiv.ltWellOrder κEquiv
instance (n : ℕ) : OfNat κ n :=
  letI := iioOfNat aleph0_lt_κ.le n
  Equiv.ofNat κEquiv n
instance : NoMaxOrder κ :=
  letI := iio_noMaxOrder aleph0_lt_κ.le
  Equiv.noMaxOrder κEquiv

instance : LtWellOrder μ := Equiv.ltWellOrder μEquiv
instance : NoMaxOrder μ :=
  letI := iio_noMaxOrder aleph0_lt_μ.le
  Equiv.noMaxOrder μEquiv

instance : Infinite Λ := NoMaxOrder.infinite
instance : Infinite κ := by rw [infinite_iff]; exact aleph0_lt_κ.le
instance : Infinite μ := by rw [infinite_iff]; exact aleph0_lt_μ.le

theorem Λ_type_isLimit : (type ((· < ·) : Λ → Λ → Prop)).IsLimit := by
  rw [isLimit_iff_noMaxOrder]
  infer_instance

@[simp]
theorem κ_type : type ((· < ·) : κ → κ → Prop) = (#κ).ord := by
  have := κEquiv.ltWellOrder_type
  rwa [Ordinal.lift_id, type_Iio, Ordinal.lift_inj] at this

@[simp]
theorem μ_type : type ((· < ·) : μ → μ → Prop) = (#μ).ord := by
  have := μEquiv.ltWellOrder_type
  rwa [Ordinal.lift_id, type_Iio, Ordinal.lift_inj] at this

instance : AddMonoid κ :=
  letI := iioAddMonoid aleph0_lt_κ.le
  Equiv.addMonoid κEquiv

instance : Sub κ :=
  letI := iioSub (#κ).ord
  Equiv.sub κEquiv

theorem κ_ofNat_def (n : ℕ) :
    letI := iioOfNat aleph0_lt_κ.le n
    OfNat.ofNat n = κEquiv.symm (OfNat.ofNat n) :=
  rfl

theorem κ_add_def (x y : κ) :
    letI := iioAddMonoid aleph0_lt_κ.le
    x + y = κEquiv.symm (κEquiv x + κEquiv y) :=
  rfl

theorem κ_sub_def (x y : κ) :
    letI := iioSub (#κ).ord
    x - y = κEquiv.symm (κEquiv x - κEquiv y) :=
  rfl

theorem κEquiv_ofNat (n : ℕ) :
    (κEquiv (OfNat.ofNat n) : Ordinal) = n := by
  rw [κ_ofNat_def, Equiv.apply_symm_apply]
  rfl

theorem κEquiv_add (x y : κ) :
    (κEquiv (x + y) : Ordinal) = (κEquiv x : Ordinal) + κEquiv y := by
  rw [κ_add_def, Equiv.apply_symm_apply]
  rfl

theorem κEquiv_sub (x y : κ) :
    (κEquiv (x - y) : Ordinal) = (κEquiv x : Ordinal) - κEquiv y := by
  rw [κ_sub_def, Equiv.apply_symm_apply]
  rfl

end ConNF
