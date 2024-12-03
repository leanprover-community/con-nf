import Mathlib.Order.Interval.Set.Infinite
import ConNF.Background.Cardinal
import ConNF.Background.Ordinal
import ConNF.Background.Transfer
import ConNF.Background.WellOrder

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
  κ_le_μ_ord_cof : #κ ≤ (#μ).ord.cof
  Λ_type_le_μ_ord_cof : type ((· < ·) : Λ → Λ → Prop) ≤ (#μ).ord.cof.ord

def Params.minimal : Params where
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
    rw [mk_out, ord_aleph]
    exact isStrongLimit_beth <| IsLimit.isSuccPrelimit <| isLimit_omega 1
  κ_lt_μ := by
    rw [mk_out, mk_out, ord_aleph]
    apply (aleph_le_beth 1).trans_lt
    rw [beth_strictMono.lt_iff_lt]
    exact (isLimit_omega 1).one_lt
  κ_le_μ_ord_cof := by
    rw [mk_out, mk_out]
    have := isNormal_beth.cof_le (aleph 1).ord
    rwa [isRegular_aleph_one.cof_eq] at this
  Λ_type_le_μ_ord_cof := by
    rw [type_nat_lt, mk_out]
    apply (omega0_le_of_isLimit (isLimit_omega 1)).trans
    have := isNormal_beth.cof_le (aleph 1).ord
    rw [isRegular_aleph_one.cof_eq, ← ord_le_ord] at this
    rwa [ord_aleph] at this ⊢

def Params.inaccessible.{v} : Params where
  Λ := (Cardinal.univ.{v, v + 1}).ord.toType
  κ := ULift.{v + 1, v} (aleph 1).out
  μ := Cardinal.univ.{v, v + 1}.out
  Λ_nonempty := by
    rw [ord_univ, toType_nonempty_iff_ne_zero, Ordinal.univ_id]
    simp only [ne_eq, type_eq_zero_iff_isEmpty, not_isEmpty_of_nonempty, not_false_eq_true]
  Λ_noMaxOrder := by
    apply noMaxOrder_of_isLimit
    change (type ((· < ·) : (Cardinal.univ.{v, v + 1}).ord.toType → _ → Prop)).IsLimit
    rw [type_toType]
    apply isLimit_ord
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
  κ_le_μ_ord_cof := by
    rw [mk_uLift, mk_out, mk_out, univ_inaccessible.2.1.cof_eq]
    exact (lift_lt_univ _).le
  Λ_type_le_μ_ord_cof := by
    change type ((· < ·) : (Cardinal.univ.{v, v + 1}).ord.toType → _ → Prop) ≤ _
    rw [type_toType, mk_out, univ_inaccessible.2.1.cof_eq]

export Params (Λ κ μ aleph0_lt_κ κ_isRegular μ_isStrongLimit κ_lt_μ κ_le_μ_ord_cof
  Λ_type_le_μ_ord_cof)

variable [Params.{u}]

instance : Nonempty Λ := Params.Λ_nonempty
instance : LtWellOrder Λ := Params.ΛWellOrder
instance : NoMaxOrder Λ := Params.Λ_noMaxOrder

/-- Allows us to use `termination_by` clauses with `Λ`. -/
instance : WellFoundedRelation Λ where
  rel := (· < ·)
  wf := IsWellFounded.wf

theorem aleph0_lt_μ : ℵ₀ < #μ :=
  aleph0_lt_κ.trans κ_lt_μ

theorem aleph0_lt_μ_ord_cof : ℵ₀ < (#μ).ord.cof :=
  aleph0_lt_κ.trans_le κ_le_μ_ord_cof

theorem Λ_type_le_μ_ord : type ((· < ·) : Λ → Λ → Prop) ≤ (#μ).ord :=
  Λ_type_le_μ_ord_cof.trans <| ord_cof_le (#μ).ord

theorem Λ_le_cof_μ : #Λ ≤ (#μ).ord.cof := by
  have := card_le_of_le_ord Λ_type_le_μ_ord_cof
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

theorem κEquiv_lt (x y : κ) :
    x < y ↔ κEquiv x < κEquiv y :=
  Iff.rfl

theorem κEquiv_le (x y : κ) :
    x ≤ y ↔ κEquiv x ≤ κEquiv y :=
  Iff.rfl

theorem κ_zero_le (x : κ) :
    0 ≤ x := by
  rw [κEquiv_le, ← Subtype.coe_le_coe, κEquiv_ofNat, Nat.cast_zero]
  exact Ordinal.zero_le _

instance : CovariantClass κ κ (· + ·) (· ≤ ·) := by
  constructor
  intro i j k h
  rw [κEquiv_le] at h
  rw [κEquiv_le, ← Subtype.coe_le_coe, κEquiv_add, κEquiv_add]
  exact (add_le_add_iff_left _).mpr h

instance : CovariantClass κ κ (· + ·) (· < ·) := by
  constructor
  intro i j k h
  rw [κEquiv_lt] at h
  rw [κEquiv_lt, ← Subtype.coe_lt_coe, κEquiv_add, κEquiv_add]
  exact (add_lt_add_iff_left _).mpr h

instance : CovariantClass κ κ (Function.swap (· + ·)) (· ≤ ·) := by
  constructor
  intro i j k h
  rw [κEquiv_le, ← Subtype.coe_le_coe] at h
  rw [κEquiv_le, ← Subtype.coe_le_coe, κEquiv_add, κEquiv_add]
  exact add_le_add_right h _

theorem κ_le_add (x y : κ) :
    x ≤ x + y :=
  (add_zero x).symm.trans_le (add_le_add le_rfl (κ_zero_le y))

instance : IsLeftCancelAdd κ := by
  constructor
  intro x y z h
  rw [← κEquiv.apply_eq_iff_eq, ← Subtype.coe_inj] at h ⊢
  rw [κEquiv_add, κEquiv_add] at h
  exact (Ordinal.add_left_cancel _).mp h

theorem κ_typein (x : κ) :
    -- TODO: Why can't Lean find this instance?
    letI := inferInstanceAs (IsWellOrder κ (· < ·))
    typein (· < ·) x = κEquiv x := by
  have := κEquiv.ltWellOrder_typein x
  rw [Ordinal.lift_id, typein_Iio, Ordinal.lift_inj] at this
  exact this.symm

theorem κ_card_Iio_eq (x : κ) : #{y | y < x} = (κEquiv x).1.card := by
  rw [Set.coe_setOf, card_typein, κ_typein]

-- TODO: Unify the following two lemmas with the corresponding ones in TypeIndex somehow.

theorem μ_card_Iio_lt (ν : μ) : #{ξ | ξ < ν} < #μ := by
  have := (type_Iio_lt ν).trans_eq μ_type
  rwa [lt_ord] at this

theorem μ_card_Iic_lt (ν : μ) : #{ξ | ξ ≤ ν} < #μ := by
  have := (type_Iic_lt ν).trans_eq μ_type
  rwa [lt_ord] at this

theorem μ_bounded_lt_of_lt_μ_ord_cof (s : Set μ) (h : #s < (#μ).ord.cof) :
    s.Bounded (· < ·) :=
  Ordinal.lt_cof_type (μ_type ▸ h)

theorem card_lt_of_μ_bounded (s : Set μ) (h : s.Bounded (· < ·)) :
    #s < #μ := by
  obtain ⟨ν, hν⟩ := h
  exact (mk_le_mk_of_subset hν).trans_lt (μ_card_Iio_lt ν)

end ConNF
