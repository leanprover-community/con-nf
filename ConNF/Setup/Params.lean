import ConNF.Aux.Cardinal
import ConNF.Aux.Ordinal
import ConNF.Aux.Transfer
import ConNF.Aux.WellOrder

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

class Params where
  Λ : Type u
  κ : Type u
  μ : Type u
  [ΛWellOrder : LtWellOrder Λ]
  [Λ_noMaxOrder : NoMaxOrder Λ]
  aleph0_lt_κ : ℵ₀ < #κ
  κ_isRegular : (#κ).IsRegular
  μ_isStrongLimit : (#μ).IsStrongLimit
  κ_lt_μ : #κ < #μ
  κ_le_cof_μ : #κ ≤ (#μ).ord.cof
  Λ_le_cof_μ : type ((· < ·) : Λ → Λ → Prop) ≤ (#μ).ord.cof.ord

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
  Λ_le_cof_μ := by
    rw [type_nat_lt, mk_out]
    have := beth_normal.cof_le (aleph 1).ord
    rw [isRegular_aleph_one.cof_eq, ← ord_le_ord] at this
    exact (omega_le_of_isLimit (ord_aleph_isLimit 1)).trans this

def inaccessibleParams.{v} : Params where
  Λ := (Cardinal.univ.{v, v + 1}).ord.out.α
  κ := ULift.{v + 1, v} (aleph 1).out
  μ := Cardinal.univ.{v, v + 1}.out
  Λ_noMaxOrder := by
    apply noMaxOrder_of_ordinal_type_eq
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
  Λ_le_cof_μ := by
    change type (Cardinal.univ.{v, v + 1}).ord.out.r ≤ _
    rw [type_out, mk_out, univ_inaccessible.2.1.cof_eq]

export Params (Λ κ μ aleph0_lt_κ κ_isRegular μ_isStrongLimit κ_lt_μ κ_le_cof_μ Λ_le_cof_μ)

variable [Params.{u}]

instance : LtWellOrder Λ := Params.ΛWellOrder
instance : NoMaxOrder Λ := Params.Λ_noMaxOrder

theorem aleph0_lt_μ : ℵ₀ < #μ :=
  aleph0_lt_κ.trans κ_lt_μ

theorem type_Λ_le_μ_ord : type ((· < ·) : Λ → Λ → Prop) ≤ (#μ).ord :=
  Λ_le_cof_μ.trans <| ord_cof_le (#μ).ord

opaque κEquiv : κ ≃ Set.Iio (#κ).ord := by
  apply Equiv.ulift.{u + 1, u}.symm.trans
  apply Nonempty.some
  rw [← Cardinal.eq, mk_uLift, card_Iio, card_ord]

opaque μEquiv : μ ≃ Set.Iio (#μ).ord := by
  apply Equiv.ulift.{u + 1, u}.symm.trans
  apply Nonempty.some
  rw [← Cardinal.eq, mk_uLift, card_Iio, card_ord]

instance : LtWellOrder κ := Equiv.ltWellOrder κEquiv
instance : LtWellOrder μ := Equiv.ltWellOrder μEquiv

@[simp]
theorem κ.type : type ((· < ·) : κ → κ → Prop) = (#κ).ord := by
  have := κEquiv.ltWellOrder_type
  rwa [Ordinal.lift_id, type_iio, Ordinal.lift_inj] at this

@[simp]
theorem μ.type : type ((· < ·) : μ → μ → Prop) = (#μ).ord := by
  have := μEquiv.ltWellOrder_type
  rwa [Ordinal.lift_id, type_iio, Ordinal.lift_inj] at this

instance : AddMonoid κ :=
  letI := iioAddMonoid aleph0_lt_κ.le
  Equiv.addMonoid κEquiv

instance : Sub κ :=
  letI := iioSub (#κ).ord
  Equiv.sub κEquiv

theorem κ.add_def (x y : κ) :
    letI := iioAddMonoid aleph0_lt_κ.le
    x + y = κEquiv.symm (κEquiv x + κEquiv y) :=
  rfl

theorem κ.sub_def (x y : κ) :
    letI := iioSub (#κ).ord
    x - y = κEquiv.symm (κEquiv x - κEquiv y) :=
  rfl

theorem κ.κEquiv_add (x y : κ) :
    (κEquiv (x + y) : Ordinal) = (κEquiv x : Ordinal) + κEquiv y := by
  rw [κ.add_def, Equiv.apply_symm_apply]
  rfl

theorem κ.κEquiv_sub (x y : κ) :
    (κEquiv (x - y) : Ordinal) = (κEquiv x : Ordinal) - κEquiv y := by
  rw [κ.sub_def, Equiv.apply_symm_apply]
  rfl

end ConNF
