import Mathlib.Order.Interval.Set.Infinite
import ConNF.Background.Cardinal
import ConNF.Background.Ordinal
import ConNF.Background.Transfer
import ConNF.Background.WellOrder

/-!
# Model parameters

In this file, we define the parameters that we will use to construct our model of tangled type
theory.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

/-!
## Parameters and examples
-/

/--
The type of model parameters. Specifically, we have:

* a nonempty type `Λ` with a relation `<` that well-orders it, and gives it no maximal element;
* a type `κ` whose cardinality is regular and strictly greater than `ℵ₀`;
* a type `μ` whose cardinality is a strong limit, strictly greater than `κ`, and has cofinality
  at least the cardinality of `κ` and at least the order type of `Λ`.

We write `#α` for the cardinality of any type `α`.

`Λ` will become our sort of type indices in the final model we build. That is, in our type
hierarchy, each inhabitant `α : Λ` will give rise to a type `TSet α` (read
"tangled sets of type `α`"). The element-of relation will be of type
`{α : Λ} → {β : Λ} → β < α → TSet β → TSet α → Prop`; that is, given a proof that `β < α`, and given
sets `x : TSet β` and `y : TSet α`, we have a proposition that asks if `x` is an element of `y`.

`κ` will be a type that delimits "small" sets from "large" sets. By manipulating "large" data,
but only allowing sufficiently "small" things in our model, we will be able to control what the
model is able to know about itself.

`μ` will be the size of each of our type levels `TSet α`. The main technical challenge of the proof
will be to prove this cardinality bound on the sizes of our types. We will not be able to construct
`TSet α` until we have already verified that `TSet β` has cardinality `#μ` for every `β < α`.

Our model parameters are not just cardinals (or ordinals): they are *types* with the given
cardinalities and properties. By doing this, the set-theoretic elements of (for example) `#μ`
correspond directly to inhabitants of the type `μ`.

Note that we use a capital `Λ` instead of a lowercase `λ` as the latter is reserved for anonymous
functions in Lean's syntax.

This structure is registered as a typeclass. This means that, at the start of a file, we can write
`variable [Params.{u}]` to parametrise definitions in our file by a choice of model parameters,
and whenever a definition or theorem involving model parameters is mentioned, Lean will implicitly
assume that we intended this particular set of model parameters without having to write it
ourselves.

Finally, note that our model parameters are parametric over a universe `u`. We will almost never
deal with universe levels in the proof (and in fact we can set `u = 0` without issue), but this
gives us greater generality for almost no cost.
-/
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

/--
The smallest collection of model parameters that we can prove to exist.
Importantly, ZFC (with no inaccessibles) proves that this is a set of model parameters.
We take `Λ = ω, κ = ω₁, μ = ב_ω₁` (of course, up to identification of cardinals and ordinals with
their representative types).
-/
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

/--
We can also instantiate our model parameters with `Λ = μ`. To do this, both `#Λ` and `#μ` will need
to be inaccessible cardinals. We simply pick `κ = ω₁` for convenience.
-/
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

/-!
We now inform Lean that our model parameters should be accessible from the names `Λ`, `κ`, etc.
instead of the longer `Params.Λ` and so on.
-/
export Params (Λ κ μ aleph0_lt_κ κ_isRegular μ_isStrongLimit κ_lt_μ κ_le_μ_ord_cof
  Λ_type_le_μ_ord_cof)

/-! Assume a set of model parameters. -/
variable [Params.{u}]

/-!
## Elementary properties

We now establish the most basic elementary properties about `Λ`, `κ`, and `μ`.
In particular, we will use choice to create well-orderings on `κ` and `μ` whose order types are
initial, and then prove some basic facts about these orders.
-/

instance : Nonempty Λ := Params.Λ_nonempty
instance : LtWellOrder Λ := Params.ΛWellOrder
instance : NoMaxOrder Λ := Params.Λ_noMaxOrder

/-- This gadget allows us to use `termination_by` clauses with `Λ`, which gives us access to more
complicated recursion and induction along `Λ`. -/
instance : WellFoundedRelation Λ where
  rel := (· < ·)
  wf := IsWellFounded.wf

/-! Basic cardinal inequalities between `ℵ₀`, `Λ`, `κ`, `μ`. -/

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

/-! We now construct the aforementioned well-orders on `κ` and `μ`. -/

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
instance : NoMaxOrder κ :=
  letI := iio_noMaxOrder aleph0_lt_κ.le
  Equiv.noMaxOrder κEquiv

/-- We overload Lean's numeric literal syntax so that numbers such as `0` can also be interpreted
as particular inhabitants of `κ`. We could do this for the other cardinal parameters as well, but
we don't need it. -/
instance (n : ℕ) : OfNat κ n :=
  letI := iioOfNat aleph0_lt_κ.le n
  Equiv.ofNat κEquiv n

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

/-- The order type on `κ` really is the initial ordinal for the cardinal `#κ`. -/
@[simp]
theorem κ_type : type ((· < ·) : κ → κ → Prop) = (#κ).ord := by
  have := κEquiv.ltWellOrder_type
  rwa [Ordinal.lift_id, type_Iio, Ordinal.lift_inj] at this

@[simp]
theorem μ_type : type ((· < ·) : μ → μ → Prop) = (#μ).ord := by
  have := μEquiv.ltWellOrder_type
  rwa [Ordinal.lift_id, type_Iio, Ordinal.lift_inj] at this

/-- We define a monoid structure on `κ`, denoted `+`, by passing to the collection of ordinals below
`(#κ).ord` and then computing their sum. -/
instance : AddMonoid κ :=
  letI := iioAddMonoid aleph0_lt_κ.le
  Equiv.addMonoid κEquiv

instance : Sub κ :=
  letI := iioSub (#κ).ord
  Equiv.sub κEquiv

/-! Basic properties about the order and operations on `κ`. -/

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

/-- A set in `μ` that is smaller than the cofinality of `μ` is bounded. -/
theorem μ_bounded_lt_of_lt_μ_ord_cof (s : Set μ) (h : #s < (#μ).ord.cof) :
    s.Bounded (· < ·) :=
  Ordinal.lt_cof_type (μ_type ▸ h)

/-- A partial converse to the previous theorem: a bounded set in `μ` must have cardinality smaller
than `μ` itself. -/
theorem card_lt_of_μ_bounded (s : Set μ) (h : s.Bounded (· < ·)) :
    #s < #μ := by
  obtain ⟨ν, hν⟩ := h
  exact (mk_le_mk_of_subset hν).trans_lt (μ_card_Iio_lt ν)

end ConNF
