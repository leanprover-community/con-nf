import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Pi instances for groups and monoids

This file defines instances for group, monoid, semigroup and related structures on Pi types.
-/


universe u v w

variable {I : Prop} {f : I → Type v}

namespace PiProp

/-! `1`, `0`, `+`, `*`, `-`, `⁻¹`, and `/` are defined pointwise. -/


@[to_additive]
instance hasOne [∀ i, One <| f i] : One (∀ i, f i) :=
  ⟨fun _ => 1⟩

@[to_additive]
instance hasMul [∀ i, Mul <| f i] : Mul (∀ i, f i) :=
  ⟨fun f g i => f i * g i⟩

@[to_additive]
instance hasInv [∀ i, Inv <| f i] : Inv (∀ i, f i) :=
  ⟨fun f i => (f i)⁻¹⟩

@[to_additive]
instance hasDiv [∀ i, Div <| f i] : Div (∀ i, f i) :=
  ⟨fun f g i => f i / g i⟩

@[to_additive (attr := simp)]
theorem one_apply [∀ i, One <| f i] (i : I) : (1 : ∀ i, f i) i = 1 :=
  rfl

@[to_additive]
instance semigroup [∀ i, Semigroup <| f i] : Semigroup (∀ i, f i)
    where
  mul := (· * ·)
  mul_assoc := fun a b c => funext (fun x => mul_assoc (a x) (b x) (c x))

instance semigroupWithZero [∀ i, SemigroupWithZero <| f i] : SemigroupWithZero (∀ i, f i)
    where
  __ := semigroup
  zero := 0
  zero_mul := fun a => funext (fun x => zero_mul (a x))
  mul_zero := fun a => funext (fun x => mul_zero (a x))

@[to_additive]
instance commSemigroup [∀ i, CommSemigroup <| f i] : CommSemigroup (∀ i, f i)
    where
  __ := semigroup
  mul_comm := fun a b => funext (fun x => mul_comm (a x) (b x))

@[to_additive]
instance mulOneClass [∀ i, MulOneClass <| f i] : MulOneClass (∀ i, f i)
    where
  one := 1
  mul := (· * ·)
  one_mul := fun a => funext (fun x => one_mul (a x))
  mul_one := fun a => funext (fun x => mul_one (a x))

@[to_additive]
instance monoid [inst : ∀ i, Monoid <| f i] : Monoid (∀ i, f i)
    where
  __ := semigroup
  __ := mulOneClass
  npow := fun n x i => x i ^ n
  npow_zero := fun a => funext (fun x => (inst x).npow_zero (a x))
  npow_succ := fun n a => funext (fun x => (inst x).npow_succ n (a x))

@[to_additive]
instance commMonoid [∀ i, CommMonoid <| f i] : CommMonoid (∀ i, f i)
    where
  __ := monoid
  __ := commSemigroup

@[to_additive PiProp.subNegMonoid]
instance divInvMonoid [inst : ∀ i, DivInvMonoid <| f i] : DivInvMonoid (∀ i, f i)
    where
  inv := Inv.inv
  div := Div.div
  div_eq_mul_inv := fun a b => funext (fun x => div_eq_mul_inv (a x) (b x))

@[to_additive]
instance hasInvolutiveInv [∀ i, InvolutiveInv <| f i] : InvolutiveInv (∀ i, f i)
    where
  inv := Inv.inv
  inv_inv := fun a => funext (fun x => inv_inv (a x))

@[to_additive PiProp.subtractionMonoid]
instance divisionMonoid [inst : ∀ i, DivisionMonoid <| f i] : DivisionMonoid (∀ i, f i)
    where
  __ := divInvMonoid
  __ := hasInvolutiveInv
  mul_inv_rev := fun a b => funext (fun x => mul_inv_rev (a x) (b x))
  inv_eq_of_mul := fun a b h => funext (fun x => (inst x).inv_eq_of_mul (a x) (b x) (congr_fun h x))

@[to_additive PiProp.subtractionCommMonoid]
instance divisionCommMonoid [∀ i, DivisionCommMonoid <| f i] : DivisionCommMonoid (∀ i, f i)
    where
  __ := divisionMonoid
  __ := commMonoid

@[to_additive]
instance group [∀ i, Group <| f i] : Group (∀ i, f i)
    where
  __ := divisionMonoid
  mul_left_inv := fun a => funext (fun x => mul_left_inv (a x))

@[to_additive]
instance commGroup [∀ i, CommGroup <| f i] : CommGroup (∀ i, f i)
    where
  __ := group
  __ := commMonoid

@[to_additive AddLeftCancelSemigroup]
instance leftCancelSemigroup [inst : ∀ i, LeftCancelSemigroup <| f i] :
    LeftCancelSemigroup (∀ i, f i)
    where
  __ := semigroup
  mul_left_cancel := fun a b c h => funext
    (fun x => (inst x).mul_left_cancel (a x) (b x) (c x) (congr_fun h x))

@[to_additive AddRightCancelSemigroup]
instance rightCancelSemigroup [inst : ∀ i, RightCancelSemigroup <| f i] :
    RightCancelSemigroup (∀ i, f i)
    where
  __ := semigroup
  mul_right_cancel := fun a b c h => funext
    (fun x => (inst x).mul_right_cancel (a x) (b x) (c x) (congr_fun h x))

@[to_additive AddLeftCancelMonoid]
instance leftCancelMonoid [∀ i, LeftCancelMonoid <| f i] : LeftCancelMonoid (∀ i, f i)
    where
  __ := monoid
  __ := leftCancelSemigroup

@[to_additive AddRightCancelMonoid]
instance rightCancelMonoid [∀ i, RightCancelMonoid <| f i] : RightCancelMonoid (∀ i, f i)
    where
  __ := monoid
  __ := rightCancelSemigroup

@[to_additive AddCancelMonoid]
instance cancelMonoid [∀ i, CancelMonoid <| f i] : CancelMonoid (∀ i, f i)
    where
  __ := leftCancelMonoid
  __ := rightCancelMonoid

@[to_additive AddCancelCommMonoid]
instance cancelCommMonoid [∀ i, CancelCommMonoid <| f i] : CancelCommMonoid (∀ i, f i)
    where
  __ := cancelMonoid
  __ := commMonoid

instance mulZeroClass [∀ i, MulZeroClass <| f i] : MulZeroClass (∀ i, f i)
    where
  zero := 0
  mul := (· * ·)
  zero_mul := fun a => funext (fun x => zero_mul (a x))
  mul_zero := fun a => funext (fun x => mul_zero (a x))

instance mulZeroOneClass [∀ i, MulZeroOneClass <| f i] : MulZeroOneClass (∀ i, f i)
    where
  __ := mulOneClass
  __ := mulZeroClass

instance monoidWithZero [∀ i, MonoidWithZero <| f i] : MonoidWithZero (∀ i, f i)
    where
  __ := monoid
  __ := mulZeroClass

instance commMonoidWithZero [∀ i, CommMonoidWithZero <| f i] : CommMonoidWithZero (∀ i, f i)
    where
  __ := commMonoid
  __ := mulZeroClass

end PiProp
