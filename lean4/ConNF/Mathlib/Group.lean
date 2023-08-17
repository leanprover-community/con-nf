import Mathbin.Algebra.Group.Pi

#align_import mathlib.group

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

@[simp, to_additive]
theorem one_apply [∀ i, One <| f i] (i : I) : (1 : ∀ i, f i) i = 1 :=
  rfl

@[to_additive]
instance semigroup [∀ i, Semigroup <| f i] : Semigroup (∀ i, f i) := by
  refine_struct { mul := (· * ·) .. } <;> pi_instance_derive_field

instance semigroupWithZero [∀ i, SemigroupWithZero <| f i] : SemigroupWithZero (∀ i, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        mul := (· * ·) .. } <;>
    pi_instance_derive_field

@[to_additive]
instance commSemigroup [∀ i, CommSemigroup <| f i] : CommSemigroup (∀ i, f i) := by
  refine_struct { mul := (· * ·) .. } <;> pi_instance_derive_field

@[to_additive]
instance mulOneClass [∀ i, MulOneClass <| f i] : MulOneClass (∀ i, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·) .. } <;>
    pi_instance_derive_field

@[to_additive]
instance monoid [∀ i, Monoid <| f i] : Monoid (∀ i, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := fun n x i => x i ^ n } <;>
    pi_instance_derive_field

@[to_additive]
instance commMonoid [∀ i, CommMonoid <| f i] : CommMonoid (∀ i, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field

@[to_additive PiProp.subNegMonoid]
instance divInvMonoid [∀ i, DivInvMonoid <| f i] : DivInvMonoid (∀ i, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        inv := Inv.inv
        div := Div.div
        npow := Monoid.npow
        zpow := fun z x i => x i ^ z } <;>
    pi_instance_derive_field

@[to_additive]
instance hasInvolutiveInv [∀ i, InvolutiveInv <| f i] : InvolutiveInv (∀ i, f i) := by
  refine_struct { inv := Inv.inv } <;> pi_instance_derive_field

@[to_additive PiProp.subtractionMonoid]
instance divisionMonoid [∀ i, DivisionMonoid <| f i] : DivisionMonoid (∀ i, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        inv := Inv.inv
        div := Div.div
        npow := Monoid.npow
        zpow := fun z x i => x i ^ z } <;>
    pi_instance_derive_field

@[to_additive PiProp.subtractionCommMonoid]
instance divisionCommMonoid [∀ i, DivisionCommMonoid <| f i] : DivisionCommMonoid (∀ i, f i) :=
  { PiProp.divisionMonoid, PiProp.commSemigroup with }

@[to_additive]
instance group [∀ i, Group <| f i] : Group (∀ i, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        inv := Inv.inv
        div := Div.div
        npow := Monoid.npow
        zpow := DivInvMonoid.zpow } <;>
    pi_instance_derive_field

@[to_additive]
instance commGroup [∀ i, CommGroup <| f i] : CommGroup (∀ i, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        inv := Inv.inv
        div := Div.div
        npow := Monoid.npow
        zpow := DivInvMonoid.zpow } <;>
    pi_instance_derive_field

@[to_additive AddLeftCancelSemigroup]
instance leftCancelSemigroup [∀ i, LeftCancelSemigroup <| f i] : LeftCancelSemigroup (∀ i, f i) :=
  by refine_struct { mul := (· * ·) } <;> pi_instance_derive_field

@[to_additive AddRightCancelSemigroup]
instance rightCancelSemigroup [∀ i, RightCancelSemigroup <| f i] :
    RightCancelSemigroup (∀ i, f i) := by
  refine_struct { mul := (· * ·) } <;> pi_instance_derive_field

@[to_additive AddLeftCancelMonoid]
instance leftCancelMonoid [∀ i, LeftCancelMonoid <| f i] : LeftCancelMonoid (∀ i, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field

@[to_additive AddRightCancelMonoid]
instance rightCancelMonoid [∀ i, RightCancelMonoid <| f i] : RightCancelMonoid (∀ i, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow .. } <;>
    pi_instance_derive_field

@[to_additive AddCancelMonoid]
instance cancelMonoid [∀ i, CancelMonoid <| f i] : CancelMonoid (∀ i, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field

@[to_additive AddCancelCommMonoid]
instance cancelCommMonoid [∀ i, CancelCommMonoid <| f i] : CancelCommMonoid (∀ i, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field

instance mulZeroClass [∀ i, MulZeroClass <| f i] : MulZeroClass (∀ i, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        mul := (· * ·) .. } <;>
    pi_instance_derive_field

instance mulZeroOneClass [∀ i, MulZeroOneClass <| f i] : MulZeroOneClass (∀ i, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        one := (1 : ∀ i, f i)
        mul := (· * ·) .. } <;>
    pi_instance_derive_field

instance monoidWithZero [∀ i, MonoidWithZero <| f i] : MonoidWithZero (∀ i, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field

instance commMonoidWithZero [∀ i, CommMonoidWithZero <| f i] : CommMonoidWithZero (∀ i, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field

end PiProp

