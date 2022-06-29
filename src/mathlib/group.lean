import algebra.group.pi

/-!
# Pi instances for groups and monoids

This file defines instances for group, monoid, semigroup and related structures on Pi types.
-/

universes u v w
variables {I : Prop} {f : I → Type v}

namespace pi

/-! `1`, `0`, `+`, `*`, `-`, `⁻¹`, and `/` are defined pointwise. -/

@[to_additive] instance has_one_Prop [Π i, has_one $ f i] : has_one (Π i, f i) := ⟨λ _, 1⟩

@[to_additive] instance has_mul_Prop [Π i, has_mul $ f i] : has_mul (Π i, f i) :=
⟨λ f g i, f i * g i⟩

@[to_additive] instance has_inv_Prop [Π i, has_inv $ f i] : has_inv (Π i, f i) :=
⟨λ f i, (f i)⁻¹⟩

@[to_additive] instance has_div_Prop [Π i, has_div $ f i] : has_div (Π i, f i) :=
⟨λ f g i, f i / g i⟩

@[to_additive]
instance semigroup_Prop [Π i, semigroup $ f i] : semigroup (Π i, f i) :=
by refine_struct { mul := (*), .. }; tactic.pi_instance_derive_field

instance semigroup_with_zero_Prop [Π i, semigroup_with_zero $ f i] :
  semigroup_with_zero (Π i, f i) :=
by refine_struct { zero := (0 : Π i, f i), mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive]
instance comm_semigroup_Prop [Π i, comm_semigroup $ f i] : comm_semigroup (Π i, f i) :=
by refine_struct { mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive]
instance mul_one_class_Prop [Π i, mul_one_class $ f i] : mul_one_class (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive]
instance monoid_Prop [Π i, monoid $ f i] : monoid (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := λ n x i, (x i) ^ n };
tactic.pi_instance_derive_field

@[to_additive]
instance comm_monoid_Prop [Π i, comm_monoid $ f i] : comm_monoid (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := monoid.npow };
tactic.pi_instance_derive_field

@[to_additive pi.sub_neg_monoid_Prop]
instance div_inv_monoid_Prop [Π i, div_inv_monoid $ f i] : div_inv_monoid (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, div := has_div.div,
  npow := monoid.npow, zpow := λ z x i, (x i) ^ z }; tactic.pi_instance_derive_field

@[to_additive]
instance has_involutive_inv_Prop [Π i, has_involutive_inv $ f i] : has_involutive_inv (Π i, f i) :=
by refine_struct { inv := has_inv.inv }; tactic.pi_instance_derive_field

@[to_additive pi.subtraction_monoid_Prop]
instance division_monoid_Prop [Π i, division_monoid $ f i] : division_monoid (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, div := has_div.div,
  npow := monoid.npow, zpow := λ z x i, (x i) ^ z }; tactic.pi_instance_derive_field

@[to_additive pi.subtraction_comm_monoid_Prop]
instance division_comm_monoid_Prop [Π i, division_comm_monoid $ f i] :
  division_comm_monoid (Π i, f i) :=
{ ..pi.division_monoid_Prop, ..pi.comm_semigroup_Prop }

@[to_additive] instance group_Prop [Π i, group $ f i] : group (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, div := has_div.div,
  npow := monoid.npow, zpow := div_inv_monoid.zpow }; tactic.pi_instance_derive_field

@[to_additive] instance comm_group_Prop [Π i, comm_group $ f i] : comm_group (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, div := has_div.div,
  npow := monoid.npow, zpow := div_inv_monoid.zpow }; tactic.pi_instance_derive_field

@[to_additive add_left_cancel_semigroup_Prop]
instance left_cancel_semigroup_Prop [Π i, left_cancel_semigroup $ f i] :
  left_cancel_semigroup (Π i, f i) :=
by refine_struct { mul := (*) }; tactic.pi_instance_derive_field

@[to_additive add_right_cancel_semigroup_Prop]
instance right_cancel_semigroup_Prop [Π i, right_cancel_semigroup $ f i] :
  right_cancel_semigroup (Π i, f i) :=
by refine_struct { mul := (*) }; tactic.pi_instance_derive_field

@[to_additive add_left_cancel_monoid_Prop]
instance left_cancel_monoid_Prop [Π i, left_cancel_monoid $ f i] :
  left_cancel_monoid (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := monoid.npow };
tactic.pi_instance_derive_field

@[to_additive add_right_cancel_monoid_Prop]
instance right_cancel_monoid_Prop [Π i, right_cancel_monoid $ f i] :
  right_cancel_monoid (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := monoid.npow, .. };
tactic.pi_instance_derive_field

@[to_additive add_cancel_monoid_Prop]
instance cancel_monoid_Prop [Π i, cancel_monoid $ f i] : cancel_monoid (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := monoid.npow };
tactic.pi_instance_derive_field

@[to_additive add_cancel_comm_monoid_Prop]
instance cancel_comm_monoid_Prop [Π i, cancel_comm_monoid $ f i] : cancel_comm_monoid (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := monoid.npow };
tactic.pi_instance_derive_field

instance mul_zero_class_Prop [Π i, mul_zero_class $ f i] : mul_zero_class (Π i, f i) :=
by refine_struct { zero := (0 : Π i, f i), mul := (*), .. }; tactic.pi_instance_derive_field

instance mul_zero_one_class_Prop [Π i, mul_zero_one_class $ f i] :
  mul_zero_one_class (Π i, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := (1 : Π i, f i), mul := (*), .. };
  tactic.pi_instance_derive_field

instance monoid_with_zero_Prop [Π i, monoid_with_zero $ f i] :
  monoid_with_zero (Π i, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := (1 : Π i, f i), mul := (*),
  npow := monoid.npow }; tactic.pi_instance_derive_field

instance comm_monoid_with_zero_Prop [Π i, comm_monoid_with_zero $ f i] :
  comm_monoid_with_zero (Π i, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := (1 : Π i, f i), mul := (*),
  npow := monoid.npow }; tactic.pi_instance_derive_field

end pi
