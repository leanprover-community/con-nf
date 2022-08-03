import algebra.group.pi

/-!
# Pi instances for groups and monoids

This file defines instances for group, monoid, semigroup and related structures on Pi types.
-/

universes u v w
variables {I : Prop} {f : I → Type v}

namespace pi_Prop

/-! `1`, `0`, `+`, `*`, `-`, `⁻¹`, and `/` are defined pointwise. -/

@[to_additive] instance has_one [Π i, has_one $ f i] : has_one (Π i, f i) := ⟨λ _, 1⟩

@[to_additive] instance has_mul [Π i, has_mul $ f i] : has_mul (Π i, f i) :=
⟨λ f g i, f i * g i⟩

@[to_additive] instance has_inv [Π i, has_inv $ f i] : has_inv (Π i, f i) :=
⟨λ f i, (f i)⁻¹⟩

@[to_additive] instance has_div [Π i, has_div $ f i] : has_div (Π i, f i) :=
⟨λ f g i, f i / g i⟩

@[simp, to_additive] lemma one_apply [Π i, has_one $ f i] (i : I) : (1 : Π i, f i) i = 1 := rfl

@[to_additive]
instance semigroup [Π i, semigroup $ f i] : semigroup (Π i, f i) :=
by refine_struct { mul := (*), .. }; tactic.pi_instance_derive_field

instance semigroup_with_zero [Π i, semigroup_with_zero $ f i] :
  semigroup_with_zero (Π i, f i) :=
by refine_struct { zero := (0 : Π i, f i), mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive]
instance comm_semigroup [Π i, comm_semigroup $ f i] : comm_semigroup (Π i, f i) :=
by refine_struct { mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive]
instance mul_one_class [Π i, mul_one_class $ f i] : mul_one_class (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive]
instance monoid [Π i, monoid $ f i] : monoid (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := λ n x i, (x i) ^ n };
tactic.pi_instance_derive_field

@[to_additive]
instance comm_monoid [Π i, comm_monoid $ f i] : comm_monoid (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := monoid.npow };
tactic.pi_instance_derive_field

@[to_additive pi_Prop.sub_neg_monoid]
instance div_inv_monoid [Π i, div_inv_monoid $ f i] : div_inv_monoid (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, div := has_div.div,
  npow := monoid.npow, zpow := λ z x i, (x i) ^ z }; tactic.pi_instance_derive_field

@[to_additive]
instance has_involutive_inv [Π i, has_involutive_inv $ f i] : has_involutive_inv (Π i, f i) :=
by refine_struct { inv := has_inv.inv }; tactic.pi_instance_derive_field

@[to_additive pi_Prop.subtraction_monoid]
instance division_monoid [Π i, division_monoid $ f i] : division_monoid (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, div := has_div.div,
  npow := monoid.npow, zpow := λ z x i, (x i) ^ z }; tactic.pi_instance_derive_field

@[to_additive pi_Prop.subtraction_comm_monoid]
instance division_comm_monoid [Π i, division_comm_monoid $ f i] :
  division_comm_monoid (Π i, f i) :=
{ ..pi_Prop.division_monoid, ..pi_Prop.comm_semigroup }

@[to_additive] instance group [Π i, group $ f i] : group (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, div := has_div.div,
  npow := monoid.npow, zpow := div_inv_monoid.zpow }; tactic.pi_instance_derive_field

@[to_additive] instance comm_group [Π i, comm_group $ f i] : comm_group (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, div := has_div.div,
  npow := monoid.npow, zpow := div_inv_monoid.zpow }; tactic.pi_instance_derive_field

@[to_additive add_left_cancel_semigroup]
instance left_cancel_semigroup [Π i, left_cancel_semigroup $ f i] :
  left_cancel_semigroup (Π i, f i) :=
by refine_struct { mul := (*) }; tactic.pi_instance_derive_field

@[to_additive add_right_cancel_semigroup]
instance right_cancel_semigroup [Π i, right_cancel_semigroup $ f i] :
  right_cancel_semigroup (Π i, f i) :=
by refine_struct { mul := (*) }; tactic.pi_instance_derive_field

@[to_additive add_left_cancel_monoid]
instance left_cancel_monoid [Π i, left_cancel_monoid $ f i] :
  left_cancel_monoid (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := monoid.npow };
tactic.pi_instance_derive_field

@[to_additive add_right_cancel_monoid]
instance right_cancel_monoid [Π i, right_cancel_monoid $ f i] :
  right_cancel_monoid (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := monoid.npow, .. };
tactic.pi_instance_derive_field

@[to_additive add_cancel_monoid]
instance cancel_monoid [Π i, cancel_monoid $ f i] : cancel_monoid (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := monoid.npow };
tactic.pi_instance_derive_field

@[to_additive add_cancel_comm_monoid]
instance cancel_comm_monoid [Π i, cancel_comm_monoid $ f i] : cancel_comm_monoid (Π i, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), npow := monoid.npow };
tactic.pi_instance_derive_field

instance mul_zero_class [Π i, mul_zero_class $ f i] : mul_zero_class (Π i, f i) :=
by refine_struct { zero := (0 : Π i, f i), mul := (*), .. }; tactic.pi_instance_derive_field

instance mul_zero_one_class [Π i, mul_zero_one_class $ f i] :
  mul_zero_one_class (Π i, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := (1 : Π i, f i), mul := (*), .. };
  tactic.pi_instance_derive_field

instance monoid_with_zero [Π i, monoid_with_zero $ f i] :
  monoid_with_zero (Π i, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := (1 : Π i, f i), mul := (*),
  npow := monoid.npow }; tactic.pi_instance_derive_field

instance comm_monoid_with_zero [Π i, comm_monoid_with_zero $ f i] :
  comm_monoid_with_zero (Π i, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := (1 : Π i, f i), mul := (*),
  npow := monoid.npow }; tactic.pi_instance_derive_field

end pi_Prop
