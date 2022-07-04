
import mathlib.group
import group_theory.group_action.defs

/-!
# Pi instances for multiplicative actions

This file defines instances for mul_action and related structures on Pi types.

## See also

* `group_theory.group_action.prod`
* `group_theory.group_action.sigma`
* `group_theory.group_action.sum`
-/

open pi

universes u v w
variable {I : Prop}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

namespace pi_Prop

@[to_additive pi_Prop.has_vadd]
instance has_smul {α : Type*} [Π i, has_smul α $ f i] :
  has_smul α (Π i : I, f i) :=
⟨λ s x, λ i, s • (x i)⟩

@[to_additive]
lemma smul_def {α : Type*} [Π i, has_smul α $ f i] (s : α) : s • x = λ i, s • x i := rfl
@[simp, to_additive]
lemma smul_apply {α : Type*} [Π i, has_smul α $ f i] (s : α) : (s • x) i = s • x i := rfl

@[to_additive pi_Prop.has_vadd']
instance has_smul' {g : I → Type*} [Π i, has_smul (f i) (g i)] :
  has_smul (Π i, f i) (Π i : I, g i) :=
⟨λ s x, λ i, (s i) • (x i)⟩

@[simp, to_additive]
lemma smul_apply' {g : I → Type*} [∀ i, has_smul (f i) (g i)] (s : Π i, f i) (x : Π i, g i) :
  (s • x) i = s i • x i :=
rfl
instance is_scalar_tower {α β : Type*}
  [has_smul α β] [Π i, has_smul β $ f i] [Π i, has_smul α $ f i]
  [Π i, is_scalar_tower α β (f i)] : is_scalar_tower α β (Π i : I, f i) :=
⟨λ x y z, funext $ λ i, smul_assoc x y (z i)⟩

instance is_scalar_tower' {g : I → Type*} {α : Type*}
  [Π i, has_smul α $ f i] [Π i, has_smul (f i) (g i)] [Π i, has_smul α $ g i]
  [Π i, is_scalar_tower α (f i) (g i)] : is_scalar_tower α (Π i : I, f i) (Π i : I, g i) :=
⟨λ x y z, funext $ λ i, smul_assoc x (y i) (z i)⟩

instance is_scalar_tower'' {g : I → Type*} {h : I → Type*}
  [Π i, has_smul (f i) (g i)] [Π i, has_smul (g i) (h i)] [Π i, has_smul (f i) (h i)]
  [Π i, is_scalar_tower (f i) (g i) (h i)] : is_scalar_tower (Π i, f i) (Π i, g i) (Π i, h i) :=
⟨λ x y z, funext $ λ i, smul_assoc (x i) (y i) (z i)⟩

@[to_additive]
instance smul_comm_class {α β : Type*}
  [Π i, has_smul α $ f i] [Π i, has_smul β $ f i] [∀ i, smul_comm_class α β (f i)] :
  smul_comm_class α β (Π i : I, f i) :=
⟨λ x y z, funext $ λ i, smul_comm x y (z i)⟩

@[to_additive]
instance smul_comm_class' {g : I → Type*} {α : Type*}
  [Π i, has_smul α $ g i] [Π i, has_smul (f i) (g i)] [∀ i, smul_comm_class α (f i) (g i)] :
  smul_comm_class α (Π i : I, f i) (Π i : I, g i) :=
⟨λ x y z, funext $ λ i, smul_comm x (y i) (z i)⟩

@[to_additive]
instance smul_comm_class'' {g : I → Type*} {h : I → Type*}
  [Π i, has_smul (g i) (h i)] [Π i, has_smul (f i) (h i)]
  [∀ i, smul_comm_class (f i) (g i) (h i)] : smul_comm_class (Π i, f i) (Π i, g i) (Π i, h i) :=
⟨λ x y z, funext $ λ i, smul_comm (x i) (y i) (z i)⟩

instance {α : Type*} [Π i, has_smul α $ f i] [Π i, has_smul αᵐᵒᵖ $ f i]
  [∀ i, is_central_scalar α (f i)] : is_central_scalar α (Π i, f i) :=
⟨λ r m, funext $ λ i, op_smul_eq_smul _ _⟩

/-- If `f i` has a faithful scalar action for a given `i`, then so does `Π i, f i`. This is
not an instance as `i` cannot be inferred. -/
@[to_additive pi_Prop.has_faithful_vadd_at]
lemma has_faithful_smul_at {α : Type*}
  [Π i, has_smul α $ f i] [Π i, nonempty (f i)] (i : I) [has_faithful_smul α (f i)] :
  has_faithful_smul α (Π i, f i) :=
⟨λ x y h, eq_of_smul_eq_smul $ λ a : f i, begin
  classical,
  have := congr_fun (h $ function.update (λ j, classical.choice (‹Π i, nonempty (f i)› j)) i a) i,
  simpa using this,
end⟩

@[to_additive pi_Prop.has_faithful_vadd]
instance has_faithful_smul {α : Type*}
  [nonempty I] [Π i, has_smul α $ f i] [Π i, nonempty (f i)] [Π i, has_faithful_smul α (f i)] :
  has_faithful_smul α (Π i, f i) :=
let ⟨i⟩ := ‹nonempty I› in has_faithful_smul_at i

@[to_additive]
instance mul_action (α) {m : monoid α} [Π i, mul_action α $ f i] :
  @mul_action α (Π i : I, f i) m :=
{ smul := (•),
  mul_smul := λ r s f, funext $ λ i, mul_smul _ _ _,
  one_smul := λ f, funext $ λ i, one_smul α _ }

@[to_additive]
instance mul_action' {g : I → Type*} {m : Π i, monoid (f i)} [Π i, mul_action (f i) (g i)] :
  @mul_action (Π i, f i) (Π i : I, g i) (@pi.monoid_Prop I f m) :=
{ smul := (•),
  mul_smul := λ r s f, funext $ λ i, mul_smul _ _ _,
  one_smul := λ f, funext $ λ i, one_smul _ _ }

instance distrib_mul_action (α) {m : monoid α} {n : ∀ i, add_monoid $ f i}
  [∀ i, distrib_mul_action α $ f i] :
  @distrib_mul_action α (Π i : I, f i) m (@pi.add_monoid_Prop I f n) :=
{ smul_zero := λ c, funext $ λ i, smul_zero _,
  smul_add := λ c f g, funext $ λ i, smul_add _ _ _,
  ..pi_Prop.mul_action _ }

instance distrib_mul_action' {g : I → Type*} {m : Π i, monoid (f i)} {n : Π i, add_monoid $ g i}
  [Π i, distrib_mul_action (f i) (g i)] :
  @distrib_mul_action (Π i, f i) (Π i, g i) (@pi.monoid_Prop I f m) (@pi.add_monoid_Prop I g n) :=
{ smul_add := by { intros, ext x, apply smul_add },
  smul_zero := by { intros, ext x, apply smul_zero } }

instance mul_distrib_mul_action (α) {m : monoid α} {n : Π i, monoid $ f i}
  [Π i, mul_distrib_mul_action α $ f i] :
  @mul_distrib_mul_action α (Π i : I, f i) m (@pi.monoid_Prop I f n) :=
{ smul_one := λ c, funext $ λ i, smul_one _,
  smul_mul := λ c f g, funext $ λ i, smul_mul' _ _ _,
  ..pi_Prop.mul_action _ }

instance mul_distrib_mul_action' {g : I → Type*} {m : Π i, monoid (f i)} {n : Π i, monoid $ g i}
  [Π i, mul_distrib_mul_action (f i) (g i)] :
  @mul_distrib_mul_action (Π i, f i) (Π i, g i) (@pi.monoid_Prop I f m) (@pi.monoid_Prop I g n) :=
{ smul_mul := by { intros, ext x, apply smul_mul' },
  smul_one := by { intros, ext x, apply smul_one } }

end pi_Prop

namespace function_Prop

/-- Non-dependent version of `pi.has_smul`. Lean gets confused by the dependent instance if this
is not present. -/
@[to_additive]
instance has_smul {ι : Prop} {R M : Type*} [has_smul R M] : has_smul R (ι → M) := pi_Prop.has_smul

/-- Non-dependent version of `pi.smul_comm_class`. Lean gets confused by the dependent instance if
this is not present. -/
@[to_additive]
instance smul_comm_class {ι : Prop} {α β M : Type*} [has_smul α M] [has_smul β M]
  [smul_comm_class α β M] :
  smul_comm_class α β (ι → M) :=
pi_Prop.smul_comm_class

end function_Prop
