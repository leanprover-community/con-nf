import ConNF.Mathlib.Group
import Mathlib.GroupTheory.GroupAction.Defs

#align_import mathlib.group_action

/-!
# Pi instances for multiplicative actions

This file defines instances for mul_action and related structures on Pi types.

## See also

* `group_theory.group_action.prod`
* `group_theory.group_action.sigma`
* `group_theory.group_action.sum`
-/


open Pi

universe u v w

variable {I : Prop}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
variable (x y : ∀ i, f i) (i : I)

namespace PiProp

@[to_additive PiProp.hasVadd]
instance hasSmul {α : Type _} [∀ i, SMul α <| f i] : SMul α (∀ i : I, f i) :=
  ⟨fun s x => fun i => s • x i⟩

@[to_additive]
theorem smul_def {α : Type _} [∀ i, SMul α <| f i] (s : α) : s • x = fun i => s • x i :=
  rfl

@[simp, to_additive]
theorem smul_apply {α : Type _} [∀ i, SMul α <| f i] (s : α) : (s • x) i = s • x i :=
  rfl

@[to_additive PiProp.hasVadd']
instance hasSmul' {g : I → Type _} [∀ i, SMul (f i) (g i)] : SMul (∀ i, f i) (∀ i : I, g i) :=
  ⟨fun s x => fun i => s i • x i⟩

@[simp, to_additive]
theorem smul_apply' {g : I → Type _} [∀ i, SMul (f i) (g i)] (s : ∀ i, f i) (x : ∀ i, g i) :
    (s • x) i = s i • x i :=
  rfl

instance isScalarTower {α β : Type _} [SMul α β] [∀ i, SMul β <| f i] [∀ i, SMul α <| f i]
    [∀ i, IsScalarTower α β (f i)] : IsScalarTower α β (∀ i : I, f i) :=
  ⟨fun x y z => funext fun i => smul_assoc x y (z i)⟩

instance is_scalar_tower' {g : I → Type _} {α : Type _} [∀ i, SMul α <| f i] [∀ i, SMul (f i) (g i)]
    [∀ i, SMul α <| g i] [∀ i, IsScalarTower α (f i) (g i)] :
    IsScalarTower α (∀ i : I, f i) (∀ i : I, g i) :=
  ⟨fun x y z => funext fun i => smul_assoc x (y i) (z i)⟩

instance is_scalar_tower'' {g : I → Type _} {h : I → Type _} [∀ i, SMul (f i) (g i)]
    [∀ i, SMul (g i) (h i)] [∀ i, SMul (f i) (h i)] [∀ i, IsScalarTower (f i) (g i) (h i)] :
    IsScalarTower (∀ i, f i) (∀ i, g i) (∀ i, h i) :=
  ⟨fun x y z => funext fun i => smul_assoc (x i) (y i) (z i)⟩

@[to_additive]
instance sMulCommClass {α β : Type _} [∀ i, SMul α <| f i] [∀ i, SMul β <| f i]
    [∀ i, SMulCommClass α β (f i)] : SMulCommClass α β (∀ i : I, f i) :=
  ⟨fun x y z => funext fun i => smul_comm x y (z i)⟩

@[to_additive]
instance smul_comm_class' {g : I → Type _} {α : Type _} [∀ i, SMul α <| g i] [∀ i, SMul (f i) (g i)]
    [∀ i, SMulCommClass α (f i) (g i)] : SMulCommClass α (∀ i : I, f i) (∀ i : I, g i) :=
  ⟨fun x y z => funext fun i => smul_comm x (y i) (z i)⟩

@[to_additive]
instance smul_comm_class'' {g : I → Type _} {h : I → Type _} [∀ i, SMul (g i) (h i)]
    [∀ i, SMul (f i) (h i)] [∀ i, SMulCommClass (f i) (g i) (h i)] :
    SMulCommClass (∀ i, f i) (∀ i, g i) (∀ i, h i) :=
  ⟨fun x y z => funext fun i => smul_comm (x i) (y i) (z i)⟩

instance {α : Type _} [∀ i, SMul α <| f i] [∀ i, SMul αᵐᵒᵖ <| f i] [∀ i, IsCentralScalar α (f i)] :
    IsCentralScalar α (∀ i, f i) :=
  ⟨fun r m => funext fun i => op_smul_eq_smul _ _⟩

/-- If `f i` has a faithful scalar action for a given `i`, then so does `Π i, f i`. This is
not an instance as `i` cannot be inferred. -/
@[to_additive PiProp.has_faithful_vadd_at]
theorem faithfulSMul_at {α : Type _} [∀ i, SMul α <| f i] [∀ i, Nonempty (f i)] (i : I)
    [FaithfulSMul α (f i)] : FaithfulSMul α (∀ i, f i) :=
  ⟨fun x y h =>
    eq_of_smul_eq_smul fun a : f i => by
      classical
      have :=
        congr_fun (h <| Function.update (fun j => Classical.choice (‹∀ i, Nonempty (f i)› j)) i a) i
      simpa using this⟩

@[to_additive PiProp.has_faithful_vadd]
instance faithfulSMul {α : Type _} [Nonempty I] [∀ i, SMul α <| f i] [∀ i, Nonempty (f i)]
    [∀ i, FaithfulSMul α (f i)] : FaithfulSMul α (∀ i, f i) :=
  let ⟨i⟩ := ‹Nonempty I›
  faithfulSMul_at i

@[to_additive]
instance mulAction (α) {m : Monoid α} [∀ i, MulAction α <| f i] : @MulAction α (∀ i : I, f i) m
    where
  smul := (· • ·)
  hMul_smul r s f := funext fun i => hMul_smul _ _ _
  one_smul f := funext fun i => one_smul α _

@[to_additive]
instance mulAction' {g : I → Type _} {m : ∀ i, Monoid (f i)} [∀ i, MulAction (f i) (g i)] :
    @MulAction (∀ i, f i) (∀ i : I, g i) (@PiProp.monoid I f m)
    where
  smul := (· • ·)
  hMul_smul r s f := funext fun i => hMul_smul _ _ _
  one_smul f := funext fun i => one_smul _ _

instance distribMulAction (α) {m : Monoid α} {n : ∀ i, AddMonoid <| f i}
    [∀ i, DistribMulAction α <| f i] :
    @DistribMulAction α (∀ i : I, f i) m (@PiProp.addMonoid I f n) :=
  { PiProp.mulAction _ with
    smul_zero := fun c => funext fun i => smul_zero _
    smul_add := fun c f g => funext fun i => smul_add _ _ _ }

instance distribMulAction' {g : I → Type _} {m : ∀ i, Monoid (f i)} {n : ∀ i, AddMonoid <| g i}
    [∀ i, DistribMulAction (f i) (g i)] :
    @DistribMulAction (∀ i, f i) (∀ i, g i) (@PiProp.monoid I f m) (@PiProp.addMonoid I g n)
    where
  smul_add := by intros; ext x; apply smul_add
  smul_zero := by intros; ext x; apply smul_zero

instance mulDistribMulAction (α) {m : Monoid α} {n : ∀ i, Monoid <| f i}
    [∀ i, MulDistribMulAction α <| f i] :
    @MulDistribMulAction α (∀ i : I, f i) m (@PiProp.monoid I f n) :=
  { PiProp.mulAction _ with
    smul_one := fun c => funext fun i => smul_one _
    smul_hMul := fun c f g => funext fun i => smul_mul' _ _ _ }

instance mulDistribMulAction' {g : I → Type _} {m : ∀ i, Monoid (f i)} {n : ∀ i, Monoid <| g i}
    [∀ i, MulDistribMulAction (f i) (g i)] :
    @MulDistribMulAction (∀ i, f i) (∀ i, g i) (@PiProp.monoid I f m) (@PiProp.monoid I g n)
    where
  smul_hMul := by intros; ext x; apply smul_mul'
  smul_one := by intros; ext x; apply smul_one

end PiProp

namespace FunctionProp

/-- Non-dependent version of `pi_Prop.has_smul`. Lean gets confused by the dependent instance if
this is not present. -/
@[to_additive]
instance hasSmul {ι : Prop} {R M : Type _} [SMul R M] : SMul R (ι → M) :=
  PiProp.hasSmul

/-- Non-dependent version of `pi_Prop.smul_comm_class`. Lean gets confused by the dependent instance
if this is not present. -/
@[to_additive]
instance sMulCommClass {ι : Prop} {α β M : Type _} [SMul α M] [SMul β M] [SMulCommClass α β M] :
    SMulCommClass α β (ι → M) :=
  PiProp.sMulCommClass

end FunctionProp
