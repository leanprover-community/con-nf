import ConNF.Structural.Index

/-!
# Structural groups

In this file, we define the *structural groups* of a given group `G`.
For each type index `α`, the `α`th structural group of `G` is the group of functions from
`α`-extended type indices to `G`, under pointwise multiplication.

## Main declarations

* `ConNF.Structural`: The structural groups of a given group `G`.
* `ConNF.Structural.comp`: The derivative functor on structural groups.
-/


open Quiver Path

universe u

namespace ConNF

variable [Params.{u}]

/-- For each type index `α`, the `α`th structural group of `G` is the group of functions from
`α`-extended type indices to `G`, under pointwise multiplication. -/
def Structural (G : Type u) (α : TypeIndex) : Type u :=
  ExtendedIndex α → G

namespace Structural

variable {G : Type u}

/-- The equivalence between `G` and `Structural G ⊥`. -/
def toBot : G ≃ Structural G ⊥
    where
  toFun a := fun _ => a
  invFun a := a nil
  left_inv a := rfl
  right_inv a := by funext A; cases path_eq_nil A; rfl

/-- The equivalence between `Structural G ⊥` and `G`. -/
def ofBot : Structural G ⊥ ≃ G
    where
  toFun a := a nil
  invFun a := fun _ => a
  left_inv a := by funext A; cases path_eq_nil A; rfl
  right_inv a := rfl

@[simp]
theorem toBot_symm : (toBot.symm : Structural G ⊥ ≃ G) = ofBot :=
  rfl

@[simp]
theorem ofBot_symm : (ofBot.symm : G ≃ Structural G ⊥) = toBot :=
  rfl

@[simp]
theorem toBot_ofBot (a : Structural G ⊥) : toBot (ofBot a) = a := by
  funext A
  cases path_eq_nil A
  rfl

@[simp]
theorem ofBot_toBot (a : G) : ofBot (toBot a) = a := rfl

@[simp]
theorem toBot_inj {a b : G} : toBot a = toBot b ↔ a = b :=
  toBot.injective.eq_iff

@[simp]
theorem ofBot_inj {a b : Structural G ⊥} : ofBot a = ofBot b ↔ a = b :=
  ofBot.injective.eq_iff

variable [Group G] {α : TypeIndex}

/-- The group structure on the `α`th structural group of `G` is given by pointwise multiplication,
see `Pi.group`. -/
instance group (α : TypeIndex) : Group (Structural G α) :=
  Pi.group

@[simp]
theorem one_apply (A : ExtendedIndex α) : (1 : Structural G α) A = 1 := rfl

@[simp]
theorem mul_apply (a a' : Structural G α) (A : ExtendedIndex α) :
    (a * a') A = a A * a' A :=
  rfl

@[simp]
theorem inv_apply (a : Structural G α) (A : ExtendedIndex α) :
    a⁻¹ A = (a A)⁻¹ :=
  rfl

/-- The group isomorphism between `G` and `Structural ⊥ G`. -/
def toBotIso : G ≃* Structural G ⊥
    where
  __ := toBot
  map_mul' := fun _ _ => rfl

@[simp]
theorem coe_toBotIso : (toBotIso : G → Structural G ⊥) = toBot :=
  rfl

@[simp]
theorem coe_toBotIso_symm : (toBotIso.symm : Structural G ⊥ → G) = ofBot :=
  rfl

@[simp]
theorem toBot_one : toBot (1 : G) = 1 :=
  toBotIso.map_one

@[simp]
theorem ofBot_one : ofBot (1 : Structural G ⊥) = 1 :=
  toBotIso.symm.map_one

@[simp]
theorem toBot_mul (a a' : G) : toBot (a * a') = toBot a * toBot a' :=
  toBotIso.map_mul _ _

@[simp]
theorem ofBot_mul (a a' : Structural G ⊥) : ofBot (a * a') = ofBot a * ofBot a' :=
  toBotIso.symm.map_mul _ _

@[simp]
theorem toBot_inv (a : G) : toBot a⁻¹ = (toBot a)⁻¹ :=
  id toBotIso.map_inv a

@[simp]
theorem ofBot_inv (a : Structural G ⊥) : ofBot a⁻¹ = (ofBot a)⁻¹ :=
  toBotIso.symm.map_inv a

variable {α β γ : TypeIndex}

@[simp]
theorem _root_.Quiver.Hom.comp_toPath {V : Type _} [Quiver V] {a b c : V}
    {p : Path a b} {e : b ⟶ c} :
    p.comp e.toPath = p.cons e := rfl

@[simp]
theorem _root_.Quiver.Hom.comp_toPath_comp {V : Type _} [Quiver V] {a b c d : V}
    {p : Path a b} {e : b ⟶ c} {q : Path c d} :
    p.comp (e.toPath.comp q) = (p.cons e).comp q := by
  rw [Hom.toPath, ← comp_assoc, comp_cons, comp_nil]

/-- The *derivative* functor.
For a path from `α` to `β`, this is a map from the `α`th structural group of `G` to its `β`th
structural group.

This is a functor from the category of type indices where the morphisms are the decreasing paths
(i.e. the category where morphisms are elements of `Path α β` for `α, β : TypeIndex`) to the
category of structural groups of a fixed group `G` where the morphisms are group homomorphisms. -/
def comp (A : Path α β) (a : Structural G α) : Structural G β :=
  fun B => a (A.comp B)

/-- Evaluating the derivative of a structural group element along a path is the same as evaluating
the original element along the composition of the paths. -/
@[simp]
theorem comp_apply (a : Structural G α) (A : Path α β) (B : ExtendedIndex β) :
    comp A a B = a (A.comp B) :=
  rfl

/-- The derivative along the empty path does nothing. -/
@[simp]
theorem comp_nil (a : Structural G α) : comp nil a = a := by
  simp only [comp, nil_comp, MonoidHom.coe_mk, OneHom.coe_mk]

theorem comp_cons (a : Structural G α) (p : Path α β) {γ : TypeIndex} (h : γ < β) :
    comp (p.cons h) a = (comp (Hom.toPath h)) (comp p a) := by
  simp only [comp, MonoidHom.coe_mk, OneHom.coe_mk, Hom.comp_toPath_comp]

/-- The derivative map is functorial. -/
theorem comp_comp (a : Structural G α) (p : Path α β) (q : Path β γ) :
    comp q (comp p a) = comp (p.comp q) a := by
  simp only [comp, MonoidHom.coe_mk, OneHom.coe_mk, comp_assoc]

/-- The derivative map preserves multiplication. -/
theorem comp_mul {β : TypeIndex} (a₁ a₂ : Structural G α) (A : Path (α : TypeIndex) β) :
    comp A (a₁ * a₂) = comp A a₁ * comp A a₂ :=
  rfl

/-- The derivative map preserves inverses. -/
theorem comp_inv {β : TypeIndex} (a : Structural G α) (A : Path (α : TypeIndex) β) :
    (comp A a)⁻¹ = comp A a⁻¹ :=
  rfl

@[simp]
theorem comp_bot (a : Structural G α) (A : Path (α : TypeIndex) ⊥) :
    comp A a = toBot (a A) := by
  funext B
  cases path_eq_nil B
  rfl

section

variable {X : Type _} [MulAction G X]

/-- `⊥`-structural groups on `G` can act on everything that `G` can. -/
instance : MulAction (Structural G ⊥) X :=
  MulAction.compHom X toBotIso.symm.toMonoidHom

@[simp]
theorem toBot_smul (a : G) (x : X) : toBot a • x = a • x := by
  rfl

@[simp]
theorem ofBot_smul (a : Structural G ⊥) (x : X) : ofBot a • x = a • x := by
  rfl

@[simp]
theorem toBot_inv_smul (a : G) (x : X) : (toBot a)⁻¹ • x = a⁻¹ • x := by
  rfl

@[simp]
theorem ofBot_inv_smul (a : Structural G ⊥) (x : X) : (ofBot a)⁻¹ • x = a⁻¹ • x := by
  rfl

end

end Structural

end ConNF
