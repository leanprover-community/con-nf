import ConNF.Structural.Index

/-!
# Trees

In this file, we define the types of *trees* of a given type `τ`.
For each type index `α`, an `α`-tree of `τ` is a function from `α`-extended type indices to `τ`.

If `τ` has a group structure, the `α`-trees of `τ` can also be given a group structure by
"branchwise" multiplication.

## Main declarations

* `ConNF.Tree`: The type of trees of a given type `τ`.
* `ConNF.Tree.group`: The group structure on trees.
* `ConNF.Tree.comp`: The derivative functor on tree groups.
-/

open Quiver Path

universe u

namespace ConNF

variable [Params.{u}]

/-- For each type index `α`, an `α`-tree of `τ` is a function from `α`-extended type indices to
`τ`. -/
def Tree (τ : Type u) (α : TypeIndex) : Type u :=
  ExtendedIndex α → τ

namespace Tree

variable {τ : Type u}

/-- The equivalence between `τ` and `Tree τ ⊥`. -/
def toBot : τ ≃ Tree τ ⊥
    where
  toFun a := fun _ => a
  invFun a := a nil
  left_inv a := rfl
  right_inv a := by funext A; cases path_eq_nil A; rfl

/-- The equivalence between `Tree τ ⊥` and `τ`. -/
def ofBot : Tree τ ⊥ ≃ τ
    where
  toFun a := a nil
  invFun a := fun _ => a
  left_inv a := by funext A; cases path_eq_nil A; rfl
  right_inv a := rfl

@[simp]
theorem toBot_symm : (toBot.symm : Tree τ ⊥ ≃ τ) = ofBot :=
  rfl

@[simp]
theorem ofBot_symm : (ofBot.symm : τ ≃ Tree τ ⊥) = toBot :=
  rfl

@[simp]
theorem toBot_ofBot (a : Tree τ ⊥) : toBot (ofBot a) = a := by
  funext A
  cases path_eq_nil A
  rfl

@[simp]
theorem ofBot_toBot (a : τ) : ofBot (toBot a) = a := rfl

@[simp]
theorem toBot_inj {a b : τ} : toBot a = toBot b ↔ a = b :=
  toBot.injective.eq_iff

@[simp]
theorem ofBot_inj {a b : Tree τ ⊥} : ofBot a = ofBot b ↔ a = b :=
  ofBot.injective.eq_iff

@[ext]
theorem ext {α : TypeIndex} (a b : Tree τ α) (h : ∀ A, a A = b A) : a = b :=
  funext h

variable [Group τ] {α : TypeIndex}

/-- The group structure on the type of `α`-trees of `τ` is given by "branchwise" multiplication,
given by `Pi.group`. -/
instance group (α : TypeIndex) : Group (Tree τ α) :=
  Pi.group

@[simp]
theorem one_apply (A : ExtendedIndex α) : (1 : Tree τ α) A = 1 := rfl

@[simp]
theorem mul_apply (a a' : Tree τ α) (A : ExtendedIndex α) :
    (a * a') A = a A * a' A :=
  rfl

@[simp]
theorem inv_apply (a : Tree τ α) (A : ExtendedIndex α) :
    a⁻¹ A = (a A)⁻¹ :=
  rfl

/-- The group isomorphism between `τ` and `Tree ⊥ τ`. -/
def toBotIso : τ ≃* Tree τ ⊥
    where
  __ := toBot
  map_mul' := fun _ _ => rfl

@[simp]
theorem coe_toBotIso : (toBotIso : τ → Tree τ ⊥) = toBot :=
  rfl

@[simp]
theorem coe_toBotIso_symm : (toBotIso.symm : Tree τ ⊥ → τ) = ofBot :=
  rfl

@[simp]
theorem toBot_one : toBot (1 : τ) = 1 :=
  toBotIso.map_one

@[simp]
theorem ofBot_one : ofBot (1 : Tree τ ⊥) = 1 :=
  toBotIso.symm.map_one

@[simp]
theorem toBot_mul (a a' : τ) : toBot (a * a') = toBot a * toBot a' :=
  toBotIso.map_mul _ _

@[simp]
theorem ofBot_mul (a a' : Tree τ ⊥) : ofBot (a * a') = ofBot a * ofBot a' :=
  toBotIso.symm.map_mul _ _

@[simp]
theorem toBot_inv (a : τ) : toBot a⁻¹ = (toBot a)⁻¹ :=
  id toBotIso.map_inv a

@[simp]
theorem ofBot_inv (a : Tree τ ⊥) : ofBot a⁻¹ = (ofBot a)⁻¹ :=
  (toBotIso (τ := τ)).symm.map_inv a

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
For a path from `α` to `β`, this is a map from `α`-trees of `τ` to `β`-trees of `τ`.

This is a functor from the category of type indices where
the morphisms are the decreasing paths (i.e. the category where morphisms are elements of `Path α β`
for `α, β : TypeIndex`) to the category of all trees of a fixed type `τ`, where the morphisms are
functions.

If `τ` has a group structure, this map preserves multiplication. This means that we can treat this
as a functor to the category of all trees on `τ` where the morphisms are group homomorphisms. -/
def comp (A : Path α β) (a : Tree τ α) : Tree τ β :=
  fun B => a (A.comp B)

theorem comp_def (A : Path α β) (a : Tree τ α) :
    comp A a = fun B => a (A.comp B) :=
  rfl

/-- Evaluating the derivative of a structural group element along a path is the same as evaluating
the original element along the composition of the paths. -/
@[simp]
theorem comp_apply (a : Tree τ α) (A : Path α β) (B : ExtendedIndex β) :
    comp A a B = a (A.comp B) :=
  rfl

/-- The derivative along the empty path does nothing. -/
@[simp]
theorem comp_nil (a : Tree τ α) : comp nil a = a := by
  simp only [comp_def, nil_comp, MonoidHom.coe_mk, OneHom.coe_mk]

theorem comp_cons (a : Tree τ α) (p : Path α β) {γ : TypeIndex} (h : γ < β) :
    comp (p.cons h) a = (comp (Hom.toPath h)) (comp p a) := by
  simp only [comp_def, MonoidHom.coe_mk, OneHom.coe_mk, Hom.comp_toPath_comp]

/-- The derivative map is functorial. -/
theorem comp_comp (a : Tree τ α) (p : Path α β) (q : Path β γ) :
    comp q (comp p a) = comp (p.comp q) a := by
  simp only [comp_def, MonoidHom.coe_mk, OneHom.coe_mk, comp_assoc]

/-- The derivative map preserves the identity. -/
@[simp]
theorem comp_one {β : TypeIndex} (A : Path (α : TypeIndex) β) :
    comp A (1 : Tree τ α) = 1 :=
  rfl

/-- The derivative map preserves multiplication. -/
theorem comp_mul {β : TypeIndex} (a₁ a₂ : Tree τ α) (A : Path (α : TypeIndex) β) :
    comp A (a₁ * a₂) = comp A a₁ * comp A a₂ :=
  rfl

/-- The derivative map preserves inverses. -/
theorem comp_inv {β : TypeIndex} (a : Tree τ α) (A : Path (α : TypeIndex) β) :
    (comp A a)⁻¹ = comp A a⁻¹ :=
  rfl

@[simp]
theorem comp_bot (a : Tree τ α) (A : Path (α : TypeIndex) ⊥) :
    comp A a = toBot (a A) := by
  funext B
  cases path_eq_nil B
  rfl

section

variable {X : Type _} [MulAction τ X]

/-- `⊥`-trees on `τ` can act on everything that `τ` can. -/
instance : MulAction (Tree τ ⊥) X :=
  MulAction.compHom X toBotIso.symm.toMonoidHom

@[simp]
theorem toBot_smul (a : τ) (x : X) : toBot a • x = a • x := by
  rfl

@[simp]
theorem ofBot_smul (a : Tree τ ⊥) (x : X) : ofBot a • x = a • x := by
  rfl

@[simp]
theorem toBot_inv_smul (a : τ) (x : X) : (toBot a)⁻¹ • x = a⁻¹ • x := by
  rfl

@[simp]
theorem ofBot_inv_smul (a : Tree τ ⊥) (x : X) : (ofBot a)⁻¹ • x = a⁻¹ • x := by
  rfl

end

end Tree

end ConNF
