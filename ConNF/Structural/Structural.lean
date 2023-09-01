import ConNF.Structural.Index

open Quiver Path

universe u

namespace ConNF

variable [Params.{u}]

def Structural (τ : Type u) (α : TypeIndex) : Type u :=
  ExtendedIndex α → τ

namespace Structural

variable {τ : Type u}

/-- The equivalence between `τ` and `Structural τ ⊥`. -/
def toBot : τ ≃ Structural τ ⊥
    where
  toFun π := fun _ => π
  invFun π := π nil
  left_inv π := rfl
  right_inv π := by funext A; cases path_eq_nil A; rfl

/-- The equivalence between `Structural τ ⊥` and `τ`. -/
def ofBot : Structural τ ⊥ ≃ τ
    where
  toFun π := π nil
  invFun π := fun _ => π
  left_inv π := by funext A; cases path_eq_nil A; rfl
  right_inv π := rfl

@[simp]
theorem toBot_symm : (toBot.symm : Structural τ ⊥ ≃ τ) = ofBot :=
  rfl

@[simp]
theorem ofBot_symm : (ofBot.symm : τ ≃ Structural τ ⊥) = toBot :=
  rfl

@[simp]
theorem toBot_ofBot (a : Structural τ ⊥) : toBot (ofBot a) = a := by
  funext A
  cases path_eq_nil A
  rfl

@[simp]
theorem ofBot_toBot (a : τ) : ofBot (toBot a) = a := rfl

@[simp]
theorem toBot_inj {a b : τ} : toBot a = toBot b ↔ a = b :=
  toBot.injective.eq_iff

@[simp]
theorem ofBot_inj {a b : Structural τ ⊥} : ofBot a = ofBot b ↔ a = b :=
  ofBot.injective.eq_iff

variable [Group τ] {α : TypeIndex}

instance group (α : TypeIndex) : Group (Structural τ α) :=
  Pi.group

@[simp]
theorem one_apply (A : ExtendedIndex α) : (1 : Structural τ α) A = 1 := rfl

@[simp]
theorem mul_apply (π π' : Structural τ α) (A : ExtendedIndex α) :
    (π * π') A = π A * π' A :=
  rfl

@[simp]
theorem inv_apply (π : Structural τ α) (A : ExtendedIndex α) :
    π⁻¹ A = (π A)⁻¹ :=
  rfl

/-- The group isomorphism between near-litter permutations and `⊥`-structural permutations. -/
def toBotIso : τ ≃* Structural τ ⊥
    where
  __ := toBot
  map_mul' := fun _ _ => rfl

@[simp]
theorem coe_toBotIso : (toBotIso : τ → Structural τ ⊥) = toBot :=
  rfl

@[simp]
theorem coe_toBotIso_symm : (toBotIso.symm : Structural τ ⊥ → τ) = ofBot :=
  rfl

@[simp]
theorem toBot_one : toBot (1 : τ) = 1 :=
  toBotIso.map_one

@[simp]
theorem ofBot_one : ofBot (1 : Structural τ ⊥) = 1 :=
  toBotIso.symm.map_one

@[simp]
theorem toBot_mul (π π' : τ) : toBot (π * π') = toBot π * toBot π' :=
  toBotIso.map_mul _ _

@[simp]
theorem ofBot_mul (π π' : Structural τ ⊥) : ofBot (π * π') = ofBot π * ofBot π' :=
  toBotIso.symm.map_mul _ _

@[simp]
theorem toBot_inv (π : τ) : toBot π⁻¹ = (toBot π)⁻¹ :=
  id toBotIso.map_inv π

@[simp]
theorem ofBot_inv (π : Structural τ ⊥) : ofBot π⁻¹ = (ofBot π)⁻¹ :=
  toBotIso.symm.map_inv π

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

/-- The derivative of a structural permutation at any lower level. -/
def comp (A : Path α β) (π : Structural τ α) : Structural τ β :=
  fun B => π (A.comp B)

@[simp]
theorem comp_apply (π : Structural τ α) (A : Path α β) (B : ExtendedIndex β) :
    comp A π B = π (A.comp B) :=
  rfl

/-- The derivative along the empty path does nothing. -/
@[simp]
theorem comp_nil (π : Structural τ α) : comp nil π = π := by
  simp only [comp, nil_comp, MonoidHom.coe_mk, OneHom.coe_mk]

theorem comp_cons (π : Structural τ α) (p : Path α β) {γ : TypeIndex} (h : γ < β) :
    comp (p.cons h) π = (comp (Hom.toPath h)) (comp p π) := by
  simp only [comp, MonoidHom.coe_mk, OneHom.coe_mk, Hom.comp_toPath_comp]

/-- The comp map is functorial. -/
theorem comp_comp (π : Structural τ α) (p : Path α β) (q : Path β γ) :
    comp q (comp p π) = comp (p.comp q) π := by
  simp only [comp, MonoidHom.coe_mk, OneHom.coe_mk, comp_assoc]

/-- The comp map preserves multiplication. -/
theorem comp_mul {β : TypeIndex} (π₁ π₂ : Structural τ α) (A : Path (α : TypeIndex) β) :
    comp A (π₁ * π₂) = comp A π₁ * comp A π₂ :=
  rfl

@[simp]
theorem comp_bot (π : Structural τ α) (A : Path (α : TypeIndex) ⊥) :
    comp A π = toBot (π A) := by
  funext B
  cases path_eq_nil B
  rfl

section

variable {X : Type _} [MulAction τ X]

/-- `⊥`-structural permutations can act on everything that near-litter permutations can.
In particular, this defines an action on atoms, litters, and near-litters. -/
instance : MulAction (Structural τ ⊥) X :=
  MulAction.compHom X toBotIso.symm.toMonoidHom

@[simp]
theorem toBot_smul (π : τ) (x : X) : toBot π • x = π • x := by
  rfl

@[simp]
theorem ofBot_smul (π : Structural τ ⊥) (x : X) : ofBot π • x = π • x := by
  rfl

@[simp]
theorem toBot_inv_smul (π : τ) (x : X) : (toBot π)⁻¹ • x = π⁻¹ • x := by
  rfl

@[simp]
theorem ofBot_inv_smul (π : Structural τ ⊥) (x : X) : (ofBot π)⁻¹ • x = π⁻¹ • x := by
  rfl

end

end Structural

end ConNF
