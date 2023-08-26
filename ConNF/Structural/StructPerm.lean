import Mathlib.GroupTheory.GroupAction.Sum
import Mathlib.Logic.Equiv.TransferInstance
import ConNF.Mathlib.GroupAction
import ConNF.Mathlib.Logic
import ConNF.Atom.NearLitterPerm
import ConNF.Structural.Index
import ConNF.Structural.Pretangle

/-!
# Structural permutations

In this file, we define the ambient groups of *structural permutations*.  These will later have
recursively-constructed subgroups of *semi-allowable* and *allowable permutations* which will act on
tangles; we define these larger ambient groups in advance in order to set up their infrastructure of
derivatives and so on independently of the recursion.
-/

open Cardinal Equiv Quiver Quiver.Path Set WithBot

open scoped Cardinal Pointwise

universe u

namespace ConNF

variable [Params.{u}]

-- Note: perhaps should be constructed directly as *groups*, not just types.
/-- A *structural permutation* on a proper type index is defined by its derivatives,
as well as its permutation on atoms. -/
def StructPerm (α : TypeIndex) : Type u :=
  ExtendedIndex α → NearLitterPerm

namespace StructPerm

section

variable {α β : Λ} {γ : TypeIndex}

instance instInhabitedStructPerm (α : TypeIndex) : Inhabited (StructPerm α) :=
  ⟨fun _ => 1⟩

/-- The equivalence between `NearLitterPerm` and `StructPerm ⊥`. -/
def toBot : NearLitterPerm ≃ StructPerm ⊥
    where
  toFun π := fun _ => π
  invFun π := π Path.nil
  left_inv π := rfl
  right_inv π := by funext A; cases path_eq_nil A; rfl

/-- The equivalence between `StructPerm ⊥` and `NearLitterPerm`. -/
def ofBot : StructPerm ⊥ ≃ NearLitterPerm
    where
  toFun π := π Path.nil
  invFun π := fun _ => π
  left_inv π := by funext A; cases path_eq_nil A; rfl
  right_inv π := rfl

@[simp]
theorem toBot_symm : toBot.symm = ofBot :=
  rfl

@[simp]
theorem ofBot_symm : ofBot.symm = toBot :=
  rfl

@[simp]
theorem toBot_ofBot (a : StructPerm ⊥) : toBot (ofBot a) = a := by
  funext A
  cases path_eq_nil A
  rfl

@[simp]
theorem ofBot_toBot (a : NearLitterPerm) : ofBot (toBot a) = a := rfl

@[simp]
theorem toBot_inj {a b} : toBot a = toBot b ↔ a = b :=
  toBot.injective.eq_iff

@[simp]
theorem ofBot_inj {a b} : ofBot a = ofBot b ↔ a = b :=
  ofBot.injective.eq_iff

noncomputable instance group (α : TypeIndex) : Group (StructPerm α) :=
  Pi.group

@[simp]
theorem one_apply (A : ExtendedIndex α) : (1 : StructPerm α) A = 1 := rfl

/-- The isomorphism between near-litter permutations and bottom structural permutations. This holds
by definition of `StructPerm`. -/
def toBotIso : NearLitterPerm ≃* StructPerm ⊥
    where
  __ := toBot
  map_mul' := fun _ _ => rfl

@[simp]
theorem coe_toBotIso : toBotIso = toBot :=
  rfl

@[simp]
theorem coe_toBotIso_symm : toBotIso.symm = ofBot :=
  rfl

@[simp]
theorem toBot_one : toBot 1 = 1 :=
  toBotIso.map_one

@[simp]
theorem ofBot_one : ofBot 1 = 1 :=
  toBotIso.symm.map_one

@[simp]
theorem toBot_mul (a b) : toBot (a * b) = toBot a * toBot b :=
  toBotIso.map_mul _ _

@[simp]
theorem ofBot_mul (a b) : ofBot (a * b) = ofBot a * ofBot b :=
  toBotIso.symm.map_mul _ _

@[simp]
theorem toBot_inv (a) : toBot a⁻¹ = (toBot a)⁻¹ :=
  toBotIso.map_inv _

@[simp]
theorem ofBot_inv (a) : ofBot a⁻¹ = (ofBot a)⁻¹ :=
  toBotIso.symm.map_inv _

end

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
def derivative (A : Path α β) (π : StructPerm α) : StructPerm β :=
  fun B => π (A.comp B)

@[simp]
theorem derivative_apply (π : StructPerm α) (A : Path α β) (B : ExtendedIndex β) :
    derivative A π B = π (A.comp B) :=
  rfl

/-- The derivative along the empty path does nothing. -/
@[simp]
theorem derivative_nil (π : StructPerm α) : derivative nil π = π := by
  simp only [derivative, nil_comp, MonoidHom.coe_mk, OneHom.coe_mk]

theorem derivative_cons (π : StructPerm α) (p : Path α β) {γ : TypeIndex} (h : γ < β) :
    derivative (p.cons h) π = (derivative (Hom.toPath h)) (derivative p π) := by
  simp only [derivative, MonoidHom.coe_mk, OneHom.coe_mk, Hom.comp_toPath_comp]

/-- The derivative map is functorial. -/
theorem derivative_derivative (π : StructPerm α) (p : Path α β) (q : Path β γ) :
    derivative q (derivative p π) = derivative (p.comp q) π := by
  simp only [derivative, MonoidHom.coe_mk, OneHom.coe_mk, comp_assoc]

/-- The derivative map preserves multiplication. -/
theorem derivative_mul {β} (π₁ π₂ : StructPerm α) (A : Path (α : TypeIndex) β) :
    derivative A (π₁ * π₂) = derivative A π₁ * derivative A π₂ :=
  rfl

@[simp]
theorem derivative_bot (π : StructPerm α) (A : Path (α : TypeIndex) ⊥) :
    derivative A π = toBot (π A) := by
  funext B
  cases path_eq_nil B
  rfl

section

variable {X : Type _} [MulAction NearLitterPerm X]

/-- Structural permutations act on atoms. -/
instance : MulAction (StructPerm ⊥) X :=
  MulAction.compHom X (toBotIso.symm : StructPerm ⊥ →* NearLitterPerm)

@[simp]
theorem toBot_smul (f : NearLitterPerm) (x : X) : toBot f • x = f • x := by
  rfl

@[simp]
theorem ofBot_smul (f : StructPerm ⊥) (x : X) : ofBot f • x = f • x := by
  rfl

@[simp]
theorem toBot_inv_smul (f : NearLitterPerm) (x : X) : (toBot f)⁻¹ • x = f⁻¹ • x := by
  rfl

@[simp]
theorem ofBot_inv_smul (f : StructPerm ⊥) (x : X) : (ofBot f)⁻¹ • x = f⁻¹ • x := by
  rfl

@[simp]
theorem smul_nearLitter_fst (π : StructPerm ⊥) (N : NearLitter) : (π • N).fst = π • N.fst :=
  rfl

theorem smul_nearLitter_coe (π : StructPerm ⊥) (N : NearLitter) :
    ((π • N) : Set Atom) = π • (N : Set Atom) :=
  NearLitterPerm.smul_nearLitter_coe (ofBot π) N

theorem smul_nearLitter_snd (π : StructPerm ⊥) (N : NearLitter) :
    ((π • N).2 : Set Atom) = π • (N.2 : Set Atom) :=
  NearLitterPerm.smul_nearLitter_snd (ofBot π) N

end

end StructPerm

end ConNF
