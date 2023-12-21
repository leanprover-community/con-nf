import ConNF.Structural.Support
import ConNF.Fuzz.Position

/-!
# Hypotheses for constructing the `fuzz` map

This file contains the inductive hypotheses required for constructing the `fuzz` map.
Even though not everything defined here is strictly necessary for this construction, we bundle
it here for more convenient use later.

## Main declarations

* `ConNF.TangleData`: Data about the model elements at level `α`.
* `ConNF.PositionedTangles`: A function that gives each `α`-tangle a unique position `ν : μ`.
* `ConNF.TypedObjects`: Allows us to encode atoms and near-litters as `α`-tangles.
* `ConNF.BasePositions`: The position of typed atoms and typed near-litters in the position function
    at any level.
-/

open Function Set WithBot

open scoped Pointwise

universe u

namespace ConNF

variable [Params.{u}]

/-- Data about the model elements at level `α`. This class asserts the existence of a type of
tangles at level `α`, and a group of allowable permutations at level `α` that act on the
`α`-tangles. We also stipulate that each tangle has a prescribed small support, called its
designated support. -/
class TangleData (α : TypeIndex) where
  /-- The type of tangles that we assume were constructed at stage `α`.
  Later in the recursion, we will construct this type explicitly, but for now, we will just assume
  that it exists. -/
  (Tangle : Type u)
  /-- The type of allowable permutations that we assume exists on `α`-tangles. -/
  (Allowable : Type u)
  [allowableGroup : Group Allowable]
  allowableToStructPerm : Allowable →* StructPerm α
  [allowableAction : MulAction Allowable Tangle]
  support : Tangle → Support α
  support_supports (t : Tangle) :
    haveI : MulAction Allowable (SupportCondition α) :=
      MulAction.compHom _ allowableToStructPerm
    MulAction.Supports Allowable (support t : Set (SupportCondition α)) t

export TangleData (Tangle Allowable)

attribute [instance] TangleData.allowableGroup TangleData.allowableAction

namespace Allowable

variable {α : TypeIndex} [TangleData α] {X : Type _} [MulAction (StructPerm α) X]

/-- Allowable permutations can be considered a subtype of structural permutations.
This map can be thought of as an inclusion that preserves the group structure. -/
def toStructPerm : Allowable α →* StructPerm α :=
  TangleData.allowableToStructPerm

/-- Allowable permutations act on anything that structural permutations do. -/
instance : MulAction (Allowable α) X :=
  MulAction.compHom _ toStructPerm

theorem toStructPerm_smul (ρ : Allowable α) (x : X) : ρ • x = Allowable.toStructPerm ρ • x :=
  rfl

variable {ρ ρ' : Allowable α} {c : SupportCondition α}

theorem smul_supportCondition :
    ρ • c = ⟨c.path, Allowable.toStructPerm ρ c.path • c.value⟩ :=
  rfl

@[simp]
theorem smul_supportCondition_eq_iff :
    ρ • c = c ↔ Allowable.toStructPerm ρ c.path • c.value = c.value :=
  StructPerm.smul_supportCondition_eq_iff

@[simp]
theorem smul_supportCondition_eq_smul_iff :
    ρ • c = ρ' • c ↔
    Allowable.toStructPerm ρ c.path • c.value = Allowable.toStructPerm ρ' c.path • c.value :=
  StructPerm.smul_supportCondition_eq_smul_iff

end Allowable

/-- For each tangle, we provide a small support for it. This is known as the designated support of
the tangle. -/
def TangleData.Tangle.support {α : TypeIndex} [TangleData α] (t : Tangle α) : Support α :=
  TangleData.support t

theorem support_supports {α : TypeIndex} [TangleData α] (t : Tangle α) :
    MulAction.Supports (Allowable α) (t.support : Set (SupportCondition α)) t :=
  TangleData.support_supports t

class PositionedTangles (α : TypeIndex) [TangleData α] where
  /-- A position function, giving each tangle a unique position `ν : μ`.
  The existence of this injection proves that there are at most `μ` tangles at level `α`.
  Since `μ` has a well-ordering, this induces a well-ordering on `α`-tangles: to compare two
  tangles, simply compare their images under this map. -/
  pos : Tangle α ↪ μ

instance {α : TypeIndex} [TangleData α] [PositionedTangles α] : Position (Tangle α) μ where
  pos := PositionedTangles.pos

variable (α : Λ) [TangleData α]

/-- Allows us to encode atoms and near-litters as `α`-tangles. These maps are expected to cohere
with the conditions given in `BasePositions`, but this requirement is expressed later. -/
class TypedObjects where
  /-- Encode an atom as an `α`-tangle. The resulting model element has a `⊥`-extension which
  contains only this atom. -/
  typedAtom : Atom ↪ Tangle α
  /-- Encode a near-litter as an `α`-tangle. The resulting model element has a `⊥`-extension which
  contains only this near-litter. -/
  typedNearLitter : NearLitter ↪ Tangle α
  smul_typedNearLitter :
    ∀ (ρ : Allowable α) (N : NearLitter),
    ρ • typedNearLitter N =
    typedNearLitter ((Allowable.toStructPerm ρ) (Quiver.Hom.toPath <| bot_lt_coe α) • N)

export TypedObjects (typedAtom typedNearLitter)

namespace Allowable

variable {α}
variable [TypedObjects α]

/-- The action of allowable permutations on tangles commutes with the `typedNearLitter` function
mapping near-litters to typed near-litters. This can be seen by representing tangles as codes. -/
theorem smul_typedNearLitter (ρ : Allowable α) (N : NearLitter) :
    (ρ • typedNearLitter N : Tangle α) =
    typedNearLitter ((Allowable.toStructPerm ρ) (Quiver.Hom.toPath <| bot_lt_coe α) • N) :=
  TypedObjects.smul_typedNearLitter _ _

end Allowable

/-- The tangle data at level `⊥` is constructed by taking the tangles to be the atoms, the allowable
permutations to be near-litter permutations, and the designated supports to be singletons. -/
instance Bot.tangleData : TangleData ⊥
    where
  Tangle := Atom
  Allowable := NearLitterPerm
  allowableToStructPerm := Tree.toBotIso.toMonoidHom
  allowableAction := inferInstance
  support a := ⟨1, fun _ _ => ⟨Quiver.Path.nil, Sum.inl a⟩⟩
  support_supports a π h := by
    simp only [Enumeration.mem_carrier_iff, κ_lt_one_iff, exists_prop, exists_eq_left,
      NearLitterPerm.smul_supportCondition_eq_iff, forall_eq, Sum.smul_inl, Sum.inl.injEq] at h
    exact h

/-- A position function for atoms, which is chosen arbitrarily. -/
noncomputable instance instPositionAtom : Position Atom μ :=
  ⟨Nonempty.some mk_atom.le⟩

/-- The position function at level `⊥`, which is chosen arbitrarily. -/
noncomputable instance Bot.positionedTangles : PositionedTangles ⊥ :=
  ⟨instPositionAtom.pos⟩

/-- The identity equivalence between `⊥`-allowable permutations and near-litter permutations.
This equivalence is a group isomorphism. -/
def _root_.NearLitterPerm.ofBot : Allowable ⊥ ≃ NearLitterPerm :=
  Equiv.refl _

@[simp]
theorem _root_.NearLitterPerm.ofBot_smul {X : Type _} [MulAction NearLitterPerm X]
    (π : Allowable ⊥) (x : X) :
    NearLitterPerm.ofBot π • x = π • x :=
  rfl

end ConNF
