import ConNF.Structural.Support

/-!
# Hypotheses for constructing the `fuzz` map

This file contains the inductive hypotheses required for constructing the `fuzz` map.
Even though not everything defined here is strictly necessary for this construction, we bundle
it here for more convenient use later.

## Main declarations

* `ConNF.TangleData`: Data about the model elements at level `α`.
* `ConNF.PositionFunction`: A function that gives each `α`-tangle a unique position `ν : μ`.
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
  designatedSupport :
    haveI : MulAction Allowable (SupportCondition α) :=
      MulAction.compHom _ allowableToStructPerm
    (t : Tangle) → Support α Allowable t

export TangleData (Tangle Allowable)

attribute [instance] TangleData.allowableGroup TangleData.allowableAction

section

variable {α : TypeIndex} [TangleData α] {X : Type _} [MulAction (StructPerm α) X]

namespace Allowable

/-- Allowable permutations can be considered a subtype of structural permutations.
This map can be thought of as an inclusion that preserves the group structure. -/
def toStructPerm : Allowable α →* StructPerm α :=
  TangleData.allowableToStructPerm

/-- Allowable permutations act on anything that structural permutations do. -/
instance : MulAction (Allowable α) X :=
  MulAction.compHom _ toStructPerm

@[simp]
theorem toStructPerm_smul (f : Allowable α) (x : X) : f • x = Allowable.toStructPerm f • x :=
  rfl

end Allowable

/-- For each tangle, we provide a small support for it. This is known as the designated support of
the tangle. -/
def designatedSupport (t : Tangle α) : Support α (Allowable α) t :=
  TangleData.designatedSupport _

end

class PositionFunction (α : TypeIndex) [TangleData α] where
  /-- A position function, giving each tangle a unique position `ν : μ`.
  The existence of this injection proves that there are at most `μ` tangles at level `α`.
  Since `μ` has a well-ordering, this induces a well-ordering on `α`-tangles: to compare two
  tangles, simply compare their images under this map. -/
  position : Tangle α ↪ μ

export PositionFunction (position)

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

/-- This class stores the position of typed atoms and typed near-litters in the position function
at any level, along with some conditions on these maps. -/
class BasePositions where
  /-- Gives the positions of typed atoms at any level. -/
  typedAtomPosition : Atom ↪ μ
  /-- Gives the positions of typed near-litters at any level. -/
  typedNearLitterPosition : NearLitter ↪ μ
  /-- Typed litters precede typed atoms they contain. -/
  litter_lt :
    ∀ (L : Litter),
      ∀ a ∈ litterSet L, typedNearLitterPosition L.toNearLitter < typedAtomPosition a
  /-- Typed litters precede near-litters to them. -/
  litter_le_nearLitter :
    ∀ N : NearLitter, typedNearLitterPosition N.fst.toNearLitter ≤ typedNearLitterPosition N
  /-- Atoms in the symmetric difference between a near-litter and its corresponding litter
  precede the near-litter. -/
  symmDiff_lt_nearLitter :
    ∀ (N : NearLitter),
      ∀ a ∈ litterSet N.fst ∆ N.snd, typedAtomPosition a < typedNearLitterPosition N

export BasePositions (typedAtomPosition typedNearLitterPosition litter_lt litter_le_nearLitter
    symmDiff_lt_nearLitter)

/-- Typed litters precede near-litters to them. -/
theorem litter_lt_nearLitter [BasePositions] (N : NearLitter) (hN : N.fst.toNearLitter ≠ N) :
    typedNearLitterPosition N.fst.toNearLitter < typedNearLitterPosition N :=
  lt_of_le_of_ne (litter_le_nearLitter N) (typedNearLitterPosition.injective.ne hN)

section Instances

variable {α : Λ} (β : Iio α) [TangleData (iioCoe β)]

instance tangleDataVal : TangleData β.val :=
  ‹TangleData β›

instance tangleDataCoeCoe : TangleData (β : Λ) :=
  ‹TangleData β›

section PositionFunction

variable [PositionFunction (iioCoe β)]

instance positionFunctionVal : PositionFunction β.val :=
  ‹PositionFunction _›

instance positionFunctionCoeCoe : PositionFunction (β : Λ) :=
  ‹PositionFunction _›

end PositionFunction

variable [TypedObjects β]

instance typedObjectsVal : TypedObjects β.val :=
  ‹TypedObjects β›

end Instances

/-- The tangle data at level `⊥` is constructed by taking the tangles to be the atoms, the allowable
permutations to be near-litter permutations, and the designated supports to be singletons. -/
noncomputable instance Bot.tangleData : TangleData ⊥
    where
  Tangle := Atom
  Allowable := NearLitterPerm
  allowableToStructPerm := StructPerm.toBotIso.toMonoidHom
  allowableAction := inferInstance
  designatedSupport a :=
    { carrier := {(Quiver.Path.nil, Sum.inl a)}
      supports := fun π => by
        simp only [mem_singleton_iff, forall_eq]
        intro h
        change (_, Sum.inl _) = (_, Sum.inl _) at h
        simp only [MulEquiv.coe_toMonoidHom, Prod.mk.injEq, Sum.inl.injEq, true_and] at h
        exact h
      small := small_singleton _ }

/-- The position function at level `⊥`, which is chosen arbitrarily. -/
noncomputable instance Bot.positionFunction : PositionFunction ⊥ :=
  ⟨Nonempty.some mk_atom.le⟩

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
