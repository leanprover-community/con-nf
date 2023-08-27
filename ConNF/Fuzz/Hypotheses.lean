import ConNF.Structural.Support

/-!
# Phase 1 of the recursion

This file contains the induction hypothesis for the first phase of the recursion. In this phase at
level `α`, we assume phase 1 at all levels `β < α`, but we do not assume any interaction between the
levels. Interaction will be introduced in phase 2.

## Main declarations

* `con_nf.core_PositionedTypedObjects`:
* `con_nf.PositionFunction`:
* `con_nf.TypedObjects`:
* `con_nf.PositionedTypedObjects`: The data for the first phase of the recursion.
-/


open Function Set WithBot

open scoped Pointwise

universe u

namespace ConNF

variable [Params.{u}]

section DefinePositionedTypedObjects

/-- The motor of the initial recursion. This contains the data of tangles and allowable permutations
for phase 1 of the recursion. -/
class TangleData (α : TypeIndex) where
  (Tangle Allowable : Type u)
  [allowableGroup : Group Allowable]
  allowableToStructPerm : Allowable →* StructPerm α
  [allowableAction : MulAction Allowable Tangle]
  designatedSupport :
    haveI : MulAction Allowable (SupportCondition α) :=
      MulAction.compHom _ allowableToStructPerm
    (t : Tangle) → Support α Allowable t

attribute [instance] TangleData.allowableGroup TangleData.allowableAction

section

variable (α : TypeIndex) [TangleData α]

/-- The type of tangles that we assume were constructed at stage `α`.
Later in the recursion, we will construct this type explicitly, but for now, we will just assume
that it exists.
Fields in `PositionedTypedObjects` give more information about this type. -/
def Tangle : Type u :=
  TangleData.Tangle α

/-- The type of allowable permutations that we assume exists on `α`-tangles. -/
def Allowable : Type u :=
  TangleData.Allowable α

/-- Allowable permutations at level `α` forms a group with respect to function composition. Note
that at this stage in the recursion, we have not established that the allowable permutations on
`α`-tangles are actually (coercible to) functions, so we cannot compose them with the `∘` symbol; we
must instead use group multiplication `*`. -/
instance : Group (Allowable α) :=
  TangleData.allowableGroup

variable {α} {X : Type _} [MulAction (StructPerm α) X]

namespace Allowable

/-- Allowable permutations can be considered a subtype of structural permutations. However, we
cannot write this explicitly in type theory, so instead we assume this monoid homomorphism from
allowable permutations to structural permutations. This can be thought of as an inclusion map that
preserves the group structure. -/
def toStructPerm : Allowable α →* StructPerm α :=
  TangleData.allowableToStructPerm

instance : MulAction (Allowable α) (Tangle α) :=
  TangleData.allowableAction

/-- Allowable permutations act on tangles. This action commutes with certain other operations; the
exact condition are given in `smul_typed_near_litter`. -/
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

/-- The motor of the initial recursion. This contains the data of the position function. -/
class PositionFunction (α : TypeIndex) [TangleData α] where
  position : Tangle α ↪ μ

export PositionFunction (position)

variable (α : Λ) [TangleData α]

/-- The motor of the initial recursion. This contains the data of the injection to all the
information needed for phase 1 of the recursion. -/
class TypedObjects where
  typedAtom : Atom ↪ Tangle α
  typedNearLitter : NearLitter ↪ Tangle α
  smul_typedNearLitter :
    ∀ (π : Allowable α) (N : NearLitter),
    π • typedNearLitter N =
    typedNearLitter ((Allowable.toStructPerm π) (Quiver.Hom.toPath <| bot_lt_coe α) • N)

export TypedObjects (typedAtom typedNearLitter)

namespace Allowable

variable {α}
variable [TypedObjects α]

/--
The action of allowable permutations on tangles commutes with the `typed_near_litter` function mapping
near-litters to typed near-litters. This is quite clear to see when representing tangles as codes,
but since at this stage tangles are just a type, we have to state this condition explicitly. -/
theorem smul_typedNearLitter (π : Allowable α) (N : NearLitter) :
    (π • typedNearLitter N : Tangle α) =
    typedNearLitter ((Allowable.toStructPerm π) (Quiver.Hom.toPath <| bot_lt_coe α) • N) :=
  TypedObjects.smul_typedNearLitter _ _

end Allowable

/-- The position of typed atoms and typed near-litters in the position function at any level.
This is part of the `γ = -1` fix. -/
class BasePositions where
  typedAtomPosition : Atom ↪ μ
  typedNearLitterPosition : NearLitter ↪ μ
  litter_lt :
    ∀ (L : Litter),
      ∀ a ∈ litterSet L, typedNearLitterPosition L.toNearLitter < typedAtomPosition a
  litter_le_nearLitter :
    ∀ N : NearLitter, typedNearLitterPosition N.fst.toNearLitter ≤ typedNearLitterPosition N
  symmDiff_lt_nearLitter :
    ∀ (N : NearLitter),
      ∀ a ∈ litterSet N.fst ∆ N.snd, typedAtomPosition a < typedNearLitterPosition N

export BasePositions (typedAtomPosition typedNearLitterPosition litter_lt litter_le_nearLitter
    symmDiff_lt_nearLitter)

theorem litter_lt_nearLitter [BasePositions] (N : NearLitter) (hN : N.fst.toNearLitter ≠ N) :
    typedNearLitterPosition N.fst.toNearLitter < typedNearLitterPosition N :=
  lt_of_le_of_ne (litter_le_nearLitter N) (typedNearLitterPosition.injective.ne hN)

/-- An injection from near-litters into level `α` tangles.
These will be explicitly constructed as "typed near-litters", which are codes of the form
`(α, -1, N)` for `N` a near-litter.

Since we haven't assumed anything about the structure of tangles at this level, we can't construct
these typed near-litters explicitly, so we rely on this function instead. In the blueprint, this is
function `j`. -/
add_decl_doc TypedObjects.typedNearLitter

/-- For any atom `a`, we can construct an `α`-tangle that has a `-1`-extension that contains exactly
this atom. This is called a typed singleton. In the blueprint, this is the function `k`. -/
add_decl_doc TypedObjects.typedAtom

/-- An injection from level `α` tangles into the type `μ`.
Since `μ` has a well-ordering, this induces a well-ordering on `α`-tangles: to compare two tangles,
simply compare their images under this map.

Conditions satisfied by this injection are given in `litter_lt`, `litter_lt_near_litter`,
`symm_diff_lt_near_litter`, and `support_le`. In the blueprint, this is function `ι`. -/
add_decl_doc PositionFunction.position

/-- Each typed litter `L` precedes the typed singletons of all of its elements `a ∈ L`. -/
add_decl_doc BasePositions.litter_lt

/-- Each near litter `N` which is not a litter comes later than its associated liter `L = N°`. -/
add_decl_doc litter_lt_nearLitter

/-- Each near litter `N` comes after all elements in the symmetric difference `N ∆ N°` (which is
a small set by construction). Note that if `N` is a litter, this condition is vacuously true. -/
add_decl_doc symmDiff_lt_nearLitter

end DefinePositionedTypedObjects

section Instances

variable {α : Λ} (β : Iio α) [TangleData (iioCoe β)]

instance coreVal : TangleData β.val :=
  ‹TangleData β›

instance coreCoeCoe : TangleData (β : Λ) :=
  ‹TangleData β›

section PositionFunction

variable [PositionFunction (iioCoe β)]

instance positionedVal : PositionFunction β.val :=
  ‹PositionFunction _›

instance positionedCoeCoe : PositionFunction (β : Λ) :=
  ‹PositionFunction _›

end PositionFunction

variable [TypedObjects β]

instance almostVal : TypedObjects β.val :=
  ‹TypedObjects β›

end Instances

/-- The tangle data at level `⊥` is constructed by taking the tangles to be the atoms, the allowable
permutations to be near-litter-permutations, and the designated supports to be singletons. -/
noncomputable instance Bot.corePositionedTypedObjects : TangleData ⊥
    where
  Tangle := Atom
  Allowable := NearLitterPerm
  allowableToStructPerm := StructPerm.toBotIso.toMonoidHom
  allowableAction := inferInstance
  designatedSupport a :=
    { carrier := {(Sum.inl a, Quiver.Path.nil)}
      supports := fun π => by
        simp only [mem_singleton_iff, forall_eq]
        intro h
        change (Sum.inl _, _) = (_, _) at h
        simp only [MulEquiv.coe_toMonoidHom, Prod.mk.injEq, Sum.inl.injEq, and_true] at h
        exact h
      small := small_singleton _ }

/-- The tangle data at the bottom level. -/
noncomputable instance Bot.positionedPositionedTypedObjects : PositionFunction ⊥ :=
  ⟨Nonempty.some mk_atom.le⟩

def _root_.NearLitterPerm.ofBot : Allowable ⊥ ≃ NearLitterPerm :=
  Equiv.refl _

@[simp]
theorem _root_.NearLitterPerm.ofBot_smul {X : Type _} [MulAction NearLitterPerm X]
    (π : Allowable ⊥) (x : X) :
    NearLitterPerm.ofBot π • x = π • x :=
  rfl

variable (α : Λ)

/-- The core tangle data below phase `α`. -/
class TangleDataIio (α : Λ) where
  data : ∀ β : Iio α, TangleData β

section TangleDataIio

variable [TangleDataIio α]

noncomputable instance TangleDataIio.toTangleData : ∀ β : IioBot α, TangleData β
  | ⟨⊥, _⟩ => Bot.corePositionedTypedObjects
  | ⟨(β : Λ), hβ⟩ => TangleDataIio.data ⟨β, coe_lt_coe.1 hβ⟩

noncomputable instance TangleDataIio.toTangleData' (β : Iio α) : TangleData β :=
  show TangleData (iioCoe β) by infer_instance

noncomputable instance TangleDataIio.toTangleData'' (β : TypeIndex) (hβ : β < α) :
    TangleData (show IioBot α from ⟨β, hβ⟩) :=
  TangleDataIio.toTangleData α ⟨β, hβ⟩

noncomputable instance TangleDataIio.toTangleData''' (β : Λ) (hβ : (β : TypeIndex) < α) :
    TangleData (show IioBot α from ⟨β, hβ⟩) :=
  TangleDataIio.toTangleData α ⟨β, hβ⟩

end TangleDataIio

/-- The positioned tangle data below phase `α`. -/
class PositionFunctionIio (α : Λ) [TangleDataIio α] where
  data : ∀ β : Iio α, PositionFunction β

section PositionFunctionIio

variable [TangleDataIio α] [PositionFunctionIio α]

noncomputable instance PositionFunctionIio.toPositionFunction :
    ∀ β : IioBot α, PositionFunction β
  | ⟨⊥, _⟩ => Bot.positionedPositionedTypedObjects
  | ⟨(β : Λ), hβ⟩ => PositionFunctionIio.data ⟨β, coe_lt_coe.1 hβ⟩

noncomputable instance PositionFunctionIio.toPositionFunction' (β : Iio α) :
    PositionFunction β :=
  show PositionFunction (iioCoe β) by infer_instance

end PositionFunctionIio

/-- The almost tangle data below phase `α`. -/
abbrev TypedObjectsIio (α : Λ) [TangleDataIio α] :=
  ∀ β : Iio α, TypedObjects β

end ConNF
