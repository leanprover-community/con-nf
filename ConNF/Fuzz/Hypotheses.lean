import ConNF.Structural.Support
import ConNF.Fuzz.Position

/-!
# Hypotheses for constructing the `fuzz` map

This file contains the inductive hypotheses required for constructing the `fuzz` map.
Even though not everything defined here is strictly necessary for this construction, we bundle
it here for more convenient use later.

## Main declarations

* `ConNF.ModelData`: Data about the model elements at level `α`, called *t-sets*.
* `ConNF.Tangle`: A t-set together with a support for it.
* `ConNF.PositionedTangles`: A function that gives each type `α` tangle a unique position `ν : μ`.
* `ConNF.TypedObjects`: Allows us to encode near-litters as type `α` t-sets.
* `ConNF.BasePositions`: Almost arbitrarily chosen position functions for atoms and near-litters.
* `ConNF.PositionedObjects`: Hypotheses on the positions of typed objects.
-/

open Function Set WithBot

open scoped Pointwise symmDiff

universe u

namespace ConNF

variable [Params.{u}]

/-- Data about the model elements at level `α`. This class asserts the existence of a type of model
elements at level `α` called *t-sets*, and a group of *allowable permutations* at level `α` that act
on the type `α` t-sets. We also stipulate that each t-set has a support. There is a natural
embedding of t-sets into structural sets. -/
class ModelData (α : TypeIndex) where
  /-- The type of model elements that we assume were constructed at stage `α`.
  Later in the recursion, we will construct this type explicitly, but for now, we will just assume
  that it exists. -/
  (TSet : Type u)
  /-- The type of allowable permutations that we assume exists on `α`-tangles. -/
  (Allowable : Type u)
  [allowableGroup : Group Allowable]
  /-- An embedding from allowable permutations to structural permutations. -/
  allowableToStructPerm : Allowable →* StructPerm α
  allowableToStructPerm_injective : Function.Injective allowableToStructPerm
  [allowableAction : MulAction Allowable TSet]
  has_support (t : TSet) : ∃ S : Support α,
    letI : MulAction Allowable (Address α) :=
      MulAction.compHom _ allowableToStructPerm
    MulAction.Supports Allowable (S : Set (Address α)) t
  /-- The embedding that converts a t-sets into its underlying structural set. -/
  toStructSet : TSet ↪ StructSet α
  toStructSet_smul (ρ : Allowable) (t : TSet) :
    letI : MulAction Allowable (StructSet α) :=
      MulAction.compHom _ allowableToStructPerm
    toStructSet (ρ • t) = ρ • toStructSet t

export ModelData (TSet Allowable toStructSet toStructSet_smul)

attribute [instance] ModelData.allowableGroup ModelData.allowableAction

namespace Allowable

variable {α : TypeIndex} [ModelData α] {X : Type _} [MulAction (StructPerm α) X]

/-- Allowable permutations can be considered a subtype of structural permutations.
This map can be thought of as an inclusion that preserves the group structure. -/
def toStructPerm : Allowable α →* StructPerm α :=
  ModelData.allowableToStructPerm

theorem toStructPerm_injective (α : TypeIndex) [ModelData α] :
    Function.Injective (toStructPerm : Allowable α → StructPerm α) :=
  ModelData.allowableToStructPerm_injective

/-- Allowable permutations act on anything that structural permutations do. -/
instance : MulAction (Allowable α) X :=
  MulAction.compHom _ toStructPerm

theorem toStructPerm_smul (ρ : Allowable α) (x : X) : ρ • x = Allowable.toStructPerm ρ • x :=
  rfl

@[simp]
theorem smul_support_max (ρ : Allowable α) (S : Support α) :
    (ρ • S).max = S.max :=
  rfl

@[simp]
theorem smul_support_f (ρ : Allowable α) (S : Support α) (i : κ) (hi : i < S.max) :
    (ρ • S).f i hi = ρ • S.f i hi :=
  rfl

@[simp]
theorem smul_support_coe (ρ : Allowable α) (S : Support α) :
    (ρ • S : Support α) = ρ • (S : Set (Address α)) :=
  Enumeration.smul_coe _ _

theorem smul_mem_smul_support {S : Support α} {c : Address α}
    (h : c ∈ S) (ρ : Allowable α) : ρ • c ∈ ρ • S :=
  Enumeration.smul_mem_smul h _

theorem smul_eq_of_smul_support_eq {S : Support α} {ρ : Allowable α}
    (hS : ρ • S = S) {c : Address α} (hc : c ∈ S) : ρ • c = c :=
  Enumeration.smul_eq_of_smul_eq hS hc

variable {ρ ρ' : Allowable α} {c : Address α}

/-- Although we use often this in `simp` invocations, it is not given the `@[simp]` attribute so
that it doesn't get used unnecessarily. -/
theorem smul_address :
    ρ • c = ⟨c.path, Allowable.toStructPerm ρ c.path • c.value⟩ :=
  rfl

@[simp]
theorem smul_address_eq_iff :
    ρ • c = c ↔ Allowable.toStructPerm ρ c.path • c.value = c.value :=
  StructPerm.smul_address_eq_iff

@[simp]
theorem smul_address_eq_smul_iff :
    ρ • c = ρ' • c ↔
    Allowable.toStructPerm ρ c.path • c.value = Allowable.toStructPerm ρ' c.path • c.value :=
  StructPerm.smul_address_eq_smul_iff

end Allowable

theorem ModelData.TSet.has_support {α : TypeIndex} [ModelData α] (t : TSet α) :
    ∃ S : Support α, MulAction.Supports (Allowable α) (S : Set (Address α)) t :=
  ModelData.has_support t

/-- The canonical support for an atom. -/
def Atom.support (a : Atom) : Support ⊥ :=
  Enumeration.singleton ⟨Quiver.Path.nil, Sum.inl a⟩

@[simp]
theorem Atom.support_carrier (a : Atom) :
    Enumeration.carrier a.support = {⟨Quiver.Path.nil, Sum.inl a⟩} := by
  ext x : 1
  simp only [support, Enumeration.singleton_carrier, mem_singleton_iff]

theorem Atom.support_supports (a : Atom) :
    MulAction.Supports BasePerm (a.support : Set (Address ⊥)) a := by
  intro ρ h
  simp only [support_carrier, mem_singleton_iff, BasePerm.smul_address_eq_iff, forall_eq,
    Sum.smul_inl, Sum.inl.injEq] at h
  exact h

/-- The model data at level `⊥` is constructed by taking the t-sets to be the atoms, and
the allowable permutations to be the near-litter permutations. -/
instance Bot.modelData : ModelData ⊥
    where
  TSet := Atom
  Allowable := BasePerm
  allowableToStructPerm := Tree.toBotIso.toMonoidHom
  allowableToStructPerm_injective := MulEquiv.injective _
  allowableAction := inferInstance
  has_support a := ⟨a.support, a.support_supports⟩
  toStructSet := StructSet.ofBot.toEmbedding
  toStructSet_smul _ _ := rfl

/-- A t-set at level `α` together with a support for it. This is a specialisation of the notion
of a tangle which will be defined for arbitrary type indices. -/
@[ext]
structure TangleCoe (α : Λ) [ModelData α] : Type u where
  set : TSet α
  support : Support α
  support_supports : MulAction.Supports (Allowable α) (support : Set (Address α)) set

/-- If `α` is a proper type index, an `α`-tangle is t-set at level `α`,
together with a support for it. If `α = ⊥`, then an `α`-tangle is an atom. -/
def Tangle : (α : TypeIndex) → [ModelData α] → Type u
  | (α : Λ), _ => TangleCoe α
  | ⊥, _ => Atom

/-- Each tangle comes with a support. Since we could (a priori) have instances for `[ModelData ⊥]`
other than that constructed above, it's possible that this isn't a support under the action of
`⊥`-allowable permutations. We will later define `Tangle.support_supports_lt` which gives the
expected result under suitable hypotheses. -/
def Tangle.support : {α : TypeIndex} → [ModelData α] → Tangle α → Support α
  | (α : Λ), _, t => TangleCoe.support t
  | ⊥, _i, a => Atom.support a

instance (α : Λ) [ModelData α] : MulAction (Allowable α) (TangleCoe α) where
  smul ρ t := ⟨ρ • t.set, ρ • t.support, by
      intro ρ' h
      rw [← inv_smul_eq_iff, smul_smul, smul_smul]
      refine t.support_supports _ ?_
      intro a ha
      rw [mul_smul, mul_smul, inv_smul_eq_iff]
      refine h ?_
      rw [Enumeration.smul_carrier, smul_mem_smul_set_iff]
      exact ha⟩
  one_smul t := by
    change ⟨1 • t.set, 1 • t.support, _⟩ = t
    ext : 1 <;> simp only [one_smul]
  mul_smul ρ₁ ρ₂ t := by
    change ⟨_ • t.set, _ • t.support, _⟩ = (⟨_ • _ • t.set, _ • _ • t.support, _⟩ : Tangle α)
    ext : 1 <;> simp only [mul_smul]

/-- Allowable permutations act on tangles. -/
instance : (α : TypeIndex) → [ModelData α] → MulAction (Allowable α) (Tangle α)
  | (α : Λ), _ => inferInstanceAs (MulAction (Allowable α) (TangleCoe α))
  | ⊥, _ => inferInstanceAs (MulAction (Allowable ⊥) Atom)

/-- Provides a position function for `α`-tangles, giving each tangle a unique position `ν : μ`.
The existence of this injection proves that there are at most `μ` tangles at level `α`, and
therefore at most `μ` t-sets. Since `μ` has a well-ordering, this induces a well-ordering on
`α`-tangles: to compare two tangles, simply compare their images under this map. -/
class PositionedTangles (α : TypeIndex) [ModelData α] where
  pos : Tangle α ↪ μ

instance {α : TypeIndex} [ModelData α] [PositionedTangles α] : Position (Tangle α) μ where
  pos := PositionedTangles.pos

variable (α : Λ) [ModelData α]

/-- Allows us to encode near-litters as `α`-tangles. These maps are expected to cohere
with the conditions given in `BasePositions`, but this requirement is expressed later. -/
class TypedObjects where
  /-- Encode a near-litter as an `α`-tangle. The resulting model element has a `⊥`-extension which
  contains only this near-litter. -/
  typedNearLitter : NearLitter ↪ TSet α
  smul_typedNearLitter :
    ∀ (ρ : Allowable α) (N : NearLitter),
    ρ • typedNearLitter N =
    typedNearLitter ((Allowable.toStructPerm ρ) (Quiver.Hom.toPath <| bot_lt_coe α) • N)

export TypedObjects (typedNearLitter)

/-- Almost arbitrarily chosen position functions for atoms and near-litters. The only requirements
they satisfy are included in this class. These requirements are later used to prove that the
`Constrains` relation is well-founded. -/
class BasePositions where
  posAtom : Atom ↪ μ
  posNearLitter : NearLitter ↪ μ
  lt_pos_atom (a : Atom) :
    posNearLitter a.1.toNearLitter < posAtom a
  lt_pos_litter (N : NearLitter) (hN : ¬N.IsLitter) :
    posNearLitter N.1.toNearLitter < posNearLitter N
  lt_pos_symmDiff (a : Atom) (N : NearLitter) (h : a ∈ litterSet N.1 ∆ N) :
    posAtom a < posNearLitter N

/-- A position function for atoms. -/
instance [BasePositions] : Position Atom μ :=
  ⟨BasePositions.posAtom⟩

/-- A position function for near-litters. -/
instance [BasePositions] : Position NearLitter μ :=
  ⟨BasePositions.posNearLitter⟩

theorem lt_pos_atom [BasePositions] (a : Atom) : pos a.1.toNearLitter < pos a :=
  BasePositions.lt_pos_atom a

theorem lt_pos_litter [BasePositions] (N : NearLitter) (hN : ¬N.IsLitter) :
    pos N.1.toNearLitter < pos N :=
  BasePositions.lt_pos_litter N hN

theorem lt_pos_symmDiff [BasePositions] (a : Atom) (N : NearLitter) (h : a ∈ litterSet N.1 ∆ N) :
    pos a < pos N :=
  BasePositions.lt_pos_symmDiff a N h

/-- The assertion that the position of typed near-litters is at least the position of the
near-litter itself. This is used to prove that the alternative extension relation `↝` is
well-founded. -/
class PositionedObjects [BasePositions] [PositionedTangles α] [TypedObjects α] : Prop where
  pos_typedNearLitter (N : NearLitter) (t : Tangle α) :
    t.set = typedNearLitter N → pos N ≤ pos t

export PositionedObjects (pos_typedNearLitter)

namespace Allowable

variable {α}
variable [TypedObjects α]

/-- The action of allowable permutations on tangles commutes with the `typedNearLitter` function
mapping near-litters to typed near-litters. This can be seen by representing tangles as codes. -/
theorem smul_typedNearLitter (ρ : Allowable α) (N : NearLitter) :
    (ρ • typedNearLitter N : TSet α) =
    typedNearLitter ((Allowable.toStructPerm ρ) (Quiver.Hom.toPath <| bot_lt_coe α) • N) :=
  TypedObjects.smul_typedNearLitter _ _

end Allowable

/-- The position function at level `⊥`, taken from the `BasePositions`. -/
instance Bot.positionedTangles [BasePositions] : PositionedTangles ⊥ :=
  ⟨BasePositions.posAtom⟩

/-- The identity equivalence between `⊥`-allowable permutations and near-litter permutations.
This equivalence is a group isomorphism. -/
def _root_.BasePerm.ofBot : Allowable ⊥ ≃ BasePerm :=
  Equiv.refl _

@[simp]
theorem _root_.BasePerm.ofBot_smul {X : Type _} [MulAction BasePerm X]
    (π : Allowable ⊥) (x : X) :
    BasePerm.ofBot π • x = π • x :=
  rfl

end ConNF
