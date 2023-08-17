import Mathbin.Combinatorics.Quiver.Path
import Project.Phase0.Params

#align_import phase0.index

open Cardinal Function Quiver Quiver.Path Set WithBot

open scoped Cardinal

universe u

namespace ConNf

variable [Params.{u}]

section IioIic

variable {α β : Λ}

abbrev iioIndex (α : Λ) :=
  Iio (α : TypeIndex)

abbrev iicIndex (α : Λ) :=
  Iic (α : TypeIndex)

instance coeIioIic : CoeTC (Iio α) (Iic α) :=
  ⟨fun β => ⟨β.1, le_of_lt β.2⟩⟩

instance coeIio : CoeTC (Iio α) (iioIndex α) :=
  ⟨fun β => ⟨β.1, coe_lt_coe.2 β.2⟩⟩

instance coeIic : CoeTC (Iic α) (iicIndex α) :=
  ⟨fun β => ⟨β.1, coe_le_coe.2 β.2⟩⟩

abbrev iioCoe : Iio α → iioIndex α :=
  coe

abbrev iicCoe : Iic α → iicIndex α :=
  coe

@[simp]
theorem Iio.coe_mk (β : Λ) (hβ : β < α) : ((⟨β, hβ⟩ : Iio α) : iioIndex α) = ⟨β, coe_lt_coe.2 hβ⟩ :=
  rfl

@[simp]
theorem Iic.coe_mk (β : Λ) (hβ : β ≤ α) : ((⟨β, hβ⟩ : Iic α) : iicIndex α) = ⟨β, coe_le_coe.2 hβ⟩ :=
  rfl

theorem Iio.coe_injective : Injective (coe : Iio α → iioIndex α) :=
  by
  rintro ⟨β, hβ⟩ ⟨γ, hγ⟩ h
  simp only [Iio.coe_mk, Subtype.mk_eq_mk] at h 
  have := WithBot.coe_injective h
  subst this

theorem Iic.coe_injective : Injective (coe : Iic α → iicIndex α) :=
  by
  rintro ⟨β, hβ⟩ ⟨γ, hγ⟩ h
  simp only [Iic.coe_mk, Subtype.mk_eq_mk] at h 
  have := WithBot.coe_injective h
  subst this

@[simp]
theorem Iio.coe_inj {β γ : Iio α} : iioCoe β = γ ↔ β = γ :=
  Iio.coe_injective.eq_iff

@[simp]
theorem Iic.coe_inj {β γ : Iic α} : iicCoe β = γ ↔ β = γ :=
  Iic.coe_injective.eq_iff

section IioIndex

variable {hβ : (β : TypeIndex) ∈ iioIndex α}

instance : Bot (iioIndex α) :=
  ⟨⟨⊥, bot_lt_coe _⟩⟩

instance : Inhabited (iioIndex α) :=
  ⟨⊥⟩

@[simp]
theorem iioIndex.bot_ne_mk_coe : (⊥ : iioIndex α) ≠ ⟨β, hβ⟩ :=
  ne_of_apply_ne Subtype.val bot_ne_coe

@[simp]
theorem iioIndex.mk_coe_ne_bot : (⟨β, hβ⟩ : iioIndex α) ≠ ⊥ :=
  ne_of_apply_ne Subtype.val coe_ne_bot

@[simp]
theorem iioIndex.bot_ne_coe {β : Iio α} : ⊥ ≠ (β : iioIndex α) :=
  ne_of_apply_ne Subtype.val bot_ne_coe

@[simp]
theorem iioIndex.coe_ne_bot {β : Iio α} : (β : iioIndex α) ≠ ⊥ :=
  ne_of_apply_ne Subtype.val coe_ne_bot

end IioIndex

section IicIndex

variable {hβ : (β : TypeIndex) ∈ iicIndex α}

instance : Bot (iicIndex α) :=
  ⟨⟨⊥, bot_le⟩⟩

instance : Inhabited (iicIndex α) :=
  ⟨⊥⟩

@[simp]
theorem iicIndex.bot_ne_mk_coe : (⊥ : iicIndex α) ≠ ⟨β, hβ⟩ :=
  ne_of_apply_ne Subtype.val bot_ne_coe

@[simp]
theorem iicIndex.mk_coe_ne_bot : (⟨β, hβ⟩ : iicIndex α) ≠ ⊥ :=
  ne_of_apply_ne Subtype.val coe_ne_bot

end IicIndex

end IioIic

/-!
We now intend to deal with the familiar tools from phase 1 along paths `A` from `α ⟶ β` down the
TTT type hierarchy, instead of linearly level-by-level. We will construct three main definitions:

* `le_index`: A type index `β`, together with a path down from `α` to level `β`.
* `lt_index`: A type index `β`, together with a path down from `α`, to some level `γ`, and then
    directly to level `β`. This enforces that the path obtained from composing `A` with this new
    `γ ⟶ β` morphism is nontrivial by construction.
* `proper_lt_index`: Like `lt_index` but the type index `β` is proper; that is, it lies in `Λ`.

Each of these types is progressively more stringent, and they have natural coercions upwards (i.e.
from `proper_lt_index` to `lt_index` to `le_index`, and the transitive coercion from
`proper_lt_index` to `le_index`). They also have coercions to their index types (`type_index` in the
first two cases, and `Λ` in the third).

We will then proceed to define new API for many phase 1 constructions (tangles, f-maps, ...)
that use these three types instead of `Λ`, `type_index`, and `Iio α`. All of the properties that
were proven in phase 1 of course still hold for the functions under these new names - their
functionality has not changed.

These constructions are helpful for stating and proving the freedom-of-action theorem, since it
allows for the possibility that the type of `β`-tangles (for instance) depends on the path downwards
from `α` to `β`. In our actual construction, this does hold, since phase 1 is conducted entirely
linearly, but this feature is not actually needed for defining and proving statements in most of
phase 2, so we use this alternate formalisation.
-/


section Improper

variable {α : TypeIndex}

/-- We define the type of paths from certain types to lower types as elements of this quiver. -/
instance quiver : Quiver TypeIndex :=
  ⟨(· > ·)⟩

/-- A (finite) path from the type α to the base type.
This can be seen as a way that we can perceive extensionality, iteratively descending to lower
types in the hierarchy until we reach the base type.
This plays the role of an extended type index in the paper. -/
def ExtendedIndex (α : TypeIndex) :=
  Quiver.Path α ⊥

/-- If there is a path between `α` and `β`, we must have `β ≤ α`.
The case `β = α` can occur with the nil path. -/
theorem le_of_path : ∀ {β : TypeIndex}, Path α β → β ≤ α
  | β, nil => le_rfl
  | β, cons p f => (le_of_lt f).trans <| le_of_path p

theorem path_eq_nil : ∀ p : Path α α, p = nil
  | nil => rfl
  | cons p f => ((le_of_path p).not_lt f).elim

/-! The next few results won't be needed in the same way in Lean 4. -/


def Path.iicRec' {α : Λ} {β : iicIndex α}
    (motive : ∀ γ : TypeIndex, Path (β : TypeIndex) γ → Sort _) :
    motive β nil →
      (∀ (γ δ : TypeIndex) (hγ : γ ≤ α) (hδ : δ ≤ α) (A : Path (β : TypeIndex) γ) (h : δ < γ),
          motive γ A → motive δ (A.cons h)) →
        ∀ (γ : iicIndex α) (A : Path (β : TypeIndex) γ),
          motive (⟨γ, (le_of_path A).trans β.Prop⟩ : iicIndex α) A :=
  fun hn hc γ =>
  Path.rec hn fun γ δ A h =>
    hc γ δ ((le_of_path A).trans β.Prop) ((le_of_path (A.cons h)).trans β.Prop) A h

def motiveEquiv {α : Λ} {β : iicIndex α}
    {motive : ∀ γ : iicIndex α, Path (β : TypeIndex) γ → Sort _} {γ : iicIndex α}
    {A : Path (β : TypeIndex) γ} : motive (⟨γ, γ.Prop⟩ : iicIndex α) A ≃ motive γ A :=
  Equiv.cast (by cases γ <;> rfl)

/-- An induction principle for paths that allows us to use `Iic_index α` instead of needing to
define the motive for all `type_index`. -/
@[elab_as_elim]
def Path.iicRec {α : Λ} {β : iicIndex α}
    {motive : ∀ γ : iicIndex α, Path (β : TypeIndex) γ → Sort _} :
    motive β nil →
      (∀ (γ δ : iicIndex α) (A : Path (β : TypeIndex) γ) (h : δ < γ),
          motive γ A → motive δ (A.cons h)) →
        ∀ (γ : iicIndex α) (A : Path (β : TypeIndex) γ), motive γ A :=
  fun hn hc γ A =>
  motiveEquiv
    (motiveEquiv
      (show _ from
        Path.iicRec' (fun γ A => motive ⟨γ, (le_of_path A).trans β.Prop⟩ A) (motiveEquiv.symm hn)
          (fun γ δ hγ hδ A h =>
            hc ⟨γ, (le_of_path A).trans β.Prop⟩ ⟨δ, (le_of_path (A.cons h)).trans β.Prop⟩ A h)
          γ A))

@[simp]
theorem Path.iicRec_nil {α : Λ} {β : iicIndex α}
    {motive : ∀ γ : iicIndex α, Path (β : TypeIndex) γ → Sort _} {hn : motive β nil} {hc} :
    @Path.iicRec _ _ _ motive hn hc β nil = hn :=
  by
  rw [path.Iic_rec, path.Iic_rec']
  simp only [Subtype.coe_mk, motive_equiv, Equiv.cast_symm, Equiv.cast_apply, cast_cast, cast_eq]

@[simp]
theorem Path.iicRec_cons {α : Λ} {β : iicIndex α}
    {motive : ∀ γ : iicIndex α, Path (β : TypeIndex) γ → Sort _} {hn : motive β nil} {hc}
    (γ δ : iicIndex α) (A : Path (β : TypeIndex) γ) (h : δ < γ) :
    @Path.iicRec _ _ _ motive hn hc δ (A.cons h) = hc γ δ A h (Path.iicRec hn hc γ A) :=
  by
  rw [path.Iic_rec, path.Iic_rec']
  dsimp only [Subtype.coe_mk, motive_equiv]
  simp only [Equiv.cast_refl, Equiv.cast_symm, Equiv.cast_apply, Equiv.coe_refl, id.def]
  rw [cast_eq_iff_heq]
  congr
  rw [Subtype.coe_eta]
  rw [Subtype.coe_eta]
  exact (cast_hEq _ _).symm

/-- There are at most `Λ` `α`-extended type indices. -/
@[simp]
theorem mk_extendedIndex (α : TypeIndex) : (#ExtendedIndex α) ≤ (#Λ) :=
  by
  refine' le_trans ((Cardinal.le_def _ _).2 ⟨⟨to_list, to_list_injective (α : type_index) ⊥⟩⟩) _
  convert mk_list_le_max _ using 1; simp only [mk_type_index, max_eq_right, aleph_0_le_mk]

/-- If `β < γ`, we have a path directly between the two types in the opposite order.
Note that the `⟶` symbol (long right arrow) is not the normal `→` (right arrow),
even though monospace fonts often display them similarly. -/
instance ltToHom (β γ : Λ) : HasLiftT (β < γ) ((γ : TypeIndex) ⟶ β) :=
  ⟨coe_lt_coe.2⟩

/-- The direct path from the base type to `α`. -/
def TypeIndex.extend : ∀ α : TypeIndex, ExtendedIndex α
  | ⊥ => nil
  | (α : Λ) => Hom.toPath <| WithBot.bot_lt_coe α

instance (α : TypeIndex) : Inhabited (ExtendedIndex α) :=
  ⟨α.extend⟩

/-- There exists an `α`-extended type index. --/
theorem mk_extendedIndex_ne_zero (α : TypeIndex) : (#ExtendedIndex α) ≠ 0 :=
  Cardinal.mk_ne_zero _

/-- A type index `β`, together with a path down from `α` to level `β`. Hence, `β ≤ α`.
This type is intended to be used in place of `β : type_index, β ≤ α` in phase 2. -/
@[ext, protect_proj]
structure LeIndex (α : TypeIndex) where
  index : TypeIndex
  Path : Path α index

namespace LeIndex

instance : Inhabited (LeIndex α) :=
  ⟨⟨⊥, α.extend⟩⟩

/-- By forgetting the path that we took from `α` to the lower index `β`, we can recover the type
index `β` that this `le_index` wraps. -/
instance hasCoeTypeIndex : Coe (LeIndex α) TypeIndex :=
  ⟨LeIndex.index⟩

@[simp]
theorem coe_mk (index : TypeIndex) (path : Path (α : TypeIndex) index) :
    ((⟨index, Path⟩ : LeIndex α) : TypeIndex) = index :=
  rfl

/-- Add an index to a `le_index`. -/
def cons (A : LeIndex α) {γ : TypeIndex} (hγ : γ < A.index) : LeIndex α :=
  ⟨γ, A.Path.cons hγ⟩

end LeIndex

/-- A type index `β`, together with a path `A` down from `α` to level `γ` and then to level `β`.
This enforces that the path obtained from composing `A` with this new `γ ⟶ β` morphism is
nontrivial by construction. This type is intended to be used in place of `β : type_index, β < α`
and `β : Iio_index α` in phase 2. -/
@[ext]
structure LtIndex (α : TypeIndex) where
  index : TypeIndex
  higher : TypeIndex
  index_lt_higher : index < higher
  path' : Path α higher

namespace LtIndex

/-- A constructor for `lt_index` with less explicit arguments. -/
def mk' {index higher : TypeIndex} (index_lt : index < higher)
    (path' : Path (α : TypeIndex) higher) : LtIndex α :=
  ⟨index, higher, index_lt, path'⟩

instance {α : Λ} : Inhabited (LtIndex α) :=
  ⟨mk' (bot_lt_coe _) Path.nil⟩

/-- A path compatible with the one from `le_index`, formed by composing the inner `path'` field
with the morphism `higher ⟶ index`. By construction, this path is always nontrivial. -/
def path (A : LtIndex α) : Path (α : TypeIndex) A.index :=
  A.path'.cons A.index_lt_higher

/-- An `lt_index` is not equal to its source `α`. This is the lemma that justifies the name
`lt_index` as compared to `le_index`, which permits the trivial path `α ⟶ α`. -/
theorem index_lt (A : LtIndex α) : A.index < α :=
  A.index_lt_higher.trans_le <| le_of_path A.path'

/-- The natural coercion from `lt_index` to `le_index`. An analogous concept to `le_of_lt`. -/
def toLeIndex (A : LtIndex α) : LeIndex α :=
  ⟨A.index, A.Path⟩

instance hasCoeLeIndex : Coe (LtIndex α) (LeIndex α) :=
  ⟨toLeIndex⟩

/-- By forgetting the path that we took from `α` to the lower index `β`, we can recover the type
index `β` that this `lt_index` wraps. -/
instance hasCoeTypeIndex : Coe (LtIndex α) TypeIndex :=
  ⟨index⟩

end LtIndex

end Improper

/-- A proper type index `β`, together with a path `A` down from `α` to level `γ` and then to level
`β`. This enforces that the path obtained from composing `A` with this new `γ ⟶ β` morphism is
nontrivial by construction. This type is intended to be used in phase of `β : Λ, β < α` and
`β : Iio α` in phase 2. -/
@[ext, nolint has_nonempty_instance]
structure ProperLtIndex (α : Λ) where
  (index higher : Λ)
  index_lt_higher : index < higher
  path' : Path (α : TypeIndex) higher

namespace ProperLtIndex

variable {α : Λ}

/-- A constructor for `proper_lt_index` with less explicit arguments. -/
def mk' {α index higher : Λ} (index_lt : index < higher) (path' : Path (α : TypeIndex) higher) :
    ProperLtIndex α :=
  ⟨index, higher, index_lt, path'⟩

/-- A path compatible with the one from `le_index`, formed by composing the inner `path'` field
with the morphism `higher ⟶ index`. By construction, this path is always nontrivial. -/
def path (A : ProperLtIndex α) : Path (α : TypeIndex) A.index :=
  A.path'.cons <| coe_lt_coe.2 A.index_lt_higher

/-- A `proper_lt_index` is not equal to its source `α`. See also `lt_index.ne`. -/
theorem index_lt (A : ProperLtIndex α) : A.index < α :=
  A.index_lt_higher.trans_le <| coe_le_coe.1 <| le_of_path A.path'

/-- The natural coercion from `proper_lt_index` to `le_index`.
An analogous concept to `le_of_lt`, also converting `index: Λ` into a `type_index`. -/
def toLeIndex (A : ProperLtIndex α) : LeIndex α :=
  ⟨A.index, A.Path⟩

/-- The natural coercion from `proper_lt_index` to `to_lt_index`, by converting `index : Λ` into a
`type_index`. -/
def toLtIndex (A : ProperLtIndex α) : LtIndex α :=
  ⟨A.index, A.higher, coe_lt_coe.2 A.index_lt_higher, A.path'⟩

instance hasCoeLtIndex : Coe (ProperLtIndex α) (LtIndex α) :=
  ⟨toLtIndex⟩

/-- By forgetting the path that we took from `α` to the lower index `β`, we can recover the proper
type index `β` that this `proper_lt_index` wraps. -/
instance hasCoeΛ : Coe (ProperLtIndex α) Λ :=
  ⟨index⟩

end ProperLtIndex

end ConNf

