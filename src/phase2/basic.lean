import phase1.tangle

open function set with_bot quiver
open_locale pointwise

noncomputable theory

universe u

namespace con_nf
variables [params.{u}] (α : Λ)

-- these instances will mess up defining phase 2 assumptions, so don't keep them in scope
-- [core_tangle_data α] [positioned_tangle_data α] [almost_tangle_data α] [tangle_data α]

/- namespace nonempty_semitangle

def to_pretangle (t : nonempty_semitangle α) : pretangle α :=
pretangle.mk t.pref.atoms (λ β hβ, pretangle_inj β hβ ''
  (t.exts β hβ : set (tangle α β $ coe_lt_coe.mpr hβ)))

lemma to_pretangle_ne_empty (t : nonempty_semitangle α) :
  to_pretangle α t ≠ pretangle.mk ∅ (λ β hβ, ∅) :=
begin
  by_cases hzero : ∃ β, β < α,
  { obtain ⟨β, hβ⟩ := hzero,
    intro h,
    have := congr_arg pretangle.extension h,
    rw pretangle.extension_mk at this,
    have := congr_fun₂ this β hβ,
    rw [to_pretangle, pretangle.extension_mk, set.image_eq_empty] at this,
    exact (t.exts β hβ).property.ne_empty this },
  { intro h,
    have := congr_arg pretangle.atom_extension h,
    rw [to_pretangle, pretangle.atom_extension_mk, pretangle.atom_extension_mk] at this,
    obtain ⟨ts, ⟨atoms, rep, hA⟩ | ⟨β, hβ, rep, hA⟩⟩ := t,
    { exact atoms.2.ne_empty this },
    { exfalso, exact hzero ⟨β, hβ⟩ } }
end

lemma to_pretangle_injective : injective (to_pretangle α) :=
begin
  intros s t hst, unfold to_pretangle at hst,
  by_cases h : is_min α,
  { have := congr_arg pretangle.atom_extension hst,
    rw [pretangle.atom_extension_mk, pretangle.atom_extension_mk] at this,
    exact ext_zero _ _ h this },
  { obtain ⟨β, hβ⟩ := not_is_min_iff.1 h,
    have := congr_arg pretangle.extension hst,
    rw [pretangle.extension_mk, pretangle.extension_mk] at this,
    have := congr_fun₂ this β hβ,
    rw set.image_eq_image (embedding.injective _) at this,
    exact ext _ _ _ (subtype.coe_inj.mp this) }
end

end nonempty_semitangle

namespace semitangle

def to_pretangle : semitangle α → pretangle α
| ⊥ := pretangle.mk ∅ (λ β hβ, ∅)
| (t : nonempty_semitangle α) := nonempty_semitangle.to_pretangle α t

lemma to_pretangle_injective : injective (to_pretangle α) :=
begin
  intros s t hst,
  induction s using with_bot.rec_bot_coe; induction t using with_bot.rec_bot_coe,
  { refl },
  { exfalso, rw [to_pretangle, to_pretangle] at hst,
    exact nonempty_semitangle.to_pretangle_ne_empty _ _ hst.symm },
  { exfalso, rw [to_pretangle, to_pretangle] at hst,
    exact nonempty_semitangle.to_pretangle_ne_empty _ _ hst },
  { rw nonempty_semitangle.to_pretangle_injective α hst }
end

end semitangle

namespace new_tangle

def to_pretangle (t : new_tangle α) : pretangle α := semitangle.to_pretangle α t

lemma to_pretangle_injective : injective (to_pretangle α) :=
λ s t hst, subtype.coe_inj.mp (semitangle.to_pretangle_injective α hst)

end new_tangle -/

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

/-- A type index `β`, together with a path down from `α` to level `β`. Hence, `β ≤ α`.
This type is intended to be used in place of `β : type_index, β ≤ α` in phase 2. -/
structure le_index (α : Λ) :=
(index : type_index)
(path : path (α : type_index) index)

/-- By forgetting the path that we took from `α` to the lower index `β`, we can recover the type
index `β` that this `le_index` wraps. -/
instance le_index.has_coe {α : Λ} : has_coe (le_index α) type_index := ⟨le_index.index⟩

def le_index.cons {α : Λ} (A : le_index α) {γ : type_index} (hγ : γ < A.index) : le_index α :=
⟨γ, path.cons A.path hγ⟩

/-- A type index `β`, together with a path `A` down from `α` to level `γ` and then to level `β`.
This enforces that the path obtained from composing `A` with this new `γ ⟶ β` morphism is
nontrivial by construction. This type is intended to be used in place of `β : type_index, β < α`
and `β : Iio (α : type_index)` in phase 2. -/
structure lt_index (α : Λ) :=
(index : type_index)
(higher : type_index)
(index_lt : index < higher)
(path' : path (α : type_index) higher)

/-- A path compatible with the one from `le_index`, formed by composing the inner `path'` field
with the morphism `higher ⟶ index`. By construction, this path is always nontrivial. -/
def lt_index.path {α : Λ} (A : lt_index α) : path (α : type_index) A.index :=
path.cons A.path' A.index_lt

/-- An `lt_index` is not equal to its source `α`. This is the lemma that justifies the name
`lt_index` as compared to `le_index`, which permits the trivial path `α ⟶ α`. -/
lemma lt_index.ne {α : Λ} (A : lt_index α) : A.index ≠ α :=
λ h, not_lt_of_le (by convert le_of_path A.path') A.index_lt

/-- The natural coercion from `lt_index` to `le_index`. An analogous concept to `le_of_lt`. -/
def lt_index.to_le_index {α : Λ} (A : lt_index α) : le_index α :=
⟨A.index, A.path⟩

instance lt_index.has_coe {α : Λ} : has_coe (lt_index α) (le_index α) :=
⟨lt_index.to_le_index⟩

/-- By forgetting the path that we took from `α` to the lower index `β`, we can recover the type
index `β` that this `lt_index` wraps. -/
instance lt_index.has_coe_to_type_index {α : Λ} : has_coe (lt_index α) type_index :=
⟨lt_index.index⟩

/-- A proper type index `β`, together with a path `A` down from `α` to level `γ` and then to level
`β`. This enforces that the path obtained from composing `A` with this new `γ ⟶ β` morphism is
nontrivial by construction. This type is intended to be used in phase of `β : Λ, β < α` and
`β : Iio α` in phase 2. -/
structure proper_lt_index (α : Λ) :=
(index : Λ)
(higher : Λ)
(index_lt : index < higher)
(path' : path (α : type_index) higher)

def proper_lt_index.mk' {α index higher : Λ}
  (index_lt : index < higher) (path' : path (α : type_index) higher) : proper_lt_index α :=
⟨index, higher, index_lt, path'⟩

/-- A path compatible with the one from `le_index`, formed by composing the inner `path'` field
with the morphism `higher ⟶ index`. By construction, this path is always nontrivial. -/
def proper_lt_index.path {α : Λ} (A : proper_lt_index α) : path (α : type_index) A.index :=
path.cons A.path' $ coe_lt_coe.mpr A.index_lt

/-- An `proper_lt_index` is not equal to its source `α`. See also `lt_index.ne`. -/
lemma proper_lt_index.ne {α : Λ} (A : proper_lt_index α) : A.index ≠ α :=
λ h, not_lt_of_le (by convert coe_le_coe.mp (le_of_path A.path')) A.index_lt

/-- The natural coercion from `proper_lt_index` to `le_index`.
An analogous concept to `le_of_lt`, also converting `index: Λ` into a `type_index`. -/
def proper_lt_index.to_le_index {α : Λ} (A : proper_lt_index α) : le_index α :=
⟨A.index, A.path⟩

/-- The natural coercion from `proper_lt_index` to `to_lt_index`, by converting `index : Λ` into a
`type_index`. -/
def proper_lt_index.to_lt_index {α : Λ} (A : proper_lt_index α) : lt_index α :=
⟨A.index, A.higher, coe_lt_coe.mpr A.index_lt, A.path'⟩

instance proper_lt_index.has_coe {α : Λ} : has_coe (proper_lt_index α) (lt_index α) :=
⟨proper_lt_index.to_lt_index⟩

/-- By forgetting the path that we took from `α` to the lower index `β`, we can recover the proper
type index `β` that this `proper_lt_index` wraps. -/
instance proper_lt_index.has_coe_to_lambda {α : Λ} : has_coe (proper_lt_index α) Λ :=
⟨proper_lt_index.index⟩

/-!
We now proceed to make some assumptions that will be held throughout phase 2.
We assume:

* core tangle data at all `le_index α`;
* positioned tangle data at all `lt_index α`;
* full tangle data at all `proper_lt_index α`.

Note that:

* There is a trivial `le_index` path `α ⟶ α`, which means that we have core tangle data at `α`.
    This is precisely what we have constructed in phase 1 of the recursion.
* Positioned tangle data exists at all type indices `β < α` (which may be different depending on the
    path taken from `α` down to `β` a priori), which notably includes the base type `-1`/`⊥`.
    This allows us to talk about f-maps and other things that require the position function without
    having to construct full tangle data for the base type `-1`/`⊥`.

In order to have positioned (or full) tangle data at a given `lt_index` (or `proper_lt_index`) we
must first have constructed the previous tangle data components. By parametrising all of the
`*_tangle_data` classes with their predecessors, we can get definitional equality and avoid diamonds
almost for free. We simply provide some instances which give

* core tangle data at all `lt_index α`;
* core tangle data at all `proper_lt_index α`;
* positioned tangle data at all `proper_lt_index α`.

These instances can obviously be satisfied using the natural coercions between the index types
above, and they can be accessed easily through typeclass resolution.

The only downside (that I can see!) to this approach is that we need to define our assumptions class
in several steps so that we can write the relevant instances between writing all of our assumptions.
-/

/-- We assume core tangle data for all type indices less than (or equal to) `α`, along all paths. -/
class phase_2_core_assumptions :=
[lower_core_tangle_data : Π (A : le_index α), core_tangle_data A.index]

/-! Make the core tangle data accessible as an instance for all `le_index α`. -/
attribute [instance] phase_2_core_assumptions.lower_core_tangle_data

variable [phase_2_core_assumptions α]

/-! We now take the core tangle data that we just assumed exists, and make it accessible under
all possible different names. This allows lean's typeclass inference to easily find all the required
instances in many cases. -/

/-! Make the core tangle data accessible as an instance for all `lt_index α`. -/
instance lt_index_core_tangle_data (A : lt_index α) : core_tangle_data A.index :=
phase_2_core_assumptions.lower_core_tangle_data (A : le_index α)

/-! Make the core tangle data accessible as an instance for all `lt_index α`,
where the index is accessed through the coercion to `le_index`. -/
instance lt_index_coe_core_tangle_data (A : lt_index α) : core_tangle_data (A : le_index α).index :=
phase_2_core_assumptions.lower_core_tangle_data (A : le_index α)

/-! Make the core tangle data accessible as an instance for all `proper_lt_index α`. -/
instance proper_lt_index_core_tangle_data (A : proper_lt_index α) : core_tangle_data A.index :=
phase_2_core_assumptions.lower_core_tangle_data (A : le_index α)

/-! Make the core tangle data accessible as an instance for all `proper_lt_index α`,
where the index is accessed through the coercion to `lt_index`. -/
instance proper_lt_index_coe_core_tangle_data (A : proper_lt_index α) :
  core_tangle_data (A : lt_index α).index :=
phase_2_core_assumptions.lower_core_tangle_data (A : le_index α)

/-! Make the core tangle data accessible as an instance for all `proper_lt_index α`,
where the index is accessed through the coercion to `le_index`. -/
instance proper_lt_index_coe_coe_core_tangle_data (A : proper_lt_index α) :
  core_tangle_data (A : le_index α).index :=
phase_2_core_assumptions.lower_core_tangle_data (A : le_index α)

/-- We assume positioned tangle data for all type indices strictly less than `α`,
along all paths. -/
class phase_2_positioned_assumptions :=
[lower_positioned_tangle_data : Π (A : lt_index α), positioned_tangle_data A.index]

/-! Make the positioned tangle data accessible as an instance for all `lt_index α`. -/
attribute [instance] phase_2_positioned_assumptions.lower_positioned_tangle_data

variable [phase_2_positioned_assumptions α]

/-! We now take the positioned tangle data that we just assumed exists, and make it accessible under
all possible different names. This allows lean's typeclass inference to easily find all the required
instances in many cases. -/

/-! Make the positioned tangle data accessible as an instance for all `lt_index α`. -/
instance lt_index_positioned_tangle_data (A : lt_index α) : positioned_tangle_data A.index :=
phase_2_positioned_assumptions.lower_positioned_tangle_data A

/-! Make the positioned tangle data accessible as an instance for all `lt_index α`,
where the index is accessed through the coercion to `le_index`. -/
instance lt_index_coe_positioned_tangle_data (A : lt_index α) :
  positioned_tangle_data (A : le_index α).index :=
phase_2_positioned_assumptions.lower_positioned_tangle_data A

/-! Make the positioned tangle data accessible as an instance for all `proper_lt_index α`. -/
instance proper_lt_index_positioned_tangle_data (A : proper_lt_index α) :
  positioned_tangle_data A.index :=
phase_2_positioned_assumptions.lower_positioned_tangle_data (A : lt_index α)

/-! Make the positioned tangle data accessible as an instance for all `proper_lt_index α`,
where the index is accessed through the coercion to `lt_index`. -/
instance proper_lt_index_coe_positioned_tangle_data (A : proper_lt_index α) :
  positioned_tangle_data (A : lt_index α).index :=
phase_2_positioned_assumptions.lower_positioned_tangle_data (A : lt_index α)

/-! Make the positioned tangle data accessible as an instance for all `proper_lt_index α`,
where the index is accessed through the coercion to `le_index`. -/
instance proper_lt_index_coe_coe_positioned_tangle_data (A : proper_lt_index α) :
  positioned_tangle_data (A : le_index α).index :=
phase_2_positioned_assumptions.lower_positioned_tangle_data (A : lt_index α)

/-- Along with `phase_2_core_assumptions` and `phase_2_positioned_assumptions`, this is the class
containing the assumptions we take for phase 2 of the recursion. In this class, we assume full
tangle data for all proper type indices `β < α` along all paths. -/
class phase_2_assumptions :=
[lower_almost_tangle_data : Π (A : proper_lt_index α), almost_tangle_data A.index]
[lower_tangle_data : Π (A : proper_lt_index α), tangle_data A.index]
(derivative : Π (A : le_index α) {γ : type_index} (hγ : γ < A.index) (π : allowable A.index),
  allowable (A.cons hγ).index)
(derivative_comm : Π (A : le_index α) {γ : type_index} (hγ : γ < A.index) (π : allowable A.index),
  allowable_to_struct_perm (derivative A hγ π) =
    struct_perm.derivative (path.cons path.nil hγ) (allowable_to_struct_perm π))

/-- The derivative of a permutation along a particular path.
Note that `allowable (A.cons hγ).index` is defeq to `allowable γ`, but by writing it in this form,
lean's typeclass resolution can find the particular instance of `core_tangle_data` that we want. -/
add_decl_doc phase_2_assumptions.derivative

/-- The derivative map commutes with the map from allowable to structural permutations.
The term `path.cons path.nil hγ` is the singleton path `A.index ⟶ γ`.
TODO: Should we refactor `struct_perm.derivative` to use singleton paths as well? -/
add_decl_doc phase_2_assumptions.derivative_comm

attribute [instance]
  phase_2_assumptions.lower_almost_tangle_data
  phase_2_assumptions.lower_tangle_data

variables {α} [phase_2_assumptions α]

/-! There are no additional names that could be used to refer to the instances
`lower_almost_tangle_data` and `lower_tangle_data`, so no new instances need to be defined here. -/

/-!
We can now proceed to define API for the phase 1 constructs in terms of our new types.
Typeclass inference should behave a lot nicer with the utility instances constructed above.
Because of how the instances are all parametrised, all suitable instances of defeq things should
also be defeq to each other.
-/

def tangle_path (A : le_index α) : Type u := tangle A.index

def allowable_path (A : le_index α) : Type u := allowable A.index

def f_map_path {A : lt_index α} (B : proper_lt_index α) (t : tangle_path (A : le_index α)) :=
f_map B.index t

def designated_support_path {A : proper_lt_index α} (t : tangle_path (A : le_index α)) :
  support allowable_to_struct_perm t := designated_support t

end con_nf
