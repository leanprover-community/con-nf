import allowable

noncomputable theory

open cardinal cardinal.is_regular equiv equiv.perm function set with_bot
open_locale cardinal

universe u

namespace con_nf
variables [params.{u}]

open params

/-- A pretangle has a preferred extension, which is either a proper type `β : Λ`,
or the base type `-1`. A pretangle has a `-1`-extension if and only if its preferred extension
is the `-1`-extension. -/
inductive preferred_extension (α : Λ) : Type u
| proper_extension : Π (β < α), preferred_extension
| base_extension : set atom → preferred_extension

/-- A *pretangle* is an object that may become a *tangle*,
an element of the model.
The type of pretangles forms a model of TTT without extensionality. -/
def pretangle : Λ → Type u
| α := set atom × Π β < α, set (pretangle β)
using_well_founded { dec_tac := `[assumption] }

namespace pretangle

/-- Obtains the members of a pretangle of type `α`, seen as a set of atoms. -/
def atom_members {α : Λ} (a : pretangle α) : set atom :=
by { unfold pretangle at a, exact a.fst }

/-- Obtains the members of a pretangle of type `α`, seen as a set of elements of type `β < α`. -/
def members {α : Λ} (a : pretangle α) : Π (β < α), set (pretangle β) :=
by { unfold pretangle at a, exact a.snd }

/-- The membership relation defined on pretangles for atoms. -/
instance has_mem_atom {α : Λ} : has_mem atom (pretangle α) :=
⟨λ b a, b ∈ a.atom_members⟩

-- Yaël: Note, this instance is useless as it won't fire because `β < α` is not a class
/-- The membership relation defined on pretangles.
This is exactly the membership relation on tangles, without the extensionality condition that
allows this membership relation to be used in a model of TTT. -/
instance has_mem {α β : Λ} (h : β < α) : has_mem (pretangle β) (pretangle α) :=
⟨λ b a, b ∈ a.members β h⟩

end pretangle

open params
variables [params.{u}] (α : Λ) [phase_1a.{u} α]

/-- A *semitangle* may become an element of our model of tangled type theory.
We keep track of its members, written as tangles of all lower levels `β < α`.
The preferred extension is either a proper type index `β < α`, or it is `-1`, in which case
we store its `-1`-extension as a set of atoms in the `preferred_extension` field.

Here, we restrict our definition to just nonempty semitangles; this simplifies the definition. -/
structure nonempty_semitangle :=
(members (β : Λ) (hβ : β < α) : set (tangle α β $ coe_lt_coe.mpr hβ))
(preferred_extension : Iio α ⊕ set atom)
(members_nonempty (β : Λ) (hβ : β < α) : (members β hβ).nonempty)
(extension_nonempty : preferred_extension.elim
  (λ β, true)
  (λ (atoms : set atom), atoms.nonempty))
(extension_condition : @sum.rec_on _ _
  (λ x, ∀ (h : x.elim (λ β, true) (λ (atoms : set atom), atoms.nonempty)), Prop) preferred_extension
  (λ (β : Iio α) cond,
    let c : code α α le_rfl := ⟨β.val, coe_lt_coe.mpr β.property, members β.val β.property⟩
    in c.is_representative ∧ ∀ δ (hδ : δ < α) (hγδ : β.val ≠ δ),
      A_map_code hδ ⟨c, members_nonempty β.val β.property⟩
      = ⟨⟨δ, coe_lt_coe.mpr hδ, members δ hδ⟩, members_nonempty δ hδ⟩)
  (λ (atoms : set atom) cond,
    let c : code α α le_rfl := ⟨⊥, bot_lt_coe _, atoms⟩
    in c.is_representative ∧ ∀ δ (hδ : δ < α),
      A_map_code hδ ⟨c, cond⟩ = ⟨⟨δ, coe_lt_coe.mpr hδ, members δ hδ⟩, members_nonempty δ hδ⟩)
  extension_nonempty)

-- TODO: Are we supposed to have a membership relation on tangles or semitangles?
def nonempty_semitangle.mem {β : Λ} (hβ : β < α)
  (t : tangle α β (coe_lt_coe.mpr hβ)) (s : nonempty_semitangle α) := t ∈ s.members β hβ

/-- A semitangle is either a nonempty semitangle, or the `⊥` element, which is considered the empty
set. Note that in TTT, a set contains no elements at one level if and only if it contains no
elements at all levels. -/
@[reducible] def semitangle := with_bot (nonempty_semitangle α)

/-- The membership relation of tangles and semitangles in TTT at this level. -/
def semitangle.mem {β : Λ} (hβ : β < α)
  (t : tangle α β (coe_lt_coe.mpr hβ)) (s : semitangle α) :=
  s.elim false (nonempty_semitangle.mem α hβ t)

variable [phase_1b.{u u} α]

/-- Allowable permutations act on nonempty semitangles. -/
instance nonempty_semitangle.has_scalar :
  has_scalar (allowable_perm α le_rfl) (nonempty_semitangle α) := sorry

/-- Allowable permutations act on semitangles. -/
instance semitangle.has_scalar : has_scalar (allowable_perm α le_rfl) (semitangle α) :=
⟨λ π s, with_bot.rec_bot_coe ⊥ (λ s, some $ π • s) s⟩

instance semitangle.mul_action : mul_action (allowable_perm α le_rfl) (semitangle α) := sorry

/-- A tangle at the new level `α` is a symmetric semitangle. This is `τ_α` in the blueprint.
Unlike the type `tangle`, this is not an opaque definition, and we can inspect and unfold it. -/
def new_tangle :=
{s : semitangle α // symmetric (λ (π : allowable_perm α le_rfl), π.val.to_struct_perm) s}

end con_nf
