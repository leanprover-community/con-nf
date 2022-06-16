import extended_index
import group_theory.perm.basic
import litter
import params

universe u

namespace con_nf
variable [params.{u}]

open params equiv equiv.perm

-- Suppose that `τ_β` has been constructed for all type indices `β < α`.
class code_params :=
(α : Λ) (tangle : Π (β : type_index), β < α → Type u)
(tangle_atom : tangle ⊥ (with_bot.bot_lt_coe _) = atom)

-- TODO: Do we need `(h : tangle ⊥ _ = atom)`?

open code_params
variable [code_params.{u}]

/-- A type-`β` code is a type index `γ < β` together with a set of tangles of type `γ`. -/
structure code (β : Λ) (β_le_α : β ≤ α) :=
(extension : type_index)
(extension_lt : extension < β)
(elts : set (tangle extension (lt_of_lt_of_le extension_lt (with_bot.coe_le_coe.mpr β_le_α))))

/-- Suppose that the set of tangles embeds into the set of codes. -/
class code_params_embedding :=
(tangle_embedding : Π (β < α), tangle β (with_bot.coe_lt_coe.mpr ‹_›) ↪ code β (le_of_lt ‹_›))
open code_params_embedding
variable [code_params_embedding.{u}]

def code.is_tangle {β < α} (c : code β (le_of_lt ‹_›)) : Prop :=
∃ (t : tangle β (with_bot.coe_lt_coe.mpr ‹_›)), c = tangle_embedding β ‹_› t

/-- A *structural permutation* on a proper type index is defined by its derivatives,
as well as its permutation on atoms. -/
def struct_perm : Π (β : Λ), Type u
| β := (perm atom) × (Π (γ < β), struct_perm γ)
using_well_founded { dec_tac := `[assumption] }

namespace struct_perm

variable {β : Λ}

/-- Obtains the atom permutation given by a prestructural permutation. -/
def atom_perm (π : struct_perm β) : perm atom :=
by { unfold struct_perm at π, exact π.1 }

/-- Obtains the permutations on lower types induced by a prestructural permutation. -/
def lower_code_perm (π : struct_perm β) (γ < β) : struct_perm γ :=
by { unfold struct_perm at π, exact π.2 γ ‹_›}

-- There is no permutation on β-codes since the structural permutations do not act on tangles.

end struct_perm

end con_nf
