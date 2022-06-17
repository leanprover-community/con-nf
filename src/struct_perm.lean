import litter
import type_index

/-!
# Structural permutations

Structural permutations In this file, we define the ambient groups of *structural permutations*.  These will later have recursively-constructed subgroups of *semi-allowable* and *allowable permutations* which will act on tangles; we define these larger ambient groups in advance in order to set up their infrastructure of derivatives and so on independently of the recursion.
-/

open equiv equiv.perm with_bot

noncomputable theory

universe u

namespace con_nf
variable [params.{u}]

open params

/-- A *structural permutation* on a proper type index is defined by its derivatives,
as well as its permutation on atoms. -/
/- Note: perhaps should be constructed directly as *groups*, not just types. -/
noncomputable def struct_perm : Π (β : type_index), Type u
| none := near_litter_perm
| β := Π γ < β, struct_perm γ
using_well_founded { dec_tac := `[assumption] }

namespace struct_perm

variable {β : Λ}

/-- Obtains the atom permutation given by a prestructural permutation. -/
def atom_perm (π : struct_perm β) : perm atom :=
by { sorry } /- unfold struct_perm at π, exact π.1 -/

/-- Obtains the permutations on lower types induced by a prestructural permutation. -/
def lower_code_perm (π : struct_perm β) (γ < β) : struct_perm γ :=
by { sorry } /- unfold struct_perm at π, exact π.2 γ ‹_› -/

/-- the derivative of a structural permutation at any lower level -/
noncomputable def derivative {β : Λ} : Π {γ : type_index} (A : quiver.path (β : type_index) γ), struct_perm β → struct_perm γ
| _ quiver.path.nil := id
| _ (@quiver.path.cons _ _ _ δ _ a b) :=
  λ π, begin
    refine π.lower_code_perm _ _,
    sorry
    end

end struct_perm

end con_nf
