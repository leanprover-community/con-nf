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
def struct_perm : Π (β : Λ), Type u
| β := perm atom × Π γ < β, struct_perm γ
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

/-- We construct the ordering on extended type indices such that when we remove the lowest arrow,
the resulting path is considered smaller. -/
lemma drop_min_lt {β : Λ} {γ δ : type_index}
(a : quiver.path (β : type_index) γ) (b : γ ⟶ δ) (c : δ ⟶ ⊥) :
extended_index.lt (a.cons (lt_trans c b) : extended_index β) ((a.cons b).cons c : extended_index β) :=
begin
  sorry
end

noncomputable def derivative_core : Π (A : extended_index β), struct_perm β → struct_perm A.min
| (quiver.path.cons quiver.path.nil _) := id
| (@quiver.path.cons _ _ _ p _ (@quiver.path.cons _ _ _ q _ a b) c) :=
  λ π, begin
    refine (derivative_core (quiver.path.cons a (lt_trans c b)) π).lower_code_perm _ _,
    induction p, { unfold quiver.hom at c, simp at c, contradiction },
    induction q, { unfold quiver.hom at b, simp at b, contradiction },
    unfold quiver.hom at b, simp at b, exact b
  end
using_well_founded { dec_tac := `[exact drop_min_lt a b c] }

/-- The derivative of a structural permutation with respect to a given extended type index. -/
def derivative (π : struct_perm β) (A : extended_index β) : struct_perm A.min :=
derivative_core A π

end struct_perm

end con_nf
