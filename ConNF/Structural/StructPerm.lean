import ConNF.BaseType.NearLitterPerm
import ConNF.Structural.Tree

/-!
# Tree permutations

In this file, we define the ambient groups of *structural permutations*.  These will later have
recursively-constructed subgroups of *semi-allowable* and *allowable permutations* which will act on
tangles; we define these larger ambient groups in advance in order to set up their infrastructure of
derivatives and so on independently of the recursion.

We define structural permutations as trees of near-litter permutations.

## Main declarations

* `ConNF.StructPerm`: The type of structural permutations.
-/

open Cardinal Equiv Quiver Quiver.Path Set WithBot

open scoped Cardinal Pointwise

universe u

namespace ConNF

variable [Params.{u}]

/-- A *structural permutation* on a proper type index `α` is a near-litter permutation for
each `α`-extended index. This represents how the permutation acts along each path down the type
levels in the model. Note that we define structural permutations as the structural groups of
near-litter permutations. -/
abbrev StructPerm : TypeIndex → Type u :=
  Tree NearLitterPerm

namespace StructPerm

instance instInhabitedStructPerm (α : TypeIndex) : Inhabited (StructPerm α) :=
  ⟨fun _ => 1⟩

/-! The following lemmas show how the action of `⊥`-structural permutations on near-litters
behaves; this is exactly how near-litter permutations behave. -/

@[simp]
theorem smul_nearLitter_fst (π : StructPerm ⊥) (N : NearLitter) : (π • N).fst = π • N.fst :=
  rfl

theorem smul_nearLitter_coe (π : StructPerm ⊥) (N : NearLitter) :
    ((π • N) : Set Atom) = π • (N : Set Atom) :=
  NearLitterPerm.smul_nearLitter_coe (Tree.ofBot π) N

theorem smul_nearLitter_snd (π : StructPerm ⊥) (N : NearLitter) :
    ((π • N).2 : Set Atom) = π • (N.2 : Set Atom) :=
  NearLitterPerm.smul_nearLitter_snd (Tree.ofBot π) N

end StructPerm

end ConNF
