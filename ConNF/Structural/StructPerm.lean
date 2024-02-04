import ConNF.BaseType.NearLitterPerm
import ConNF.Structural.Tree
import ConNF.Structural.Pretangle

/-!
# Structural permutations

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
levels in the model. Note that we define structural permutations as trees of near-litter
permutations. -/
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
    (π • N : NearLitter) = π • (N : Set Atom) :=
  NearLitterPerm.smul_nearLitter_coe (Tree.ofBot π) N

theorem smul_nearLitter_snd (π : StructPerm ⊥) (N : NearLitter) :
    ((π • N).2 : Set Atom) = π • (N.2 : Set Atom) :=
  NearLitterPerm.smul_nearLitter_snd (Tree.ofBot π) N

@[simp]
theorem comp_bot_smul_atom {α : TypeIndex} (π : StructPerm α)
    (A : ExtendedIndex α) (a : Atom) :
    Tree.comp A π • a = π A • a :=
  rfl

@[simp]
theorem comp_bot_smul_litter {α : TypeIndex} (π : StructPerm α)
    (A : ExtendedIndex α) (L : Litter) :
    Tree.comp A π • L = π A • L :=
  rfl

@[simp]
theorem comp_bot_smul_nearLitter {α : TypeIndex} (π : StructPerm α)
    (A : ExtendedIndex α) (N : NearLitter) :
    Tree.comp A π • N = π A • N :=
  rfl

def pretangleAction : {α : TypeIndex} → StructPerm α → Pretangle α → Pretangle α
  | ⊥, π, t => Tree.ofBot π • (Pretangle.ofBot t)
  | (α : Λ), π, t => Pretangle.toCoe
      (fun β hβ => pretangleAction (Tree.comp (Hom.toPath hβ) π) '' Pretangle.ofCoe t β hβ)
termination_by α π t => α

theorem one_pretangleAction {α : TypeIndex} (t : Pretangle α) : pretangleAction 1 t = t := by
  have : WellFoundedLT TypeIndex := inferInstance
  revert t
  refine this.induction α (C := fun α => ∀ t : Pretangle α, pretangleAction 1 t = t) ?_
  intro α ih t
  induction α using WithBot.recBotCoe with
  | bot =>
      unfold pretangleAction
      rfl
  | coe α =>
      unfold pretangleAction
      rw [Pretangle.coe_ext]
      intro β hβ u
      simp only [Tree.comp_one, Pretangle.ofCoe_toCoe, ih β hβ, image_id']

theorem mul_pretangleAction {α : TypeIndex} (π₁ π₂ : StructPerm α) (t : Pretangle α) :
    pretangleAction (π₁ * π₂) t = pretangleAction π₁ (pretangleAction π₂ t) := by
  have : WellFoundedLT TypeIndex := inferInstance
  revert π₁ π₂ t
  refine this.induction α
    (C := fun α => ∀ π₁ π₂ : StructPerm α, ∀ t : Pretangle α,
      pretangleAction (π₁ * π₂) t = pretangleAction π₁ (pretangleAction π₂ t)) ?_
  intro α ih π₁ π₂ t
  induction α using WithBot.recBotCoe with
  | bot =>
      unfold pretangleAction
      rfl
  | coe α =>
      rw [pretangleAction, pretangleAction, pretangleAction]
      simp only [Tree.comp_mul, Pretangle.ofCoe_toCoe, EmbeddingLike.apply_eq_iff_eq]
      ext β hβ u
      simp only [ih β hβ, mem_image, exists_exists_and_eq_and]

instance {α : TypeIndex} : MulAction (StructPerm α) (Pretangle α) where
  smul := pretangleAction
  one_smul := one_pretangleAction
  mul_smul := mul_pretangleAction

theorem smul_eq {α : TypeIndex} (π : StructPerm α) (t : Pretangle α) :
    π • t = pretangleAction π t :=
  rfl

theorem ofCoe_smul {α : Λ} {β : TypeIndex} (π : StructPerm α) (t : Pretangle α) (h : β < α) :
    Pretangle.ofCoe (π • t) β h = Tree.comp (Hom.toPath h) π • Pretangle.ofCoe t β h := by
  ext u
  simp only [smul_eq, pretangleAction, Pretangle.ofCoe_toCoe, mem_image, mem_smul_set]

end StructPerm

end ConNF
