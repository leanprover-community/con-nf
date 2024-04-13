import ConNF.BaseType.NearLitterPerm
import ConNF.Structural.Tree
import ConNF.Structural.StructSet

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

def structSetAction : {α : TypeIndex} → StructPerm α → StructSet α → StructSet α
  | ⊥, π, t => Tree.ofBot π • (StructSet.ofBot t)
  | (α : Λ), π, t => StructSet.toCoe
      (fun β hβ => structSetAction (Tree.comp (Hom.toPath hβ) π) '' StructSet.ofCoe t β hβ)
termination_by α π t => α

theorem one_structSetAction {α : TypeIndex} (t : StructSet α) : structSetAction 1 t = t := by
  have : WellFoundedLT TypeIndex := inferInstance
  revert t
  refine this.induction α (C := fun α => ∀ t : StructSet α, structSetAction 1 t = t) ?_
  intro α ih t
  induction α using WithBot.recBotCoe with
  | bot =>
      unfold structSetAction
      rfl
  | coe α =>
      unfold structSetAction
      rw [StructSet.coe_ext]
      intro β hβ u
      simp only [Tree.comp_one, StructSet.ofCoe_toCoe, ih β hβ, image_id']

theorem mul_structSetAction {α : TypeIndex} (π₁ π₂ : StructPerm α) (t : StructSet α) :
    structSetAction (π₁ * π₂) t = structSetAction π₁ (structSetAction π₂ t) := by
  have : WellFoundedLT TypeIndex := inferInstance
  revert π₁ π₂ t
  refine this.induction α
    (C := fun α => ∀ π₁ π₂ : StructPerm α, ∀ t : StructSet α,
      structSetAction (π₁ * π₂) t = structSetAction π₁ (structSetAction π₂ t)) ?_
  intro α ih π₁ π₂ t
  induction α using WithBot.recBotCoe with
  | bot =>
      unfold structSetAction
      rfl
  | coe α =>
      rw [structSetAction, structSetAction, structSetAction]
      simp only [Tree.comp_mul, StructSet.ofCoe_toCoe, EmbeddingLike.apply_eq_iff_eq]
      ext β hβ u
      simp only [ih β hβ, mem_image, exists_exists_and_eq_and]

instance {α : TypeIndex} : MulAction (StructPerm α) (StructSet α) where
  smul := structSetAction
  one_smul := one_structSetAction
  mul_smul := mul_structSetAction

theorem smul_eq {α : TypeIndex} (π : StructPerm α) (t : StructSet α) :
    π • t = structSetAction π t :=
  rfl

theorem ofCoe_smul {α : Λ} {β : TypeIndex} (π : StructPerm α) (t : StructSet α) (h : β < α) :
    StructSet.ofCoe (π • t) β h = Tree.comp (Hom.toPath h) π • StructSet.ofCoe t β h := by
  ext u
  simp only [smul_eq, structSetAction, StructSet.ofCoe_toCoe, mem_image, mem_smul_set]

end StructPerm

end ConNF
