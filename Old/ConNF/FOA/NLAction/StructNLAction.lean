import ConNF.FOA.NLAction.BaseNLAction

/-!
# Structural near-litter actions

In this file, we define structural near-litter actions, which are trees of base near-litter actions.

## Main declarations

* `ConNF.StructNLAction`: A tree of base near-litter actions.
* `ConNF.StructNLAction.Lawful`, `ConNF.StructNLAction.Approximates`: Branchwise definitions of
    lawfulness and approximation.
* `ConNF.StructNLAction.withLitters`: Branchwise augmentation of near-litter action to define its
    value on all litters associated to near-litters in its domain.
-/

open Cardinal Quiver Set Sum WithBot

open scoped Cardinal Classical Pointwise symmDiff

universe u

namespace ConNF

variable [Params.{u}] {β : TypeIndex}

/-- A `β`-structural action is a product that assigns a base near-litter action to each `β`-extended
index. -/
abbrev StructNLAction :=
  Tree BaseNLAction

namespace StructNLAction

def Lawful (ξ : StructNLAction β) : Prop :=
  ∀ A, (ξ A).Lawful

def Approximates (ξ : StructNLAction β) (π : StructPerm β) : Prop :=
  ∀ A, (ξ A).Approximates (π A)

noncomputable def withLitters (ξ : StructNLAction β) (hξ : ξ.Lawful) : StructNLAction β :=
  fun A => (ξ A).withLitters (hξ A)

theorem withLitters_lawful (ξ : StructNLAction β) (hξ : ξ.Lawful) : (ξ.withLitters hξ).Lawful :=
  fun A => (ξ A).withLitters_lawful (hξ A)

end StructNLAction

end ConNF
