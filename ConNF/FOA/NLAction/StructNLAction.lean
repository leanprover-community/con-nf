import ConNF.FOA.NLAction.BaseNLAction

open Cardinal Quiver Set Sum WithBot

open scoped Cardinal Classical Pointwise symmDiff

universe u

namespace ConNF

variable [Params.{u}] {β : TypeIndex}

/-!
# Structural actions
-/

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
