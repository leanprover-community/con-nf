import ConNF.FOA.Behaviour.NearLitterBehaviour

open Cardinal Quiver Set Sum WithBot

open scoped Cardinal Classical Pointwise symmDiff

universe u

namespace ConNF

variable [Params.{u}] {β : TypeIndex}

/-!
# Structural actions
-/

/-- A `β`-structural action is a product that assigns a near-litter action to each `β`-extended
index. -/
abbrev StructBehaviour :=
  Tree NearLitterBehaviour

namespace StructBehaviour

def Lawful (ξ : StructBehaviour β) : Prop :=
  ∀ A, (ξ A).Lawful

noncomputable def withLitters (ξ : StructBehaviour β) (hξ : ξ.Lawful) : StructBehaviour β :=
  fun A => (ξ A).withLitters (hξ A)

theorem withLitters_lawful (ξ : StructBehaviour β) (hξ : ξ.Lawful) : (ξ.withLitters hξ).Lawful :=
  fun A => (ξ A).withLitters_lawful (hξ A)

end StructBehaviour

end ConNF
