import ConNF.FOA.FlexApprox

/-!
# Structural actions

In this file, we define structural actions, and prove the freedom of action theorem for actions.

## Main declarations

* `ConNF.StrAction`: Structural actions.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}]

abbrev StrAction : TypeIndex → Type u :=
  Tree BaseAction

namespace StrAction

variable [Level] [CoherentData] {β : TypeIndex} [LeLevel β] {A : β ↝ ⊥}

def Coherent (ξ : StrAction β) : Prop :=
  ∀ A L₁ L₂, (ξ A)ᴸ L₁ L₂ → CoherentAt ξ A L₁ L₂

theorem mapFlexible_of_coherent {ξ : StrAction β} (hξ : ξ.Coherent) (A : β ↝ ⊥) :
    (ξ A).MapFlexible A := by
  intro L₁ L₂ h
  specialize hξ A L₁ L₂ h
  constructor
  · rintro ⟨P, t, hA, ht⟩
    obtain ⟨ρ, _, hρ⟩ := hξ.inflexible P t hA ht
    exact ⟨P, ρ • t, hA, hρ⟩
  · contrapose
    exact hξ.flexible

end StrAction
end ConNF
