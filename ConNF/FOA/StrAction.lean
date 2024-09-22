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

theorem Coherent.deriv {ξ : StrAction β} (hξ : ξ.Coherent)
    {γ : TypeIndex} [LeLevel γ] (A : β ↝ γ) :
    Coherent (ξ ⇘ A) :=
  λ B L₁ L₂ h ↦ (hξ (A ⇘ B) L₁ L₂ h).deriv

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

/-- TODO: Maybe move this to `BaseActionClass`? -/
structure BaseAction.Approximates (ξ : BaseAction) (π : BasePerm) : Prop where
  atoms : ∀ a₁ a₂, ξᴬ a₁ a₂ → a₂ = π • a₁
  nearLitters : ∀ N₁ N₂, ξᴺ N₁ N₂ → N₂ = π • N₁

theorem BaseAction.Approximates.litters {ξ : BaseAction} {π : BasePerm} (h : ξ.Approximates π)
    (L₁ L₂ : Litter) : ξᴸ L₁ L₂ → π • L₁ = L₂ := by
  intro hL
  rw [litters_iff] at hL
  obtain ⟨N₁, N₂, rfl, rfl, hN⟩ := hL
  exact congr_arg (·ᴸ) (h.nearLitters N₁ N₂ hN).symm

theorem BaseAction.Approximates.mono {ψ χ : BaseAction} {π : BasePerm}
    (hχ : χ.Approximates π) (h : ψ ≤ χ) :
    ψ.Approximates π := by
  constructor
  · intro a₁ a₂ hψ
    exact hχ.atoms a₁ a₂ (h.1 a₁ a₂ hψ)
  · intro N₁ N₂ hψ
    exact hχ.nearLitters N₁ N₂ (h.2 ▸ hψ)

def StrAction.Approximates {β : TypeIndex} [ModelData β]
    (ξ : StrAction β) (ρ : AllPerm β) : Prop :=
  ∀ A, (ξ A).Approximates (ρᵁ A)

def StrAction.flexApprox [Level] {β : TypeIndex} [LeLevel β] [CoherentData]
    (ξ : StrAction β) : StrApprox β :=
  λ A ↦ (ξ A).flexApprox A

/-- TODO: Put this in the blueprint. -/
theorem StrAction.flexApprox_coherent [Level] {β : TypeIndex} [LeLevel β] [CoherentData]
    (ξ : StrAction β) (hξ : ∀ A, (ξ A).MapFlexible A) :
    StrApprox.Coherent ξ.flexApprox := by
  intro A L₁ L₂ hL
  constructor
  · intro P t hA ht
    cases ((ξ A).flexApprox_flexApprox (hξ A)).flexible_of_mem_dom ⟨L₂, hL⟩ ⟨P, t, hA, ht⟩
  · intro _
    apply ((ξ A).flexApprox_flexApprox (hξ A)).flexible_of_mem_dom
    rw [← (BaseApprox.litters_permutative _).codom_eq_dom]
    exact ⟨L₁, hL⟩

end ConNF
