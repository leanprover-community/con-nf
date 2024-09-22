import ConNF.FOA.StrAction
import ConNF.FOA.StrApproxFOA

/-!
# Freedom of action for structural actions

In this file, we state and prove the freedom of action theorem for structural actions.

## Main declarations

* `ConNF.StrAction.freedomOfAction`: Freedom of action for structural actions.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}] [Level] [CoherentData] {β : TypeIndex} [LeLevel β]

namespace StrAction

def FreedomOfAction (β : TypeIndex) [LeLevel β] : Prop :=
  ∀ ξ : StrAction β, ξ.Coherent → ∃ ρ, ξ.Approximates ρ

theorem approximates_of_flexApprox_exactlyApproximates {ξ : StrAction β} (hξ : ξ.Coherent)
    {ρ : AllPerm β} (hρ : ξ.flexApprox.ExactlyApproximates ρ) :
    ξ.Approximates ρ := by
  intro A
  constructor
  · intro a₁ a₂ ha
    have := ((ξ A).flexApprox_flexApprox (ξ.mapFlexible_of_coherent hξ A)).atoms_le_atoms a₁ a₂ ha
    exact (hρ A).atoms a₁ a₂ (Or.inl this)
  intro N₁ N₂ h
  symm
  induction N₁ using pos_induction generalizing A N₂ with
  | h N₁ ih =>
    apply BaseAction.smul_nearLitter_of_smul_litter
      ((ξ A).flexApprox_flexApprox (ξ.mapFlexible_of_coherent hξ A)) (hρ A) h
    obtain (⟨P, t, hA, ht⟩ | hN₁) := inflexible_cases A N₁ᴸ
    · rw [ht, hA]
      suffices (ρ ⇘ P.A)ᵁ ↘ P.hε ↘. • fuzz P.hδε t = N₂ᴸ by
        rw [← this, allPermDeriv_forget]
        rfl
      rw [smul_fuzz P.hδ P.hε P.hδε]
      obtain ⟨ρ', hρ', _⟩ := (hξ A N₁ᴸ N₂ᴸ (BaseAction.litters.mk h)).inflexible P t hA ht
      refine (smul_eq_of_coherentAt_inflexible hA ht (hξ A N₁ᴸ N₂ᴸ (BaseAction.litters.mk h))
        (ρ ⇘ P.A ↘ P.hδ) ?_).symm
      simp only [smul_support_eq_smul_iff, Tree.sderiv_apply, Tree.deriv_apply, Path.deriv_scoderiv,
        allPermSderiv_forget, allPermDeriv_forget] at hρ' ⊢
      intro B
      constructor
      · intro a ha
        have ha' := (hρ' B).1 a ha
        have := ((ξ (P.A ↘ P.hδ ⇘ B)).flexApprox_flexApprox
          (mapFlexible_of_coherent hξ _)).atoms_le_atoms _ _ ha'
        rwa [(hρ (P.A ↘ P.hδ ⇘ B)).atoms _ _ (Or.inl this)] at ha'
      · intro N hN
        have hN' := (hρ' B).2 N hN
        have := ih N ?_ (P.A ↘ P.hδ ⇘ B) _ hN'
        · rwa [this]
        · apply (pos_nearLitter_lt_pos t B N hN).trans
          apply (pos_fuzz P.hδε t).trans
          rw [← ht]
          exact N₁.pos_litter_lt_pos
    · have := ((ξ A).flexApprox_flexApprox (ξ.mapFlexible_of_coherent hξ A)).litters_of_flexible
        hN₁ (BaseAction.litters.mk h)
      obtain ⟨N₃, hN₃⟩ := (ξ.flexApprox A).mem_dom_nearLitters
        (N := N₁ᴸᴺ) ⟨N₂ᴸ, this⟩ (λ a h ↦ (h.2 h.1).elim)
      rw [(ξ.flexApprox A).litters_permutative.coinjective this hN₃.1]
      exact (congr_arg (·ᴸ) ((hρ A).nearLitters _ _ hN₃)).symm

theorem freedomOfAction : FreedomOfAction β := by
  intro ξ hξ
  obtain ⟨ρ, hρ⟩ := ξ.flexApprox.freedomOfAction
    (ξ.flexApprox_coherent (ξ.mapFlexible_of_coherent hξ))
  exact ⟨ρ, approximates_of_flexApprox_exactlyApproximates hξ hρ⟩

end StrAction
end ConNF
