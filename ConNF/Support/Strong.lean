import ConNF.FOA.Inflexible

/-!
# Strong supports

In this file, we define strong supports.

## Main declarations

* `ConNF.Support.Strong`: The property that a support is strong.
-/

noncomputable section
universe u

open Cardinal Ordinal
open scoped symmDiff

namespace ConNF

variable [Params.{u}] {β : TypeIndex}

instance : LE BaseSupport where
  le S T := (Sᴬ : Set Atom) ⊆ Tᴬ ∧ (Sᴺ : Set NearLitter) ⊆ Tᴺ

instance : Preorder BaseSupport where
  le_refl S := ⟨subset_rfl, subset_rfl⟩
  le_trans S T U h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem BaseSupport.smul_le_smul {S T : BaseSupport} (h : S ≤ T) (π : BasePerm) :
    π • S ≤ π • T := by
  constructor
  · simp only [smul_atoms, Enumeration.smul_rel_codom, Set.set_smul_subset_set_smul_iff]
    exact h.1
  · simp only [smul_nearLitters, Enumeration.smul_rel_codom, Set.set_smul_subset_set_smul_iff]
    exact h.2

instance : LE (Support β) where
  le S T := ∀ A, S ⇘. A ≤ T ⇘. A

instance : Preorder (Support β) where
  le_refl S := λ A ↦ le_rfl
  le_trans S T U h₁ h₂ := λ A ↦ (h₁ A).trans (h₂ A)

theorem Support.smul_le_smul {S T : Support β} (h : S ≤ T) (π : StrPerm β) :
    π • S ≤ π • T :=
  λ A ↦ BaseSupport.smul_le_smul (h A) (π A)

namespace Support

variable [Level] [CoherentData] [LeLevel β]

structure Strong (S : Support β) : Prop where
  interference_subset {A : β ↝ ⊥} {N₁ N₂ : NearLitter} :
    N₁ ∈ (S ⇘. A)ᴺ → N₂ ∈ (S ⇘. A)ᴺ → N₁ᴬ ∆ N₂ᴬ ⊆ (S ⇘. A)ᴬ
  support_le {A : β ↝ ⊥} {N : NearLitter} (h : N ∈ (S ⇘. A)ᴺ)
    (P : InflexiblePath β) (t : Tangle P.δ)
    (hA : A = P.A ↘ P.hε ↘.) (ht : Nᴸ = fuzz P.hδε t) :
    t.support ≤ S ⇘ (P.A ↘ P.hδ)

theorem Strong.smul {S : Support β} (hS : S.Strong) (ρ : AllPerm β) : (ρᵁ • S).Strong := by
  constructor
  · intro A N₁ N₂ h₁ h₂
    rw [smul_derivBot, BaseSupport.smul_nearLitters, Enumeration.mem_smul] at h₁ h₂
    rw [smul_derivBot, BaseSupport.smul_atoms, Enumeration.smul_rel_codom, Set.subset_smul_set,
      Set.symmDiff_smul_set]
    exact hS.interference_subset h₁ h₂
  · intro A N hN P t hA ht
    rw [smul_derivBot, BaseSupport.smul_nearLitters, Enumeration.mem_smul] at hN
    have := hS.support_le hN P (ρ⁻¹ ⇘ P.A ↘ P.hδ • t) hA ?_
    · convert smul_le_smul this (ρᵁ ⇘ P.A ↘ P.hδ) using 1
      · rw [Tangle.smul_support, smul_smul,
          allPermSderiv_forget, allPermDeriv_forget, allPermForget_inv,
          Tree.inv_deriv, Tree.inv_sderiv, mul_inv_cancel, one_smul]
      · ext B : 1
        rw [smul_derivBot, Tree.sderiv_apply, Tree.deriv_apply, Path.deriv_scoderiv]
        rfl
    · rw [← smul_fuzz P.hδ P.hε P.hδε, allPermDeriv_forget, allPermForget_inv,
        BasePerm.smul_nearLitter_litter, ← Tree.inv_apply, hA, ht]
      rfl

end Support
end ConNF
