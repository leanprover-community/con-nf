import ConNF.Structural.Pretangle
import ConNF.FOA.Basic.Reduction

/-!
# Hypotheses
-/

open MulAction Quiver Set Sum WithBot

open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions]

instance : LeLevel (0 : Λ) := ⟨WithBot.coe_le_coe.mpr (Params.Λ_zero_le _)⟩

class CountingAssumptions extends FOAAssumptions where
  toPretangle (β : TypeIndex) [LeLevel β] : Tangle β → Pretangle β
  toPretangle_smul (β : TypeIndex) [LeLevel β] (ρ : Allowable β) (t : Tangle β) :
    toPretangle β (ρ • t) = ρ • toPretangle β t
  /-- Tangles contain only tangles. -/
  eq_toPretangle_of_mem (β : Λ) [LeLevel β] (γ : Λ) [LeLevel γ]
    (h : (γ : TypeIndex) < β) (t₁ : Tangle β) (t₂ : Pretangle γ) :
    t₂ ∈ Pretangle.ofCoe (toPretangle β t₁) γ h → ∃ t₂' : Tangle γ, t₂ = toPretangle γ t₂'
  /-- Tangles are extensional at every proper level `γ < β`. -/
  toPretangle_ext (β γ : Λ) [LeLevel β] [LeLevel γ] (h : (γ : TypeIndex) < β) (t₁ t₂ : Tangle β) :
    (∀ t : Pretangle γ,
      t ∈ Pretangle.ofCoe (toPretangle β t₁) γ h ↔ t ∈ Pretangle.ofCoe (toPretangle β t₂) γ h) →
    toPretangle β t₁ = toPretangle β t₂
  tangle_ext (β : Λ) [LeLevel β] (t₁ t₂ : Tangle β) :
    toPretangle β t₁ = toPretangle β t₂ → t₁.support = t₂.support → t₁ = t₂
  /-- Any `γ`-tangle can be treated as a singleton at level `β` if `γ < β`. -/
  singleton (β : Λ) [LeLevel β] (γ : TypeIndex) [LeLevel γ] (h : γ < β) (t : Tangle γ) : Tangle β
  singleton_support (β : Λ) [LeLevel β] (γ : TypeIndex) [LeLevel γ] (h : γ < β) (t : Tangle γ) :
    (singleton β γ h t).support = t.support.image (fun c => ⟨(Hom.toPath h).comp c.1, c.2⟩)
  singleton_toPretangle (β : Λ) [LeLevel β] (γ : TypeIndex) [LeLevel γ] (h : γ < β) (t : Tangle γ) :
    Pretangle.ofCoe (toPretangle β (singleton β γ h t)) γ h = {toPretangle γ t}

export CountingAssumptions (toPretangle toPretangle_smul eq_toPretangle_of_mem toPretangle_ext
  tangle_ext singleton singleton_support singleton_toPretangle)

variable [CountingAssumptions] {β γ : Λ} [LeLevel β] [LeLevel γ] (hγ : γ < β)

theorem singleton_smul (β γ : Λ) [LeLevel β] [LeLevel γ] (h : (γ : TypeIndex) < β) (t : Tangle γ)
    (ρ : Allowable β) :
    ρ • singleton β γ h t = singleton β γ h (Allowable.comp (Hom.toPath h) ρ • t) := by
  refine tangle_ext β _ _ ?_ ?_
  · refine toPretangle_ext β γ h _ _ ?_
    intro u
    rw [toPretangle_smul, Allowable.toStructPerm_smul, StructPerm.ofCoe_smul,
      singleton_toPretangle, singleton_toPretangle, smul_set_singleton,
      mem_singleton_iff, mem_singleton_iff, toPretangle_smul, Allowable.toStructPerm_smul,
      Allowable.toStructPerm_comp]
  · rw [smul_support, singleton_support, singleton_support]
    refine Enumeration.ext' ?_ ?_
    · simp only [Enumeration.smul_max, Enumeration.image_max, smul_support]
    · intro i h₁ h₂
      simp only [Enumeration.smul_f, Enumeration.image_f, Allowable.smul_address, smul_support,
        Allowable.toStructPerm_comp, Tree.comp_apply]

theorem singleton_injective (β γ : Λ) [LeLevel β] [LeLevel γ] (h : (γ : TypeIndex) < β) :
    Function.Injective (singleton β γ h) := by
  intro t₁ t₂ ht
  refine tangle_ext γ _ _ ?_ ?_
  · have h₁ := singleton_toPretangle β γ h t₁
    have h₂ := singleton_toPretangle β γ h t₂
    rw [ht, h₂, singleton_eq_singleton_iff] at h₁
    exact h₁.symm
  · have h₁ := singleton_support β γ h t₁
    have h₂ := singleton_support β γ h t₂
    rw [ht, h₂] at h₁
    refine Enumeration.ext' ?_ ?_
    · have := congr_arg Enumeration.max h₁
      simp only [Enumeration.image_max] at this
      exact this.symm
    · intro i hi₁ hi₂
      have := support_f_congr h₁ i hi₂
      simp only [Enumeration.image_f, Address.mk.injEq] at this
      refine Address.ext _ _ ?_ ?_
      · exact Path.comp_inj_right.mp this.1.symm
      · exact this.2.symm

end ConNF
