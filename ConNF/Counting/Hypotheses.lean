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
  /-- Tangles contain only tangles. -/
  eq_toPretangle_of_mem (β : Λ) [LeLevel β] (γ : Λ) [LeLevel γ]
    (h : (γ : TypeIndex) < β) (t₁ : TSet β) (t₂ : Pretangle γ) :
    t₂ ∈ Pretangle.ofCoe (toPretangle t₁) γ h → ∃ t₂' : TSet γ, t₂ = toPretangle t₂'
  /-- Tangles are extensional at every proper level `γ < β`. -/
  toPretangle_ext (β γ : Λ) [LeLevel β] [LeLevel γ] (h : (γ : TypeIndex) < β) (t₁ t₂ : TSet β) :
    (∀ t : Pretangle γ,
      t ∈ Pretangle.ofCoe (toPretangle t₁) γ h ↔ t ∈ Pretangle.ofCoe (toPretangle t₂) γ h) →
    toPretangle t₁ = toPretangle t₂
  /-- Any `γ`-tangle can be treated as a singleton at level `β` if `γ < β`. -/
  singleton (β : Λ) [LeLevel β] (γ : Λ) [LeLevel γ]
    (h : (γ : TypeIndex) < β) (t : TSet γ) : TSet β
  singleton_toPretangle (β : Λ) [LeLevel β] (γ : Λ) [LeLevel γ]
    (h : (γ : TypeIndex) < β) (t : TSet γ) :
    Pretangle.ofCoe (toPretangle (singleton β γ h t)) γ h = {toPretangle t}

export CountingAssumptions (eq_toPretangle_of_mem toPretangle_ext
  singleton singleton_toPretangle)

variable [CountingAssumptions] {β γ : Λ} [LeLevel β] [LeLevel γ] (hγ : γ < β)

theorem singleton_smul (β γ : Λ) [LeLevel β] [LeLevel γ] (h : (γ : TypeIndex) < β) (t : TSet γ)
    (ρ : Allowable β) :
    ρ • singleton β γ h t = singleton β γ h (Allowable.comp (Hom.toPath h) ρ • t) := by
  refine toPretangle.inj' ?_
  refine toPretangle_ext β γ h _ _ ?_
  intro u
  rw [toPretangle_smul, Allowable.toStructPerm_smul, StructPerm.ofCoe_smul,
    singleton_toPretangle, singleton_toPretangle, smul_set_singleton,
    mem_singleton_iff, mem_singleton_iff, toPretangle_smul, Allowable.toStructPerm_smul,
    Allowable.toStructPerm_comp]

theorem singleton_injective (β γ : Λ) [LeLevel β] [LeLevel γ] (h : (γ : TypeIndex) < β) :
    Function.Injective (singleton β γ h) := by
  intro t₁ t₂ ht
  have h₁ := singleton_toPretangle β γ h t₁
  have h₂ := singleton_toPretangle β γ h t₂
  rw [ht, h₂, singleton_eq_singleton_iff] at h₁
  exact toPretangle.inj' h₁.symm

end ConNF
