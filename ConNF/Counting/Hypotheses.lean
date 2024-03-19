import ConNF.Structural.Pretangle
import ConNF.FOA.Basic.Reduction
import ConNF.Counting.CodingFunction

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
    t₁ = t₂
  /-- Any `γ`-tangle can be treated as a singleton at level `β` if `γ < β`. -/
  singleton (β : Λ) [LeLevel β] (γ : TypeIndex) [LeLevel γ] (h : γ < β) (t : Tangle γ) : Tangle β
  singleton_injective (β : Λ) [LeLevel β] (γ : TypeIndex) [LeLevel γ] (h : γ < β) :
    Function.Injective (singleton β γ h)
  singleton_toPretangle (β : Λ) [LeLevel β] (γ : TypeIndex) [LeLevel γ] (h : γ < β) (t : Tangle γ) :
    Pretangle.ofCoe (toPretangle β (singleton β γ h t)) γ h = {toPretangle γ t}
  mk_codingFunction_zero : #(CodingFunction 0) < #μ

export CountingAssumptions (toPretangle toPretangle_smul eq_toPretangle_of_mem toPretangle_ext
  singleton singleton_injective singleton_toPretangle mk_codingFunction_zero)

variable [CountingAssumptions] {β γ : Λ} [LeLevel β] [LeLevel γ] (hγ : γ < β)

theorem singleton_smul (β γ : Λ) [LeLevel β] [LeLevel γ] (h : (γ : TypeIndex) < β) (t : Tangle γ)
    (ρ : Allowable β) :
    ρ • singleton β γ h t = singleton β γ h (Allowable.comp (Hom.toPath h) ρ • t) := by
  refine toPretangle_ext β γ h _ _ ?_
  intro u
  rw [toPretangle_smul, Allowable.toStructPerm_smul, StructPerm.ofCoe_smul,
    singleton_toPretangle, singleton_toPretangle, smul_set_singleton,
    mem_singleton_iff, mem_singleton_iff, toPretangle_smul, Allowable.toStructPerm_smul,
    Allowable.toStructPerm_comp]

end ConNF
