import ConNF.Structural.Pretangle
import ConNF.Foa.Basic.Reduction

/-!
# Hypotheses
-/

open MulAction Quiver Set Sum WithBot

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions]

class CountingAssumptions (α : Λ) [BasePositions] extends FoaAssumptions α where
  toPretangle (β : IicBot α) : Tangle β → Pretangle β
  toPretangle_smul (β : IicBot α) (ρ : Allowable β) (t : Tangle β) :
    toPretangle β (ρ • t) = ρ • toPretangle β t
  /-- Tangles contain only tangles. -/
  eq_toPretangle_of_mem (β : Iic α) (γ : IicBot α) (h : γ < β) (t₁ : Tangle β) (t₂ : Pretangle γ) :
    t₂ ∈ Pretangle.ofCoe (toPretangle β t₁) γ h → ∃ t₂' : Tangle γ, t₂ = toPretangle γ t₂'
  /-- Tangles are extensional at every proper level `γ < β`. -/
  toPretangle_ext (β γ : Iic α) (h : γ < β) (t₁ t₂ : Tangle β) :
    (∀ t : Pretangle γ,
      t ∈ Pretangle.ofCoe (toPretangle β t₁) γ (coe_lt_coe.mpr h) ↔
      t ∈ Pretangle.ofCoe (toPretangle β t₂) γ (coe_lt_coe.mpr h)) →
    t₁ = t₂
  /-- Any `γ`-tangle can be treated as a singleton at level `β` if `γ < β`. -/
  singleton (β : Iic α) (γ : IicBot α) (h : γ < β) (t : Tangle γ) : Tangle β
  singleton_toPretangle (β : Iic α) (γ : IicBot α) (h : γ < β) (t : Tangle γ) :
    Pretangle.ofCoe (toPretangle β (singleton β γ h t)) γ h = {toPretangle γ t}

export CountingAssumptions (toPretangle toPretangle_smul eq_toPretangle_of_mem toPretangle_ext
  singleton singleton_toPretangle)

variable [CountingAssumptions α] {β γ : Iic α} (hγ : γ < β)

theorem singleton_smul (β : Iic α) (γ : Iic α) (h : (γ : IicBot α) < β) (t : Tangle γ)
    (ρ : Allowable β) :
    ρ • singleton β γ h t = singleton β γ h (Allowable.comp (Hom.toPath h) ρ • t) := by
  refine toPretangle_ext β γ ?_ _ _ ?_
  · simp only [Subtype.mk_lt_mk, coe_lt_coe, Subtype.coe_lt_coe] at h
    exact h
  intro u
  rw [toPretangle_smul, Allowable.toStructPerm_smul, StructPerm.ofCoe_smul,
    singleton_toPretangle, singleton_toPretangle, smul_set_singleton,
    mem_singleton_iff, mem_singleton_iff, toPretangle_smul, Allowable.toStructPerm_smul,
    Allowable.toStructPerm_comp]

end ConNF
