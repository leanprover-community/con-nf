import ConNF.Structural.StructSet
import ConNF.FOA.Basic.Reduction

/-!
# Hypotheses
-/

open MulAction Quiver Set Sum WithBot

open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions]

class CountingAssumptions extends FOAAssumptions where
  /-- Tangles contain only tangles. -/
  eq_toStructSet_of_mem (β : Λ) [LeLevel β] (γ : Λ) [LeLevel γ]
    (h : (γ : TypeIndex) < β) (t₁ : TSet β) (t₂ : StructSet γ) :
    t₂ ∈ StructSet.ofCoe (toStructSet t₁) γ h → ∃ t₂' : TSet γ, t₂ = toStructSet t₂'
  /-- Tangles are extensional at every proper level `γ < β`. -/
  toStructSet_ext (β γ : Λ) [LeLevel β] [LeLevel γ] (h : (γ : TypeIndex) < β) (t₁ t₂ : TSet β) :
    (∀ t : StructSet γ,
      t ∈ StructSet.ofCoe (toStructSet t₁) γ h ↔ t ∈ StructSet.ofCoe (toStructSet t₂) γ h) →
    toStructSet t₁ = toStructSet t₂
  /-- Any `γ`-tangle can be treated as a singleton at level `β` if `γ < β`. -/
  singleton (β : Λ) [LeLevel β] (γ : Λ) [LeLevel γ]
    (h : (γ : TypeIndex) < β) (t : TSet γ) : TSet β
  singleton_toStructSet (β : Λ) [LeLevel β] (γ : Λ) [LeLevel γ]
    (h : (γ : TypeIndex) < β) (t : TSet γ) :
    StructSet.ofCoe (toStructSet (singleton β γ h t)) γ h = {toStructSet t}

export CountingAssumptions (eq_toStructSet_of_mem toStructSet_ext
  singleton singleton_toStructSet)

variable [CountingAssumptions] {β γ : Λ} [LeLevel β] [LeLevel γ] (hγ : γ < β)

theorem singleton_smul (β γ : Λ) [LeLevel β] [LeLevel γ] (h : (γ : TypeIndex) < β) (t : TSet γ)
    (ρ : Allowable β) :
    ρ • singleton β γ h t = singleton β γ h (Allowable.comp (Hom.toPath h) ρ • t) := by
  refine toStructSet.inj' ?_
  refine toStructSet_ext β γ h _ _ ?_
  intro u
  rw [toStructSet_smul, Allowable.toStructPerm_smul, StructPerm.ofCoe_smul,
    singleton_toStructSet, singleton_toStructSet, smul_set_singleton,
    mem_singleton_iff, mem_singleton_iff, toStructSet_smul, Allowable.toStructPerm_smul,
    Allowable.toStructPerm_comp]

theorem singleton_injective (β γ : Λ) [LeLevel β] [LeLevel γ] (h : (γ : TypeIndex) < β) :
    Function.Injective (singleton β γ h) := by
  intro t₁ t₂ ht
  have h₁ := singleton_toStructSet β γ h t₁
  have h₂ := singleton_toStructSet β γ h t₂
  rw [ht, h₂, singleton_eq_singleton_iff] at h₁
  exact toStructSet.inj' h₁.symm

end ConNF
