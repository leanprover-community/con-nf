import ConNF.Levels.BasePositions
import ConNF.Coherent.ModelData

/-!
# The `fuzz` map

In this file, we define the `fuzz` map.

## Main declarations

* `ConNF.fuzz`: The `fuzz` map.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}]

section fuzz

variable {β : TypeIndex} [ModelData β] [Position (Tangle β)] {γ : Λ}

def fuzz (hβγ : β ≠ γ) : Tangle β → Litter :=
  (⟨·, β, γ, hβγ⟩) ∘ funOfDeny card_le_of_position (λ t ↦ {pos t})
    (λ _ ↦ (mk_singleton _).trans_lt (one_lt_aleph0.trans aleph0_lt_μ_ord_cof))

theorem fuzz_β_eq {β' : TypeIndex} [ModelData β'] [Position (Tangle β')] {γ' : Λ}
    {hβγ : β ≠ γ} {hβγ' : β' ≠ γ'} {t : Tangle β} {t' : Tangle β'}
    (h : fuzz hβγ t = fuzz hβγ' t') :
    β = β' :=
  congr_arg Litter.β h

theorem fuzz_γ_eq {β' : TypeIndex} [ModelData β'] [Position (Tangle β')] {γ' : Λ}
    {hβγ : β ≠ γ} {hβγ' : β' ≠ γ'} {t : Tangle β} {t' : Tangle β'}
    (h : fuzz hβγ t = fuzz hβγ' t') :
    γ = γ' :=
  congr_arg Litter.γ h

theorem fuzz_injective {hβγ : β ≠ γ} {t₁ t₂ : Tangle β} (h : fuzz hβγ t₁ = fuzz hβγ t₂) :
    t₁ = t₂ := by
  refine Function.Injective.comp ?_ (funOfDeny_injective _ _ _) h
  intro ν₁ ν₂ h
  cases h
  rfl

theorem fuzz_ν (hβγ : β ≠ γ) (t : Tangle β) :
    pos t < (fuzz hβγ t).ν :=
  funOfDeny_gt_deny _ _ _ t _ rfl

theorem pos_fuzz (hβγ : β ≠ γ) (t : Tangle β) :
    pos t < pos (fuzz hβγ t) :=
  (fuzz_ν hβγ t).trans (fuzz hβγ t).lt_pos

end fuzz

end ConNF
