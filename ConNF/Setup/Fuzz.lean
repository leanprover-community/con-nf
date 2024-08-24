import ConNF.Setup.BasePositions
import ConNF.Setup.ModelData

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

end fuzz

class TypedNearLitters {α : Λ} [ModelData α] [Position (Tangle α)] where
  typed : NearLitter → TSet α
  typed_injective : Function.Injective typed
  pos_le_pos_of_typed (N : NearLitter) (t : Tangle α) : t.set = typed N → pos N ≤ pos t

end ConNF
