import ConNF.Construction.NewModelData
import ConNF.Basic.InductiveConstruction

/-!
# New file

In this file...

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}]

structure Motive (α : Λ) where
  data : ModelData α
  pos : Position (Tangle α)
  typed : TypedNearLitters α

structure Hypothesis (α : Λ) (M : Motive α) (N : (β : Λ) → β < α → Motive β) where

theorem card_tangle_bot_le [ModelData ⊥] : #(Tangle ⊥) ≤ #μ := by
  apply card_tangle_le_of_card_tSet
  apply (mk_le_of_injective (tSetForget_injective' (α := ⊥))).trans
  apply (mk_le_of_injective StrSet.botEquiv.injective).trans
  rw [card_atom]

def botPosition [ModelData ⊥] : Position (Tangle ⊥) where
  pos := ⟨funOfDeny card_tangle_bot_le (λ t ↦ {pos (StrSet.botEquiv t.setᵁ)})
      (λ _ ↦ (mk_singleton _).trans_lt (one_lt_aleph0.trans aleph0_lt_μ_ord_cof)),
    funOfDeny_injective _ _ _⟩

theorem pos_tangle_bot [ModelData ⊥] (t : Tangle ⊥) :
    letI := botPosition
    pos (StrSet.botEquiv t.setᵁ) < pos t :=
  funOfDeny_gt_deny _ _ _ _ _ rfl

def ltData
    (α : Λ) (M : (β : Λ) → β < α → Motive β) :
    letI : Level := ⟨α⟩; LtData :=
  letI : Level := ⟨α⟩
  letI data : (β : TypeIndex) → [LtLevel β] → ModelData β :=
    λ β hβ ↦ β.recBotCoe (λ _ ↦ botModelData)
      (λ β hβ ↦ (M β (WithBot.coe_lt_coe.mp hβ.elim)).data) hβ
  letI positions : (β : TypeIndex) → [LtLevel β] → Position (Tangle β) :=
    λ β hβ ↦ β.recBotCoe (λ _ ↦ botPosition)
      (λ β hβ ↦ (M β (WithBot.coe_lt_coe.mp hβ.elim)).pos) hβ
  letI typedNearLitters : (β : Λ) → [LtLevel β] → TypedNearLitters β :=
    λ β hβ ↦ (M β (WithBot.coe_lt_coe.mp hβ.elim)).typed
  LtData.mk (data := data) (positions := positions) (typedNearLitters := typedNearLitters)

def constructMotive (α : Λ) (M : (β : Λ) → β < α → Motive β)
    (H : (β : Λ) → (h : β < α) → Hypothesis β (M β h) fun γ h' ↦ M γ (h'.trans h)) :
    Motive α :=
  letI : Level := ⟨α⟩
  letI : LtData := ltData α M
  ⟨newModelData, sorry, sorry⟩

def constructHypothesis (α : Λ) (M : (β : Λ) → β < α → Motive β)
    (H : (β : Λ) → (h : β < α) → Hypothesis β (M β h) fun γ h' ↦ M γ (h'.trans h)) :
    Hypothesis α (constructMotive α M H) M :=
  sorry

def motive : (α : Λ) → Motive α :=
  ICT.fix constructMotive constructHypothesis

def hypothesis : (α : Λ) → Hypothesis α (motive α) (λ β _ ↦ motive β) :=
  ICT.fix_prop constructMotive constructHypothesis

theorem motive_eq : (α : Λ) →
    motive α = constructMotive α (λ β _ ↦ motive β) (λ β _ ↦ hypothesis β) :=
  ICT.fix_eq constructMotive constructHypothesis

end ConNF
