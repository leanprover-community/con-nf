import ConNF.Basic.InductiveConstruction
import ConNF.Construction.NewModelData
import ConNF.Counting.Conclusions

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
  allPermSderiv {β : Λ} (h : β < α) : M.data.AllPerm → (N β h).data.AllPerm
  allPermBotSderiv : M.data.AllPerm → botModelData.AllPerm
  singleton {β : Λ} (h : β < α) : (N β h).data.TSet → M.data.TSet

theorem card_tangle_bot_le [ModelData ⊥] : #(Tangle ⊥) ≤ #μ := by
  apply card_tangle_le_of_card_tSet
  apply (mk_le_of_injective (ModelData.tSetForget_injective' (α := ⊥))).trans
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

def ltData (α : Λ) (M : (β : Λ) → β < α → Motive β) :
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

def newModelData' (α : Λ) (M : (β : Λ) → β < α → Motive β) :
    letI : Level := ⟨α⟩; ModelData α :=
  letI : Level := ⟨α⟩
  letI : LtData := ltData α M
  newModelData

def castData (α : Λ) (M : (β : Λ) → β < α → Motive β)
    (β : TypeIndex) [letI : Level := ⟨α⟩; LeLevel β] : ModelData β :=
  if h : β = α then
    cast (by simp_rw [h]) (newModelData' α M)
  else
    letI : Level := ⟨α⟩
    haveI : LtLevel β := ⟨LeLevel.elim.lt_of_ne h⟩
    (ltData α M).data β

theorem castData_eq_of_eq (α : Λ) (M : (β : Λ) → β < α → Motive β) :
    letI : Level := ⟨α⟩
    letI : LeLevel α := ⟨le_rfl⟩
    castData α M α = newModelData' α M := by
  letI : Level := ⟨α⟩
  rw [castData, dif_pos rfl]
  rfl

theorem castData_eq_of_lt (α : Λ) (M : (β : Λ) → β < α → Motive β)
    (β : TypeIndex) [letI : Level := ⟨α⟩; LtLevel β] :
    letI : Level := ⟨α⟩
    castData α M β = (ltData α M).data β := by
  letI : Level := ⟨α⟩
  rw [castData, dif_neg]
  rintro rfl
  exact LtLevel.elim.ne rfl

def liftCastDataLt (α : Λ) (M : (β : Λ) → β < α → Motive β)
    {D : (β : TypeIndex) → ModelData β → Type _}
    (f : letI : Level := ⟨α⟩; (β : TypeIndex) → [LtLevel β] → D β ((ltData α M).data β))
    (β : TypeIndex) [letI : Level := ⟨α⟩; LtLevel β] : D β (castData α M β) :=
  cast (by rw [castData_eq_of_lt]) (f β)

def liftCastDataLe (α : Λ) (M : (β : Λ) → β < α → Motive β)
    {D : (β : TypeIndex) → ModelData β → Type _} (β : TypeIndex)
    (fβ : letI : Level := ⟨α⟩; [LtLevel β] → D β ((ltData α M).data β))
    (fα : D α (newModelData' α M))
    [letI : Level := ⟨α⟩; LeLevel β] : D β (castData α M β) :=
  if h : β = α then
    cast (by cases h; rw [castData_eq_of_eq]) fα
  else
    letI : Level := ⟨α⟩
    haveI : LtLevel β := ⟨LeLevel.elim.lt_of_ne h⟩
    cast (by rw [castData_eq_of_lt]) (fβ)

def leData (α : Λ) (M : (β : Λ) → β < α → Motive β) :
    letI : Level := ⟨α⟩; LeData :=
  letI : Level := ⟨α⟩
  letI data : (β : TypeIndex) → [LeLevel β] → ModelData β := castData α M
  letI positions : (β : TypeIndex) → [LtLevel β] → Position (Tangle β) :=
    liftCastDataLt α M
      (D := λ β (x : ModelData β) ↦ Position (@Tangle _ β x)) (ltData α M).positions
  LeData.mk (data := data) (positions := positions)

def preCoherentData (α : Λ) (M : (β : Λ) → β < α → Motive β)
    (H : (β : Λ) → (h : β < α) → Hypothesis β (M β h) λ γ h' ↦ M γ (h'.trans h)) :
    letI : Level := ⟨α⟩; PreCoherentData :=
  letI : Level := ⟨α⟩
  letI := leData α M
  {
    allPermSderiv := λ {β γ} _ _ hγ ρ ↦
      -- Case split on `γ = α`.
      liftCastDataLe α M (D := λ γ Mγ ↦ γ < β → Mγ.AllPerm) γ
        -- Case split on `β = α`.
        (λ hγ ↦ liftCastDataLe α M
          (D := λ _β Mβ ↦ Mβ.AllPerm → ((ltData α M).data γ).AllPerm) β
          ( -- Case split on `β = ⊥`.
            β.recBotCoe (C := λ β ↦ [LtLevel β] → γ < β →
              ((ltData α M).data β).AllPerm → ((ltData α M).data γ).AllPerm)
            (λ h ↦ (not_lt_bot h).elim)
            (λ β _ ↦ -- Case split on `γ = ⊥`.
              γ.recBotCoe (C := λ γ ↦ [LtLevel γ] → γ < β →
                ((ltData α M).data β).AllPerm → ((ltData α M).data γ).AllPerm)
              (λ _ ↦ (H β (WithBot.coe_lt_coe.mp LtLevel.elim)).allPermBotSderiv)
              (λ _γ _ hγ ↦ (H β (WithBot.coe_lt_coe.mp LtLevel.elim)).allPermSderiv
                  (WithBot.coe_lt_coe.mp hγ)))
            hγ)
          (λ ρ ↦ letI : LtData := ltData α M; ρ.sderiv γ)
          ρ)
        (λ h' ↦ (LeLevel.elim.not_lt h').elim) hγ
    singleton := λ {β γ} _ _ hγ x ↦
      -- Case split on `γ = α`.
      liftCastDataLe α M (D := λ γ Mγ ↦ γ < β → Mγ.TSet → TSet β) γ
      (λ _hγ ↦
        -- Case split on `β = α`.
        liftCastDataLe α M
          (D := λ _β Mβ ↦ ((ltData α M).data γ).TSet → Mβ.TSet) β
          ((H β (WithBot.coe_lt_coe.mp LtLevel.elim)).singleton (WithBot.coe_lt_coe.mp hγ))
          (λ x ↦ letI : LtData := ltData α M; some (newSingleton x)))
      (λ h' ↦ (LeLevel.elim.not_lt h').elim) hγ x
  }

def coherentData
    (α : Λ) (M : (β : Λ) → β < α → Motive β)
    (H : (β : Λ) → (h : β < α) → Hypothesis β (M β h) λ γ h' ↦ M γ (h'.trans h)) :
    letI : Level := ⟨α⟩; CoherentData :=
  letI : Level := ⟨α⟩
  letI := preCoherentData α M H
  ⟨sorry, sorry, sorry, sorry, sorry, sorry, sorry, sorry⟩

theorem construct_tangle_le_μ' (α : Λ) (M : (β : Λ) → β < α → Motive β)
    (H : (β : Λ) → (h : β < α) → Hypothesis β (M β h) λ γ h' ↦ M γ (h'.trans h)) :
    letI : Level := ⟨α⟩
    letI : LeLevel α := ⟨le_rfl⟩
    letI := coherentData α M H
    #(Tangle α) ≤ #μ :=
  letI : Level := ⟨α⟩
  letI : LeLevel α := ⟨le_rfl⟩
  letI := coherentData α M H
  card_tangle_le α

theorem construct_tangle_le_μ (α : Λ) (M : (β : Λ) → β < α → Motive β)
    (H : (β : Λ) → (h : β < α) → Hypothesis β (M β h) λ γ h' ↦ M γ (h'.trans h)) :
    letI := newModelData' α M
    #(Tangle α) ≤ #μ :=
  sorry

def constructMotive (α : Λ) (M : (β : Λ) → β < α → Motive β)
    (H : (β : Λ) → (h : β < α) → Hypothesis β (M β h) λ γ h' ↦ M γ (h'.trans h)) :
    Motive α :=
  letI : Level := ⟨α⟩
  letI : LtData := ltData α M
  letI := newModelData
  {
    data := newModelData,
    pos := newPosition (construct_tangle_le_μ α M H),
    typed := newTypedNearLitters (construct_tangle_le_μ α M H)
  }

def constructHypothesis (α : Λ) (M : (β : Λ) → β < α → Motive β)
    (H : (β : Λ) → (h : β < α) → Hypothesis β (M β h) λ γ h' ↦ M γ (h'.trans h)) :
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
