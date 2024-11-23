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

open Cardinal Ordinal WithBot

namespace ConNF

variable [Params.{u}]

structure Motive (α : Λ) where
  data : ModelData α
  pos : Position (Tangle α)
  typed : TypedNearLitters α

structure Hypothesis {α : Λ} (M : Motive α) (N : (β : Λ) → (β : TypeIndex) < α → Motive β) where
  allPermSderiv {β : Λ} (h : (β : TypeIndex) < α) : M.data.AllPerm → (N β h).data.AllPerm
  allPermBotSderiv : M.data.AllPerm → botModelData.AllPerm
  singleton {β : Λ} (h : (β : TypeIndex) < α) : (N β h).data.TSet → M.data.TSet

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

variable {α : Λ} (M : (β : Λ) → (β : TypeIndex) < α → Motive β)

def ltData :
    letI : Level := ⟨α⟩; LtData :=
  letI : Level := ⟨α⟩
  letI data : (β : TypeIndex) → [LtLevel β] → ModelData β :=
    λ β hβ ↦ β.recBotCoe (λ _ ↦ botModelData)
      (λ β hβ ↦ (M β hβ.elim).data) hβ
  letI positions : (β : TypeIndex) → [LtLevel β] → Position (Tangle β) :=
    λ β hβ ↦ β.recBotCoe (λ _ ↦ botPosition)
      (λ β hβ ↦ (M β hβ.elim).pos) hβ
  letI typedNearLitters : (β : Λ) → [LtLevel β] → TypedNearLitters β :=
    λ β hβ ↦ (M β hβ.elim).typed
  LtData.mk (data := data) (positions := positions) (typedNearLitters := typedNearLitters)

def newModelData' :
    letI : Level := ⟨α⟩; ModelData α :=
  letI : Level := ⟨α⟩
  letI : LtData := ltData M
  newModelData

def leData :
    letI : Level := ⟨α⟩; LeData :=
  letI : Level := ⟨α⟩
  letI data : (β : TypeIndex) → [LeLevel β] → ModelData β :=
    λ β hβ ↦ β.recBotCoe (λ _ ↦ botModelData)
      (λ β hβ ↦ if h : β = α then
          cast (by rw [h]) (newModelData' M)
        else
          (M β (LeLevel.elim.lt_of_ne (coe_injective.ne h))).data) hβ
  letI positions : (β : TypeIndex) → [LtLevel β] → Position (Tangle β) :=
    λ β hβ ↦ β.recBotCoe (λ _ ↦ botPosition)
      (λ β hβ ↦
        cast (by
          congr; unfold data; rw [recBotCoe_coe, dif_neg];
          exact (LtLevel.elim (β := β)).ne ∘ congrArg WithBot.some)
        (M β LtLevel.elim).pos) hβ
  LeData.mk (data := data) (positions := positions)

theorem leData_data_bot :
    (leData M).data ⊥ = botModelData :=
  rfl

theorem leData_data_lt {β : Λ} (hβ : (β : TypeIndex) < α) :
    (letI : Level := ⟨α⟩; letI : LeLevel β := ⟨hβ.le⟩; (leData M).data β) = (M β hβ).data := by
  simp only [leData, recBotCoe_coe, dif_neg (hβ.ne ∘ congrArg WithBot.some)]

theorem leData_data_eq :
    (letI : Level := ⟨α⟩; letI : LeLevel α := ⟨le_rfl⟩; (leData M).data α) = newModelData' M := by
  simp only [leData, recBotCoe_coe, dif_pos trivial, cast_eq]

abbrev TSetLe (β : TypeIndex) (hβ : β ≤ α) : Type _ :=
    letI : Level := ⟨α⟩; letI := leData M; letI : LeLevel β := ⟨hβ⟩
    TSet β

abbrev AllPermLe (β : TypeIndex) (hβ : β ≤ α) : Type _ :=
    letI : Level := ⟨α⟩; letI := leData M; letI : LeLevel β := ⟨hβ⟩
    AllPerm β

abbrev TangleLe (β : TypeIndex) (hβ : β ≤ α) : Type _ :=
    letI : Level := ⟨α⟩; letI := leData M; letI : LeLevel β := ⟨hβ⟩
    Tangle β

def castTSetLeBot :
    TSetLe M ⊥ bot_le ≃ (letI := botModelData; TSet ⊥) :=
  Equiv.refl _

def castTSetLeLt {β : Λ} (hβ : (β : TypeIndex) < α) :
    TSetLe M β hβ.le ≃ (M β hβ).data.TSet :=
  Equiv.cast (by rw [TSetLe]; congr; exact leData_data_lt M hβ)

def castTSetLeEq {β : Λ} (hβ : (β : TypeIndex) = α) :
    TSetLe M β hβ.le ≃ (newModelData' M).TSet :=
  Equiv.cast (by cases hβ; rw [TSetLe]; congr; exact leData_data_eq M)

def castAllPermLeBot :
    AllPermLe M ⊥ bot_le ≃ (letI := botModelData; AllPerm ⊥) :=
  Equiv.refl _

def castAllPermLeLt {β : Λ} (hβ : (β : TypeIndex) < α) :
    AllPermLe M β hβ.le ≃ (M β hβ).data.AllPerm :=
  Equiv.cast (by rw [AllPermLe]; congr; exact leData_data_lt M hβ)

def castAllPermLeEq {β : Λ} (hβ : (β : TypeIndex) = α) :
    AllPermLe M β hβ.le ≃ (newModelData' M).AllPerm :=
  Equiv.cast (by cases hβ; rw [AllPermLe]; congr; exact leData_data_eq M)

def castTangleLeBot :
    TangleLe M ⊥ bot_le ≃ (letI := botModelData; Tangle ⊥) :=
  Equiv.refl _

def castTangleLeLt {β : Λ} (hβ : (β : TypeIndex) < α) :
    TangleLe M β hβ.le ≃ (letI := (M β hβ).data; Tangle β) :=
  Equiv.cast (by rw [TangleLe]; congr; exact leData_data_lt M hβ)

def castTangleLeEq {β : Λ} (hβ : (β : TypeIndex) = α) :
    TangleLe M β hβ.le ≃ (letI := newModelData' M; Tangle α) :=
  Equiv.cast (by cases hβ; rw [TangleLe]; congr; exact leData_data_eq M)

variable (H : (β : Λ) → (h : (β : TypeIndex) < α) → Hypothesis (M β h) λ γ h' ↦ M γ (h'.trans h))

def preCoherentData :
    letI : Level := ⟨α⟩; PreCoherentData :=
  letI : Level := ⟨α⟩
  letI := leData M
  {
    allPermSderiv := λ {β γ} _ _ hγ ρ ↦
      β.recBotCoe (C := λ β ↦ [LeLevel β] → γ < β → AllPerm β → AllPerm γ)
        (λ hγ ↦ (WithBot.not_lt_bot γ hγ).elim)
        (λ β _ hγ ρ ↦
          letI : LtLevel γ := ⟨hγ.trans_le LeLevel.elim⟩
          if h : (β : TypeIndex) = α then
            letI := ltData M
            γ.recBotCoe (C := λ γ ↦ [LtLevel γ] →
                ((ltData M).data γ).AllPerm → AllPermLe M γ LtLevel.elim.le)
              id (λ _γ _ ρ ↦ (castAllPermLeLt M _).symm ρ)
              ((castAllPermLeEq M h ρ).sderiv γ)
          else
            γ.recBotCoe (C := λ γ ↦ [LtLevel γ] → γ < β →
                ((leData M).data β).AllPerm → AllPermLe M γ LtLevel.elim.le)
              (λ _ ρ ↦ (H β (LeLevel.elim.lt_of_ne h)).allPermBotSderiv (castAllPermLeLt M _ ρ))
              (λ _γ _ hγ ρ ↦ (castAllPermLeLt M _).symm <|
                (H β (LeLevel.elim.lt_of_ne h)).allPermSderiv hγ (castAllPermLeLt M _ ρ))
              hγ ρ)
        hγ ρ
    singleton := λ {β γ} _ _ hγ x ↦
      letI : LtLevel γ := ⟨hγ.trans_le LeLevel.elim⟩
      if h : (β : TypeIndex) = α then
        letI := ltData M
        (castTSetLeEq M h).symm (Option.some (newSingleton (castTSetLeLt M _ x)))
      else
        (castTSetLeLt M _).symm ((H β (LeLevel.elim.lt_of_ne h)).singleton hγ (castTSetLeLt M _ x))
  }

def coherentData :
    letI : Level := ⟨α⟩; CoherentData :=
  letI : Level := ⟨α⟩
  letI := preCoherentData M H
  {
    allPermSderiv_forget := sorry
    pos_atom_lt_pos := sorry
    pos_nearLitter_lt_pos := sorry
    smul_fuzz := sorry
    allPerm_of_basePerm := sorry
    allPerm_of_smulFuzz := sorry
    tSet_ext := sorry
    typedMem_singleton_iff := sorry
  }

def constructMotive (α : Λ) (M : (β : Λ) → (β : TypeIndex) < α → Motive β)
    (H : (β : Λ) → (h : (β : TypeIndex) < α) → Hypothesis (M β h) λ γ h' ↦ M γ (h'.trans h)) :
    Motive α :=
  letI : Level := ⟨α⟩
  letI : LtData := ltData M
  letI := newModelData
  {
    data := newModelData,
    pos := newPosition sorry,
    typed := newTypedNearLitters sorry
  }

def constructHypothesis (α : Λ) (M : (β : Λ) → (β : TypeIndex) < α → Motive β)
    (H : (β : Λ) → (h : (β : TypeIndex) < α) → Hypothesis (M β h) λ γ h' ↦ M γ (h'.trans h)) :
    Hypothesis (constructMotive α M H) M :=
  sorry

instance : IsTrans Λ λ β γ ↦ (β : TypeIndex) < (γ : TypeIndex) :=
  ⟨λ _ _ _ ↦ lt_trans⟩

instance : IsWellFounded Λ λ β γ ↦ (β : TypeIndex) < (γ : TypeIndex) :=
  ⟨InvImage.wf _ (wellFounded_lt)⟩

def motive : (α : Λ) → Motive α :=
  ICT.fix constructMotive constructHypothesis

def hypothesis : (α : Λ) → Hypothesis (motive α) (λ β _ ↦ motive β) :=
  ICT.fix_prop constructMotive constructHypothesis

theorem motive_eq : (α : Λ) →
    motive α = constructMotive α (λ β _ ↦ motive β) (λ β _ ↦ hypothesis β) :=
  ICT.fix_eq constructMotive constructHypothesis

end ConNF
