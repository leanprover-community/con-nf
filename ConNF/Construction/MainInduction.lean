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

theorem card_tangle_bot_le [ModelData ⊥] : #(Tangle ⊥) ≤ #μ := by
  apply card_tangle_le_of_card_tSet
  apply (mk_le_of_injective (ModelData.tSetForget_injective' (α := ⊥))).trans
  apply (mk_le_of_injective StrSet.botEquiv.injective).trans
  rw [card_atom]

def botPosition [ModelData ⊥] : Position (Tangle ⊥) where
  pos := ⟨funOfDeny card_tangle_bot_le (λ t ↦ pos '' (t.supportᴬ.image Prod.snd : Set Atom))
      (λ _ ↦ sorry),
    funOfDeny_injective _ _ _⟩

theorem pos_tangle_bot {D : ModelData ⊥} (t : Tangle ⊥) (a : Atom) (A : ⊥ ↝ ⊥)
    (ha : a ∈ (t.support ⇘. A)ᴬ) :
    letI := botPosition
    pos a < pos t := by
  refine funOfDeny_gt_deny _ _ _ _ _ ⟨_, ?_, rfl⟩
  obtain ⟨i, hi⟩ := ha
  exact ⟨i, ⟨A, a⟩, hi, rfl⟩

structure Hypothesis {α : Λ} (M : Motive α) (N : (β : Λ) → (β : TypeIndex) < α → Motive β) where
  allPermSderiv {β : Λ} (h : (β : TypeIndex) < α) : M.data.AllPerm → (N β h).data.AllPerm
  allPermBotSderiv : M.data.AllPerm → botModelData.AllPerm
  singleton {β : Λ} (h : (β : TypeIndex) < α) : (N β h).data.TSet → M.data.TSet
  allPermSderiv_forget {β : Λ} (h : (β : TypeIndex) < α) (ρ : M.data.AllPerm) :
    (N β h).data.allPermForget (allPermSderiv h ρ) = M.data.allPermForget ρ ↘ h
  allPermBotSderiv_forget (ρ : M.data.AllPerm) :
    botModelData.allPermForget (allPermBotSderiv ρ) = M.data.allPermForget ρ ↘ bot_lt_coe _
  pos_atom_lt_pos :
    letI := M.data; letI := M.pos
    ∀ (t : Tangle α) (A : α ↝ ⊥) (a : Atom), a ∈ (t.support ⇘. A)ᴬ → pos a < pos t
  pos_nearLitter_lt_pos :
    letI := M.data; letI := M.pos
    ∀ (t : Tangle α) (A : α ↝ ⊥) (N : NearLitter), N ∈ (t.support ⇘. A)ᴺ → pos N < pos t
  smul_fuzz {β γ : Λ} (hβ : (β : TypeIndex) < α)
      (hγ : (γ : TypeIndex) < α) (hβγ : (β : TypeIndex) ≠ γ) :
    letI := (N β hβ).data; letI := (N β hβ).pos
    ∀ (ρ : M.data.AllPerm) (t : Tangle β),
    M.data.allPermForget ρ ↘ hγ ↘. • fuzz hβγ t = fuzz hβγ (allPermSderiv hβ ρ • t)
  smul_fuzz_bot {γ : Λ} (hγ : (γ : TypeIndex) < α) :
    letI := botModelData; letI := botPosition
    ∀ (ρ : M.data.AllPerm) (t : Tangle ⊥),
    M.data.allPermForget ρ ↘ hγ ↘. • fuzz (bot_ne_coe (a := γ)) t =
      fuzz (bot_ne_coe (a := γ)) (allPermBotSderiv ρ • t)

def castTSet {α β : TypeIndex} {D₁ : ModelData α} {D₂ : ModelData β}
    (h₁ : α = β) (h₂ : HEq D₁ D₂) :
    D₁.TSet ≃ D₂.TSet := by cases h₁; rw [eq_of_heq h₂]

def castAllPerm {α β : TypeIndex} {D₁ : ModelData α} {D₂ : ModelData β}
    (h₁ : α = β) (h₂ : HEq D₁ D₂) :
    D₁.AllPerm ≃ D₂.AllPerm := by cases h₁; rw [eq_of_heq h₂]

def castTangle {α β : TypeIndex} {D₁ : ModelData α} {D₂ : ModelData β}
    (h₁ : α = β) (h₂ : HEq D₁ D₂) :
    (letI := D₁; Tangle α) ≃ (letI := D₂; Tangle β) := by cases h₁; rw [eq_of_heq h₂]

theorem castAllPerm_forget {α : TypeIndex} {D₁ D₂ : ModelData α} (h₂ : HEq D₁ D₂) (ρ : D₁.AllPerm) :
    D₂.allPermForget (castAllPerm rfl h₂ ρ) = D₁.allPermForget ρ := by cases h₂; rfl

theorem castTangle_support {α : TypeIndex} {D₁ D₂ : ModelData α} (h₂ : HEq D₁ D₂)
    (t : letI := D₁; Tangle α) :
    (castTangle rfl h₂ t).support = letI := D₁; t.support := by cases h₂; rfl

theorem castAllPerm_smul {α : TypeIndex} {D₁ D₂ : ModelData α} (h₂ : HEq D₁ D₂)
    (ρ : D₂.AllPerm) (t : letI := D₁; Tangle α) :
    ρ • (castTangle rfl h₂ t) = letI := D₁; castTangle rfl h₂ ((castAllPerm rfl h₂).symm ρ • t) :=
  by cases h₂; rfl

theorem castTangle_pos {α β : TypeIndex} {D₁ : ModelData α} {D₂ : ModelData β}
    {E₁ : Position (Tangle α)} {E₂ : Position (Tangle β)}
    (h₁ : α = β) (h₂ : HEq D₁ D₂) (h₃ : HEq E₁ E₂) (t : Tangle α) :
    pos (castTangle h₁ h₂ t) = pos t := by cases h₁; cases h₂; cases h₃; rfl

theorem castTangle_fuzz {α : TypeIndex} {D₁ D₂ : ModelData α}
    {E₁ : letI := D₁; Position (Tangle α)} {E₂ : letI := D₂; Position (Tangle α)}
    (h₂ : HEq D₁ D₂) (h₃ : HEq E₁ E₂) (t : letI := D₁; Tangle α) {β : Λ} (hαβ : α ≠ β) :
    (letI := D₂; fuzz hαβ (castTangle rfl h₂ t)) = (letI := D₁; fuzz hαβ t) :=
  by cases h₂; cases h₃; rfl

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
  castTSet rfl (heq_of_eq <| leData_data_lt M hβ)

def castTSetLeEq {β : Λ} (hβ : (β : TypeIndex) = α) :
    TSetLe M β hβ.le ≃ (newModelData' M).TSet :=
  castTSet hβ (by cases hβ; exact heq_of_eq <| leData_data_eq M)

def castAllPermLeBot :
    AllPermLe M ⊥ bot_le ≃ (letI := botModelData; AllPerm ⊥) :=
  Equiv.refl _

def castAllPermLeLt {β : Λ} (hβ : (β : TypeIndex) < α) :
    AllPermLe M β hβ.le ≃ (M β hβ).data.AllPerm :=
  castAllPerm rfl (heq_of_eq <| leData_data_lt M hβ)

def castAllPermLeEq {β : Λ} (hβ : (β : TypeIndex) = α) :
    AllPermLe M β hβ.le ≃ (newModelData' M).AllPerm :=
  castAllPerm hβ (by cases hβ; exact heq_of_eq <| leData_data_eq M)

def castTangleLeBot :
    TangleLe M ⊥ bot_le ≃ (letI := botModelData; Tangle ⊥) :=
  Equiv.refl _

def castTangleLeLt {β : Λ} (hβ : (β : TypeIndex) < α) :
    TangleLe M β hβ.le ≃ (letI := (M β hβ).data; Tangle β) :=
  castTangle rfl (heq_of_eq <| leData_data_lt M hβ)

def castTangleLeEq {β : Λ} (hβ : (β : TypeIndex) = α) :
    TangleLe M β hβ.le ≃ (letI := newModelData' M; Tangle α) :=
  castTangle hβ (by cases hβ; exact heq_of_eq <| leData_data_eq M)

theorem castAllPermLeLt_forget {β : Λ} (hβ : (β : TypeIndex) < α) (ρ : AllPermLe M β hβ.le) :
    (M β hβ).data.allPermForget (castAllPermLeLt M hβ ρ) =
    letI : Level := ⟨α⟩; letI : LeLevel β := ⟨hβ.le⟩; ((leData M).data β).allPermForget ρ :=
  castAllPerm_forget _ _

theorem castAllPermLeEq_forget (ρ : AllPermLe M α le_rfl) :
    (newModelData' M).allPermForget (castAllPermLeEq M rfl ρ) =
    letI : Level := ⟨α⟩; letI : LeLevel α := ⟨le_rfl⟩; ((leData M).data α).allPermForget ρ :=
  castAllPerm_forget _ _

theorem castTangleLeLt_support {β : Λ} (hβ : (β : TypeIndex) < α) (t : TangleLe M β hβ.le) :
    (letI := (M β hβ).data; (castTangleLeLt M hβ t).support) =
    letI : Level := ⟨α⟩; letI : LeLevel β := ⟨hβ.le⟩; letI := (leData M).data β; t.support :=
  castTangle_support _ _

theorem castAllPermLeLt_smul {β : Λ} (hβ : (β : TypeIndex) < α)
    (ρ : (M β hβ).data.AllPerm) (t : TangleLe M β hβ.le) :
    ρ • castTangleLeLt M hβ t = castTangleLeLt M hβ (((castAllPermLeLt M hβ).symm ρ) • t) :=
  castAllPerm_smul _ _ _

theorem castAllPermLeLt_smul' {β : Λ} (hβ : (β : TypeIndex) < α)
    (ρ : AllPermLe M β hβ.le) (t : TangleLe M β hβ.le) :
    castTangleLeLt M hβ (ρ • t) = castAllPermLeLt M hβ ρ • castTangleLeLt M hβ t := by
  rw [castAllPermLeLt_smul, Equiv.symm_apply_apply]

theorem castTangleLeLt_pos {β : Λ} (hβ : (β : TypeIndex) < α) (t : TangleLe M β hβ.le) :
    (M β hβ).pos.pos (castTangleLeLt M hβ t) =
    letI : Level := ⟨α⟩; letI : LtLevel β := ⟨hβ⟩; ((leData M).positions β).pos t := by
  apply castTangle_pos
  unfold LeData.positions leData
  simp only [recBotCoe_coe, cast_heq]

theorem castTangleLeLt_fuzz {β : Λ} (hβ : (β : TypeIndex) < α) (t : TangleLe M β hβ.le)
    {γ : Λ} (hβγ : (β : TypeIndex) ≠ γ) :
    (letI := (M β hβ).data; letI := (M β hβ).pos; fuzz hβγ (castTangleLeLt M hβ t)) =
    letI : Level := ⟨α⟩; letI : LtLevel β := ⟨hβ⟩; letI := (leData M).data β; fuzz hβγ t := by
  apply castTangle_fuzz
  unfold instPositionTangle leData
  simp only [recBotCoe_coe, cast_heq]

variable (H : (β : Λ) → (h : (β : TypeIndex) < α) → Hypothesis (M β h) λ γ h' ↦ M γ (h'.trans h))

def preCoherentData :
    letI : Level := ⟨α⟩; PreCoherentData :=
  letI : Level := ⟨α⟩
  letI := leData M
  {
    allPermSderiv := λ {β γ} _ _ hγ ρ ↦
      β.recBotCoe (C := λ β ↦ [LeLevel β] → γ < β → AllPerm β → AllPerm γ)
        (λ hγ ↦ (not_lt_bot hγ).elim)
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

theorem preCoherentData_allPermSderiv_forget {β γ : TypeIndex}
    [iβ : letI : Level := ⟨α⟩; LeLevel β] [iγ : letI : Level := ⟨α⟩; LeLevel γ]
    (hγ : γ < β) (ρ : AllPermLe M β iβ.elim) :
    ((leData M).data γ).allPermForget ((preCoherentData M H).allPermSderiv hγ ρ) =
    ((leData M).data β).allPermForget ρ ↘ hγ := by
  letI : Level := ⟨α⟩
  letI : LtData := ltData M
  unfold PreCoherentData.allPermSderiv preCoherentData
  dsimp only
  revert iβ iγ
  induction β using recBotCoe with
  | bot => cases not_lt_bot hγ
  | coe β =>
    dsimp only [recBotCoe_coe]
    split_ifs with h
    · cases coe_injective h
      revert γ; intro γ; induction γ using recBotCoe with
      | bot =>
        intro _ hγ ρ
        rw [← castAllPermLeEq_forget]
        exact (NewPerm.forget_sderiv ((castAllPermLeEq M h) ρ) ⊥).symm
      | coe γ =>
        intro _ hγ ρ
        haveI : LtLevel γ := ⟨hγ⟩
        rw [← castAllPermLeEq_forget, ← castAllPermLeLt_forget M hγ]
        simp only [recBotCoe_coe, Equiv.apply_symm_apply]
        exact (NewPerm.forget_sderiv ((castAllPermLeEq M h) ρ) γ).symm
    · revert γ; intro γ; induction γ using recBotCoe with
      | bot =>
        intro hγ _ ρ
        rw [← castAllPermLeLt_forget M (LeLevel.elim.lt_of_ne h)]
        apply (H β _).allPermBotSderiv_forget
      | coe γ =>
        intro hγ _ ρ
        rw [← castAllPermLeLt_forget M (LeLevel.elim.lt_of_ne h),
          ← castAllPermLeLt_forget M (hγ.trans_le LeLevel.elim)]
        simp only [recBotCoe_coe, Equiv.apply_symm_apply]
        apply (H β _).allPermSderiv_forget

theorem preCoherentData_pos_atom_lt_pos
    (H : (β : Λ) → (h : (β : TypeIndex) < α) → Hypothesis (M β h) λ γ h' ↦ M γ (h'.trans h))
    {β : TypeIndex} [iβ : letI : Level := ⟨α⟩; LtLevel β] (t : TangleLe M β iβ.elim.le)
    (A : β ↝ ⊥) (a : Atom) (ha : a ∈ (letI := (leData M).data β; Tangle.support t ⇘. A)ᴬ) :
    pos a < ((leData M).positions β).pos t := by
  letI : Level := ⟨α⟩
  revert iβ
  induction β using recBotCoe with
  | bot =>
    intro _ t ha
    exact (pos_tangle_bot t a A ha)
  | coe β =>
    intro _ t ha
    rw [← castTangleLeLt_pos M LtLevel.elim]
    apply (H β _).pos_atom_lt_pos (castTangleLeLt M LtLevel.elim t) A a
    rwa [castTangleLeLt_support]

theorem preCoherentData_pos_nearLitter_lt_pos
    (H : (β : Λ) → (h : (β : TypeIndex) < α) → Hypothesis (M β h) λ γ h' ↦ M γ (h'.trans h))
    {β : TypeIndex} [iβ : letI : Level := ⟨α⟩; LtLevel β] (t : TangleLe M β iβ.elim.le)
    (A : β ↝ ⊥) (N : NearLitter) (hN : N ∈ (letI := (leData M).data β; Tangle.support t ⇘. A)ᴺ) :
    pos N < ((leData M).positions β).pos t := by
  letI : Level := ⟨α⟩
  revert iβ
  induction β using recBotCoe with
  | bot =>
    rintro _ t ⟨i, ha⟩
    letI := botModelData
    change t.supportᴺ.rel i ⟨A, N⟩ at ha
    rw [t.support_supports.nearLitters_eq_empty_of_bot rfl] at ha
    cases ha
  | coe β =>
    intro _ t ha
    rw [← castTangleLeLt_pos M LtLevel.elim]
    apply (H β _).pos_nearLitter_lt_pos (castTangleLeLt M LtLevel.elim t) A N
    rwa [castTangleLeLt_support]

theorem preCoherentData_smul_fuzz
    {β : Λ} {γ : TypeIndex} {δ : Λ} [iβ : letI : Level := ⟨α⟩; LeLevel β]
    [iγ : letI : Level := ⟨α⟩; LtLevel γ] [iδ : letI : Level := ⟨α⟩; LtLevel δ]
    (hγ : γ < β) (hδ : (δ : TypeIndex) < β) (hγδ : γ ≠ δ)
    (ρ : AllPermLe M β iβ.elim) (t : TangleLe M γ iγ.elim.le) :
    letI : Level := ⟨α⟩; letI := preCoherentData M H
    ((leData M).data β).allPermForget ρ ↘ hδ ↘. • fuzz hγδ t =
    fuzz hγδ ((preCoherentData M H).allPermSderiv hγ ρ • t) := by
  letI : Level := ⟨α⟩
  by_cases h : (β : TypeIndex) = α
  · cases coe_injective h
    revert iγ
    induction γ using recBotCoe with
    | bot =>
      intro _ t
      rw [← castAllPermLeEq_forget]
      unfold PreCoherentData.allPermSderiv preCoherentData
      simp only [recBotCoe_bot, recBotCoe_coe, ↓reduceDIte, id_eq]
      letI := ltData M
      exact (castAllPermLeEq M rfl ρ).smul_fuzz hγδ t
    | coe γ =>
      intro _ t
      rw [← castTangleLeLt_fuzz M hγ, ← castTangleLeLt_fuzz M hγ, ← castAllPermLeEq_forget]
      unfold PreCoherentData.allPermSderiv preCoherentData
      simp only [recBotCoe_coe, ↓reduceDIte]
      letI := ltData M
      have := (castAllPermLeEq M rfl ρ).smul_fuzz hγδ (castTangleLeLt M hγ t)
      rwa [castAllPermLeLt_smul] at this
  · revert iγ
    induction γ using recBotCoe with
    | bot =>
      intro _ t
      rw [← castAllPermLeLt_forget M (iβ.elim.lt_of_ne h)]
      unfold PreCoherentData.allPermSderiv preCoherentData
      simp only [coe_inj, recBotCoe_bot, id_eq, recBotCoe_coe, show β ≠ α from h ∘ congr_arg _,
        ↓reduceDIte, ne_eq]
      exact (H β (iβ.elim.lt_of_ne h)).smul_fuzz_bot hδ (castAllPermLeLt M _ ρ) t
    | coe γ =>
      intro _ t
      rw [← castAllPermLeLt_forget M (iβ.elim.lt_of_ne h),
        ← castTangleLeLt_fuzz M (hγ.trans_le LeLevel.elim),
        ← castTangleLeLt_fuzz M (hγ.trans_le LeLevel.elim),
        castAllPermLeLt_smul']
      unfold PreCoherentData.allPermSderiv preCoherentData
      simp only [coe_inj, recBotCoe_coe, imp_self, show β ≠ α from h ∘ congr_arg _,
        IsEmpty.forall_iff, ↓reduceDIte, ne_eq, Equiv.apply_symm_apply]
      exact (H β (iβ.elim.lt_of_ne h)).smul_fuzz hγ hδ hγδ
        (castAllPermLeLt M _ ρ) (castTangleLeLt M _ t)

def coherentData :
    letI : Level := ⟨α⟩; CoherentData :=
  letI : Level := ⟨α⟩
  letI := preCoherentData M H
  {
    allPermSderiv_forget := preCoherentData_allPermSderiv_forget M H
    pos_atom_lt_pos := preCoherentData_pos_atom_lt_pos M H
    pos_nearLitter_lt_pos := preCoherentData_pos_nearLitter_lt_pos M H
    smul_fuzz := preCoherentData_smul_fuzz M H
    allPerm_of_basePerm := sorry
    allPerm_of_smulFuzz := sorry
    tSet_ext := sorry
    typedMem_singleton_iff := sorry
  }

theorem newModelData_card_tangle_le
    (H : (β : Λ) → (h : (β : TypeIndex) < α) → Hypothesis (M β h) λ γ h' ↦ M γ (h'.trans h)) :
    #(letI := newModelData' M; Tangle α) ≤ #μ := by
  rw [← Cardinal.eq.mpr ⟨castTangleLeEq M rfl⟩]
  letI := coherentData M H
  letI : Level := ⟨α⟩
  letI : LeLevel α := ⟨le_rfl⟩
  exact card_tangle_le_of_card_tSet (card_tSet_le α)

def constructMotive (α : Λ) (M : (β : Λ) → (β : TypeIndex) < α → Motive β)
    (H : (β : Λ) → (h : (β : TypeIndex) < α) → Hypothesis (M β h) λ γ h' ↦ M γ (h'.trans h)) :
    Motive α :=
  letI : Level := ⟨α⟩
  letI : LtData := ltData M
  letI := newModelData
  {
    data := newModelData,
    pos := newPosition (newModelData_card_tangle_le M H),
    typed := newTypedNearLitters (newModelData_card_tangle_le M H)
  }

def constructHypothesis (α : Λ) (M : (β : Λ) → (β : TypeIndex) < α → Motive β)
    (H : (β : Λ) → (h : (β : TypeIndex) < α) → Hypothesis (M β h) λ γ h' ↦ M γ (h'.trans h)) :
    Hypothesis (constructMotive α M H) M :=
  {
    allPermSderiv := sorry
    allPermBotSderiv := sorry
    singleton := sorry
    allPermSderiv_forget := sorry
    allPermBotSderiv_forget := sorry
    pos_atom_lt_pos := sorry
    pos_nearLitter_lt_pos := sorry
    smul_fuzz := sorry
    smul_fuzz_bot := sorry
  }

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
