import ConNF.Model.InductionStatement
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

variable [Params.{u}] {α : Λ} (M : (β : Λ) → (β : TypeIndex) < α → Motive β)

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
      (λ β hβ ↦ if h : (β : TypeIndex) = α then
          cast (by rw [h]) (newModelData' M)
        else
          (M β (LeLevel.elim.lt_of_ne h)).data) hβ
  letI positions : (β : TypeIndex) → [LtLevel β] → Position (Tangle β) :=
    λ β hβ ↦ β.recBotCoe (λ _ ↦ botPosition)
      (λ β hβ ↦
        cast (by
          congr; unfold data; rw [recBotCoe_coe, dif_neg];
          exact (LtLevel.elim (β := β)).ne)
        (M β LtLevel.elim).pos) hβ
  LeData.mk (data := data) (positions := positions)

theorem leData_data_bot :
    (leData M).data ⊥ = botModelData :=
  rfl

theorem leData_data_lt {β : Λ} (hβ : (β : TypeIndex) < α) :
    (letI : Level := ⟨α⟩; letI : LeLevel β := ⟨hβ.le⟩; (leData M).data β) = (M β hβ).data := by
  simp only [leData, recBotCoe_coe, dif_neg hβ.ne]

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

def castTSetLeLt {β : Λ} (hβ : (β : TypeIndex) < α) :
    TSetLe M β hβ.le ≃ (M β hβ).data.TSet :=
  castTSet rfl (heq_of_eq <| leData_data_lt M hβ)

def castTSetLeEq {β : Λ} (hβ : (β : TypeIndex) = α) :
    TSetLe M β hβ.le ≃ (newModelData' M).TSet :=
  castTSet hβ (by cases hβ; exact heq_of_eq <| leData_data_eq M)

def castAllPermLeLt {β : Λ} (hβ : (β : TypeIndex) < α) :
    AllPermLe M β hβ.le ≃ (M β hβ).data.AllPerm :=
  castAllPerm rfl (heq_of_eq <| leData_data_lt M hβ)

def castAllPermLeEq {β : Λ} (hβ : (β : TypeIndex) = α) :
    AllPermLe M β hβ.le ≃ (newModelData' M).AllPerm :=
  castAllPerm hβ (by cases hβ; exact heq_of_eq <| leData_data_eq M)

def castTangleLeLt {β : Λ} (hβ : (β : TypeIndex) < α) :
    TangleLe M β hβ.le ≃ (letI := (M β hβ).data; Tangle β) :=
  castTangle rfl (heq_of_eq <| leData_data_lt M hβ)

def castTangleLeEq {β : Λ} (hβ : (β : TypeIndex) = α) :
    TangleLe M β hβ.le ≃ (letI := newModelData' M; Tangle α) :=
  castTangle hβ (by cases hβ; exact heq_of_eq <| leData_data_eq M)

theorem castTSetLeLt_forget {β : Λ} (hβ : (β : TypeIndex) < α) (x : TSetLe M β hβ.le) :
    (M β hβ).data.tSetForget (castTSetLeLt M hβ x) =
    letI : Level := ⟨α⟩; letI : LeLevel β := ⟨hβ.le⟩; ((leData M).data β).tSetForget x :=
  castTSet_forget _ _

theorem castTSetLeEq_forget (x : TSetLe M α le_rfl) :
    (newModelData' M).tSetForget (castTSetLeEq M rfl x) =
    letI : Level := ⟨α⟩; letI : LeLevel α := ⟨le_rfl⟩; ((leData M).data α).tSetForget x :=
  castTSet_forget _ _

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
    ρ • castTangleLeLt M hβ t = castTangleLeLt M hβ ((castAllPermLeLt M hβ).symm ρ • t) :=
  castAllPerm_smul _ _ _

theorem castAllPermLeLt_smul' {β : Λ} (hβ : (β : TypeIndex) < α)
    (ρ : AllPermLe M β hβ.le) (t : TangleLe M β hβ.le) :
    castTangleLeLt M hβ (ρ • t) = castAllPermLeLt M hβ ρ • castTangleLeLt M hβ t := by
  rw [castAllPermLeLt_smul, Equiv.symm_apply_apply]

theorem castAllPermLeLt_smul'' {β : Λ} (hβ : (β : TypeIndex) < α)
    (ρ : AllPermLe M β hβ.le) (t : letI := (M β hβ).data; Tangle β) :
    castAllPermLeLt M hβ ρ • t = castTangleLeLt M hβ (ρ • (castTangleLeLt M hβ).symm t) := by
  rw [castAllPermLeLt_smul', Equiv.apply_symm_apply]

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
                ((ltData M).data γ).AllPerm → AllPermLe M γ LeLevel.elim)
              id (λ _γ _ ρ ↦ (castAllPermLeLt M _).symm ρ)
              ((castAllPermLeEq M h ρ).sderiv γ)
          else
            γ.recBotCoe (C := λ γ ↦ [LtLevel γ] → γ < β →
                ((leData M).data β).AllPerm → AllPermLe M γ LeLevel.elim)
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

theorem preCoherentData_allPerm_of_smulFuzz
    {β : Λ} [iβ : letI : Level := ⟨α⟩; LeLevel β]
    (ρs : letI : Level := ⟨α⟩; {γ : TypeIndex} → [LtLevel γ] → γ < β → AllPermLe M γ LeLevel.elim)
    (hρs : letI : Level := ⟨α⟩; ∀ {γ : TypeIndex} {δ : Λ}
      [LtLevel γ] [LtLevel δ] (hγ : γ < β) (hδ : (δ : TypeIndex) < β) (hγδ : γ ≠ δ)
      (t : TangleLe M γ LeLevel.elim),
      letI := preCoherentData M H;
      ((leData M).data δ).allPermForget (ρs hδ) ↘. • fuzz hγδ t = fuzz hγδ (ρs hγ • t)) :
    letI : Level := ⟨α⟩
    ∃ ρ : AllPermLe M β LeLevel.elim, ∀ (γ : TypeIndex) [LtLevel γ] (hγ : γ < β),
      (preCoherentData M H).allPermSderiv hγ ρ = ρs hγ := by
  letI : Level := ⟨α⟩
  by_cases h : (β : TypeIndex) = α
  · cases coe_injective h
    letI := ltData M
    refine ⟨(castAllPermLeEq M rfl).symm ⟨λ β iβ ↦ β.recBotCoe
        (λ _ ↦ ρs (bot_lt_coe _)) (λ β iβ ↦ castAllPermLeLt M iβ.elim (ρs iβ.elim)) iβ, ?_⟩, ?_⟩
    · intro β
      induction β using recBotCoe with
      | bot =>
        intro γ _ _ hβγ t
        simp only [recBotCoe_coe, recBotCoe_bot]
        have := hρs LtLevel.elim LtLevel.elim hβγ t
        rw [← castAllPermLeLt_forget M LtLevel.elim] at this
        exact this
      | coe β =>
        intro γ _ _ hβγ t
        simp only [recBotCoe_coe]
        rw [castAllPermLeLt_smul'' M LtLevel.elim, castTangleLeLt_fuzz M LtLevel.elim]
        have := hρs LtLevel.elim LtLevel.elim hβγ ((castTangleLeLt M LtLevel.elim).symm t)
        rwa [← castTangleLeLt_fuzz M LtLevel.elim, Equiv.apply_symm_apply,
          ← castAllPermLeLt_forget M LtLevel.elim] at this
    · intro β
      induction β using recBotCoe <;>
      · intro _ hβ
        unfold PreCoherentData.allPermSderiv preCoherentData
        simp only [coe_inj, recBotCoe_bot, recBotCoe_coe, id_eq,
          ↓reduceDIte, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  · have := (H β (LeLevel.elim.lt_of_ne h)).allPerm_of_smul_fuzz
      (λ {γ} hγ ↦ letI : LtLevel γ := ⟨hγ.trans_le LeLevel.elim⟩
        castAllPermLeLt M LtLevel.elim (ρs hγ)) (ρs (bot_lt_coe β)) ?_ ?_
    · obtain ⟨ρ, hρ₁, hρ₂⟩ := this
      use (castAllPermLeLt M (LeLevel.elim.lt_of_ne h)).symm ρ
      intro γ
      induction γ using recBotCoe <;>
      · intro _ hβ
        unfold PreCoherentData.allPermSderiv preCoherentData
        simp only [coe_inj, recBotCoe_bot, recBotCoe_coe, id_eq,
          ↓reduceDIte, Equiv.apply_symm_apply, Equiv.symm_apply_apply,
          show β ≠ α from h ∘ congr_arg _, hρ₁, hρ₂]
    · intro γ δ hγ hδ hγδ t
      simp only [recBotCoe_coe]
      letI : LtLevel γ := ⟨hγ.trans_le LeLevel.elim⟩
      letI : LtLevel δ := ⟨hδ.trans_le LeLevel.elim⟩
      rw [castAllPermLeLt_smul'' M, castTangleLeLt_fuzz M]
      have := hρs hγ hδ hγδ ((castTangleLeLt M LtLevel.elim).symm t)
      rwa [← castTangleLeLt_fuzz M LtLevel.elim, Equiv.apply_symm_apply,
        ← castAllPermLeLt_forget M LtLevel.elim] at this
    · intro δ hδ t
      letI : LtLevel δ := ⟨hδ.trans_le LeLevel.elim⟩
      simp only [recBotCoe_coe, recBotCoe_bot]
      have := hρs (bot_lt_coe β) hδ bot_ne_coe t
      rw [← castAllPermLeLt_forget M LtLevel.elim] at this
      exact this

theorem preCoherent_tSet_ext
    (H : (β : Λ) → (h : (β : TypeIndex) < α) → Hypothesis (M β h) λ γ h' ↦ M γ (h'.trans h))
    {β γ : Λ} [iβ : letI : Level := ⟨α⟩; LeLevel β] [iγ : letI : Level := ⟨α⟩; LeLevel γ]
    (hγ : (γ : TypeIndex) < β) (x y : letI : Level := ⟨α⟩; TSetLe M β LeLevel.elim)
    (hxy : letI : Level := ⟨α⟩; ∀ (z : TSetLe M γ LeLevel.elim), z ∈[hγ] x ↔ z ∈[hγ] y) :
    x = y := by
  letI : Level := ⟨α⟩
  by_cases h : (β : TypeIndex) = α
  · cases coe_injective h
    apply (castTSetLeEq M rfl).injective
    letI : LtLevel γ := ⟨hγ⟩
    letI := ltData M
    apply newModelData_ext γ
    intro z
    simp only [← TSet.forget_mem_forget] at hxy ⊢
    convert hxy ((castTSetLeLt M hγ).symm z) using 2
    · have := castTSetLeLt_forget M hγ ((castTSetLeLt M hγ).symm z)
      rwa [Equiv.apply_symm_apply] at this
    · exact castTSetLeEq_forget M x
    · have := castTSetLeLt_forget M hγ ((castTSetLeLt M hγ).symm z)
      rwa [Equiv.apply_symm_apply] at this
    · exact castTSetLeEq_forget M y
  · apply (castTSetLeLt M (LeLevel.elim.lt_of_ne h)).injective
    apply (H β _).tSet_ext γ hγ
    intro z
    simp only [← TSet.forget_mem_forget] at hxy ⊢
    convert hxy ((castTSetLeLt M (hγ.trans_le LeLevel.elim)).symm z) using 2
    · have := castTSetLeLt_forget M (hγ.trans_le LeLevel.elim) ((castTSetLeLt M _).symm z)
      rwa [Equiv.apply_symm_apply] at this
    · exact castTSetLeLt_forget M _ x
    · have := castTSetLeLt_forget M (hγ.trans_le LeLevel.elim) ((castTSetLeLt M _).symm z)
      rwa [Equiv.apply_symm_apply] at this
    · exact castTSetLeLt_forget M _ y

theorem typedMem_singleton_iff
    {β γ : Λ} [iβ : letI : Level := ⟨α⟩; LeLevel β] [iγ : letI : Level := ⟨α⟩; LeLevel γ]
    (hγ : (γ : TypeIndex) < β) (x y : letI : Level := ⟨α⟩; TSetLe M γ LeLevel.elim) :
    y ∈[hγ] (preCoherentData M H).singleton hγ x ↔ y = x := by
  letI : Level := ⟨α⟩
  by_cases h : (β : TypeIndex) = α
  · cases coe_injective h
    unfold singleton preCoherentData
    simp only [coe_inj, ↓reduceDIte, ← TSet.forget_mem_forget]
    letI : LtLevel γ := ⟨hγ⟩
    letI := newModelData' M
    letI := ltData M
    have := mem_newSingleton_iff (castTSetLeLt M _ x) (castTSetLeLt M _ y)
    rw [EmbeddingLike.apply_eq_iff_eq] at this
    have h' := TSet.forget_mem_forget
      (x := castTSetLeLt M _ y)
      (y := show TSet α from Option.some (newSingleton (castTSetLeLt M _ x)))
    rw [← h'] at this
    convert this using 2
    · exact (castTSetLeLt_forget M _ y).symm
    · have := castTSetLeEq_forget M
        ((castTSetLeEq M rfl).symm (Option.some (newSingleton (castTSetLeLt M _ x))))
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
  · unfold singleton preCoherentData
    simp only [coe_inj, show β ≠ α from h ∘ congr_arg _, ↓reduceDIte, ne_eq, ←
      TSet.forget_mem_forget]
    letI := (M β (LeLevel.elim.lt_of_ne h)).data
    letI := (M γ (hγ.trans_le LeLevel.elim)).data
    have := (H β (LeLevel.elim.lt_of_ne h)).typedMem_singleton_iff hγ
      (castTSetLeLt M _ x) (castTSetLeLt M _ y)
    rw [EmbeddingLike.apply_eq_iff_eq] at this
    rw [← TSet.forget_mem_forget] at this
    convert this using 2
    · exact (castTSetLeLt_forget M _ y).symm
    · have := castTSetLeLt_forget M (LeLevel.elim.lt_of_ne h) ((castTSetLeLt M _).symm
        ((H β (LeLevel.elim.lt_of_ne h)).singleton hγ (castTSetLeLt M _ x)))
      rw [Equiv.apply_symm_apply] at this
      exact this.symm

def coherentData :
    letI : Level := ⟨α⟩; CoherentData :=
  letI : Level := ⟨α⟩
  letI := preCoherentData M H
  {
    allPermSderiv_forget := preCoherentData_allPermSderiv_forget M H
    pos_atom_lt_pos := preCoherentData_pos_atom_lt_pos M H
    pos_nearLitter_lt_pos := preCoherentData_pos_nearLitter_lt_pos M H
    smul_fuzz := preCoherentData_smul_fuzz M H
    allPerm_of_basePerm := λ π ↦ ⟨π, rfl⟩
    allPerm_of_smulFuzz := preCoherentData_allPerm_of_smulFuzz M H
    tSet_ext := preCoherent_tSet_ext M H
    typedMem_singleton_iff := typedMem_singleton_iff M H
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

end ConNF
