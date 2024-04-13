import ConNF.Model.Basic

/-!
# Restatement of freedom of action theorems
-/

open Quiver Sum WithBot

open scoped Pointwise symmDiff

universe u

noncomputable section

namespace ConNF

open ModelData TSet

variable [Params.{u}]

namespace MainInduction.FOA

variable [Level]

local instance : FOAData where
  lowerModelData := fun _ _ => inferInstance
  lowerPositionedTangles := fun _ _ => inferInstance
  lowerTypedObjects := fun _ _ => inferInstance
  lowerPositionedObjects := fun _ _ => inferInstance

/-- `Allowable β` is defeq to `foaAllowable β` for every `β : TypeIndex`.
However, it's not the case that `Allowable` is defeq to `foaAllowable`, because we need
to pattern-match on its argument (i.e. check if it's `⊥`) before we can establish the defeq. -/
abbrev foaAllowable (β : TypeIndex) [LeLevel β] : Type u :=
  (FOAData.leModelData β).Allowable

def foaAllowableToStructPerm {β : TypeIndex} [LeLevel β] : foaAllowable β →* StructPerm β :=
  (FOAData.leModelData β).allowableToStructPerm

@[simp]
theorem foaAllowableToStructPerm_eq_coe {β : Λ} [LeLevel β] :
    foaAllowableToStructPerm (β := β) = Allowable.toStructPerm :=
  rfl

@[simp]
theorem foaAllowableToStructPerm_eq_bot :
    foaAllowableToStructPerm (β := ⊥) = Allowable.toStructPerm :=
  rfl

def allowableCons : ∀ {β : TypeIndex} [LeLevel β] {γ : TypeIndex} [LeLevel γ],
      γ < β → foaAllowable β →* foaAllowable γ
  | (β : Λ), _, (γ : Λ), _ => cons'
  | (β : Λ), _, ⊥, _ => cons'
  | ⊥, _, _, _ => fun h => (not_lt_bot h).elim

@[simp]
theorem allowableCons_eq_coe {β : Λ} [LeLevel β] {γ : Λ} [LeLevel γ] (hγ : (γ : TypeIndex) < β) :
    allowableCons hγ = cons (coe_lt_coe.mp hγ) :=
  rfl

@[simp]
theorem allowableCons_eq_bot {β : Λ} [LeLevel β] :
    allowableCons (bot_lt_coe β) = cons' (bot_lt_coe β) :=
  rfl

theorem allowableCons_eq (β : TypeIndex) [iβ : LeLevel β] (γ : TypeIndex) [iγ : LeLevel γ]
    (hγ : γ < β) (ρ : foaAllowable β) :
    Tree.comp (Quiver.Path.nil.cons hγ) (foaAllowableToStructPerm ρ) =
    foaAllowableToStructPerm (allowableCons hγ ρ) := by
  revert iβ iγ
  induction β using recBotCoe with
  | bot => cases not_lt_bot hγ
  | coe β =>
    induction γ using recBotCoe with
    | bot =>
      intro iβ iγ ρ
      rw [foaAllowableToStructPerm_eq_coe, foaAllowableToStructPerm_eq_bot,
        allowableCons_eq_bot]
      exact cons'_spec hγ _
    | coe γ =>
      intro iβ iγ ρ
      rw [foaAllowableToStructPerm_eq_coe, foaAllowableToStructPerm_eq_coe,
        allowableCons_eq_coe]
      exact cons'_spec hγ _

theorem smul_fuzz_bot {β : Λ} [LeLevel β] {δ : Λ} [LtLevel δ]
    (hδ : (δ : TypeIndex) < β)
    (ρ : foaAllowable β) (t : Tangle ⊥) :
    foaAllowableToStructPerm ρ ((Quiver.Hom.toPath hδ).cons (bot_lt_coe _)) •
      fuzz (bot_ne_coe (a := δ)) t =
    fuzz (bot_ne_coe (a := δ)) (allowableCons (bot_lt_coe _) ρ • t) := by
  refine (((MainInduction.buildCumul β).prop β le_rfl).smul_fuzz_bot δ
    (coe_lt_coe.mp hδ) ρ t).trans ?_
  rw [fuzz'Bot, allowableCons]
  congr 2
  exact congr_fun (cons'_spec (bot_lt_coe _) ρ) Path.nil

def tangleEquiv' {β γ : Λ} (hγ : γ ≤ β) :
    Tangle γ ≃ ((buildCumul β).ih γ hγ).Tangle :=
  Equiv.cast (by rw [buildCumul_apply_eq]; rfl)

def allowableEquiv' {β γ : Λ} (hγ : γ ≤ β) :
    Allowable γ ≃ ((buildCumul β).ih γ hγ).Allowable :=
  Equiv.cast (by rw [buildCumul_apply_eq]; rfl)

theorem smul_fuzz {β : Λ} [LeLevel β] {γ : Λ} [LtLevel γ] {δ : Λ} [LtLevel δ]
    (hγ : (γ : TypeIndex) < β) (hδ : (δ : TypeIndex) < β) (hγδ : (γ : TypeIndex) ≠ δ)
    (ρ : foaAllowable β) (t : Tangle γ) :
    foaAllowableToStructPerm ρ ((Quiver.Hom.toPath hδ).cons (bot_lt_coe _)) • fuzz hγδ t =
    fuzz hγδ (allowableCons hγ ρ • t) := by
  have := ((MainInduction.buildCumul β).prop β le_rfl).smul_fuzz
      γ (coe_lt_coe.mp hγ) δ (coe_lt_coe.mp hδ) hγδ ρ
      (tangleEquiv' (coe_lt_coe.mp hγ).le t)
      (fun ρ => allowableEquiv' (coe_lt_coe.mp hγ).le (cons' hγ ρ)) ?_
  · simp only [foaAllowableToStructPerm_eq_coe, allowableCons_eq_coe]
    simp only [cons'_eq_cons] at this
    have h := buildCumul_apply_eq β γ (coe_le_coe.mp hγ.le)
    have hcast := MainInduction.fuzz_cast γ δ hγδ _ _ (congr_arg MainInduction.IH.modelData h)
      _ _ (congr_arg_heq MainInduction.IH.positionedTangles h)
    rw [tangleEquiv', Equiv.cast_apply] at this
    rw [fuzz', hcast, hcast] at this
    rw [cast_cast, cast_eq] at this
    refine this.trans (congr_arg _ ?_)
    erw [MainInduction.modelData_cast_smul' γ _ _ (congr_arg MainInduction.IH.modelData h)]
    simp only [allowableEquiv', Equiv.cast_apply, cast_cast, cast_eq]
    rfl
  · intro ρ
    simp only [cons'_eq_cons]
    have h := buildCumul_apply_eq β γ (coe_le_coe.mp hγ.le)
    erw [MainInduction.modelData_cast_toStructPerm γ _ _ (congr_arg MainInduction.IH.modelData h)]
    rw [allowableEquiv']
    simp only [Equiv.cast_apply, cast_cast, cast_eq]
    erw [cons_toStructPerm]
    rfl

theorem allowable_of_smulFuzz (β : Λ) [iβ : LeLevel β]
    (ρs : ∀ γ : Λ, [LtLevel γ] → (γ : TypeIndex) < β → foaAllowable γ)
    (π : NearLitterPerm) :
    (∀ (γ : Λ) [LtLevel γ] (δ : Λ) [LtLevel δ]
        (hγ : (γ : TypeIndex) < β) (hδ : (δ : TypeIndex) < β) (hγδ : (γ : TypeIndex) ≠ δ)
        (t : Tangle γ),
        Allowable.toStructPerm (ρs δ hδ) (Quiver.Hom.toPath (bot_lt_coe _)) • fuzz hγδ t =
        fuzz hγδ (ρs γ hγ • t)) →
    (∀ (δ : Λ) [LtLevel δ] (hδ : (δ : TypeIndex) < β) (a : Atom),
        Allowable.toStructPerm (ρs δ hδ) (Quiver.Hom.toPath (bot_lt_coe _)) •
          fuzz (bot_ne_coe (a := δ)) a =
        fuzz (bot_ne_coe (a := δ)) (π • a)) →
      ∃ ρ : Allowable β,
      (∀ (γ : Λ) [LtLevel γ] (hγ : (γ : TypeIndex) < β), allowableCons hγ ρ = ρs γ hγ) ∧
      allowableCons (bot_lt_coe _) ρ = π := by
  letI : Level := ⟨α⟩
  have hβ := iβ.elim
  intro h₁ h₂
  have := ((MainInduction.buildCumul β).prop β le_rfl).allowable_of_smulFuzz
      (fun γ hγ => letI : LtLevel γ := ⟨(coe_lt_coe.mpr hγ).trans_le hβ⟩;
        allowableEquiv' hγ.le (ρs γ (coe_lt_coe.mpr hγ))) π ?_ ?_
  · obtain ⟨ρ, hρ₁, hρ₂⟩ := this
    refine ⟨ρ, ?_, ?_⟩
    · intro γ _ hγ
      have := hρ₁ γ (coe_lt_coe.mp hγ)
        (fun ρ => allowableEquiv' (coe_lt_coe.mp hγ).le (cons' hγ ρ)) ?_
      · exact (allowableEquiv' _).injective this
      · intro ρ
        simp only [cons'_eq_cons]
        have h := buildCumul_apply_eq β γ (coe_le_coe.mp hγ.le)
        erw [MainInduction.modelData_cast_toStructPerm γ _ _
          (congr_arg MainInduction.IH.modelData h)]
        rw [allowableEquiv']
        simp only [Equiv.cast_apply, cast_cast, cast_eq]
        erw [cons_toStructPerm]
        rfl
    · refine hρ₂ (cons' (bot_lt_coe _)) ?_
      intro ρ
      exact congr_fun (cons'_spec (bot_lt_coe _) ρ) Path.nil
  · intro γ hγ δ hδ hγδ t
    letI : LtLevel γ := ⟨(coe_lt_coe.mpr hγ).trans_le hβ⟩
    letI : LtLevel δ := ⟨(coe_lt_coe.mpr hδ).trans_le hβ⟩
    have h := buildCumul_apply_eq β γ hγ.le
    have hcast := MainInduction.fuzz_cast γ δ hγδ _ _ (congr_arg MainInduction.IH.modelData h)
      _ _ (congr_arg_heq MainInduction.IH.positionedTangles h)
    have hcast' := MainInduction.modelData_cast_smul' γ _ _ (congr_arg MainInduction.IH.modelData h).symm
      (ρs γ (coe_lt_coe.mpr hγ)) ((tangleEquiv' hγ.le).symm t)
    simp only [tangleEquiv', Equiv.cast_symm, Equiv.cast_apply, cast_cast, cast_eq] at hcast'
    change _ = allowableEquiv' hγ.le (ρs γ (coe_lt_coe.mpr hγ)) • t at hcast'
    dsimp only [fuzz']
    rw [hcast, hcast, ← hcast', cast_cast, cast_eq]
    refine Eq.trans ?_
      (h₁ γ δ (coe_lt_coe.mpr hγ) (coe_lt_coe.mpr hδ) hγδ ((tangleEquiv' hγ.le).symm t))
    have := MainInduction.modelData_cast_toStructPerm δ _ _
      (congr_arg MainInduction.IH.modelData (buildCumul_apply_eq β δ hδ.le))
    erw [this]
    rw [allowableEquiv', Equiv.cast_apply, cast_cast, cast_eq]
    rfl
  · intro δ hδ a
    letI : LtLevel δ := ⟨(coe_lt_coe.mpr hδ).trans_le hβ⟩
    dsimp only [fuzz'Bot]
    have := MainInduction.modelData_cast_toStructPerm δ _ _
      (congr_arg MainInduction.IH.modelData (buildCumul_apply_eq β δ hδ.le))
    erw [this]
    rw [← h₂ δ (coe_lt_coe.mpr hδ) a, allowableEquiv', Equiv.cast_apply, cast_cast, cast_eq]
    rfl

local instance foaAssumptions : FOAAssumptions where
  allowableCons := allowableCons
  allowableCons_eq := allowableCons_eq
  pos_lt_pos_atom := by
    intro β _
    exact ((MainInduction.buildCumul β).prop β le_rfl).pos_lt_pos_atom
  pos_lt_pos_nearLitter := by
    intro β _
    exact ((MainInduction.buildCumul β).prop β le_rfl).pos_lt_pos_nearLitter
  smul_fuzz := by
    intro β
    induction β using recBotCoe with
    | bot =>
      intro _ _ _ δ _ _ hδ
      cases not_lt_bot hδ
    | coe β =>
      intro hβ γ
      induction γ using recBotCoe with
      | bot => intro _ δ _ _ hδ _; exact smul_fuzz_bot hδ
      | coe β => exact smul_fuzz
  allowable_of_smulFuzz := by
    intro β _ ρs hρs
    have := allowable_of_smulFuzz β (fun γ => ρs γ) (ρs ⊥ (bot_lt_coe _)) ?_ ?_
    · obtain ⟨ρ, h₁, h₂⟩ := this
      refine ⟨ρ, ?_⟩
      intro γ
      induction γ using recBotCoe with
      | bot =>
        intro _ _
        exact h₂
      | coe γ =>
        intro _ hγ
        exact h₁ γ hγ
    · intro γ _ δ _ hγ hδ hγδ t
      exact hρs γ δ hγ hδ hγδ t
    · intro δ _ hδ a
      exact hρs ⊥ δ (bot_lt_coe _) hδ bot_ne_coe a

theorem exists_allowable_of_specifies {S T : Support α} (hS : S.Strong) (hT : T.Strong)
    {σ : Spec α} (hσS : σ.Specifies S hS) (hσT : σ.Specifies T hT) :
    ∃ ρ : Allowable α, ρ • S = T :=
  ⟨convertAllowable hσS hσT, convertAllowable_smul hσS hσT⟩

end MainInduction.FOA

end ConNF
