import ConNF.Model.MainInduction
import ConNF.Model.BasePositions

open Quiver WithBot

universe u

noncomputable section

namespace ConNF

variable [Params.{u}]

def constructionIH (α : Λ) : MainInduction.IH α :=
  (MainInduction.buildCumul α).ih α le_rfl

theorem buildCumul_spec (α : Λ) :
    MainInduction.buildCumul α =
    MainInduction.buildCumulStep α (fun β _ => MainInduction.buildCumul β) := by
  rw [MainInduction.buildCumul, WellFounded.fix_eq]

theorem buildCumul_apply_eq (α β : Λ) (hβ : β ≤ α) :
    (MainInduction.buildCumul α).ih β hβ = (MainInduction.buildCumul β).ih β le_rfl := by
  by_cases hβ' : β = α
  · cases hβ'
    rfl
  rw [buildCumul_spec, buildCumul_spec,
    MainInduction.buildCumulStep, MainInduction.buildCumulStep]
  dsimp only
  rw [MainInduction.buildStepFn, MainInduction.buildStepFn, dif_neg hβ', dif_pos rfl]
  rw [buildCumul_spec, MainInduction.buildCumulStep]
  dsimp only
  rw [MainInduction.buildStepFn, dif_pos rfl]

theorem constructionIHProp (α : Λ) : MainInduction.IHProp α (fun γ _ => constructionIH γ) := by
  convert (MainInduction.buildCumul α).prop α le_rfl using 1
  ext β hβ
  rw [constructionIH, buildCumul_apply_eq α β hβ]

theorem constructionIH_eq (α : Λ) :
    constructionIH α = MainInduction.buildStep α
      (fun β _ => constructionIH β) (fun β _ => constructionIHProp β) := by
  refine ((MainInduction.buildCumul α).ih_eq α le_rfl).trans ?_
  congr 1
  ext β hβ
  rw [buildCumul_apply_eq α β hβ.le]
  rfl

instance modelData (α : Λ) : ModelData α :=
  (constructionIH α).modelData

instance positionedTangles (α : Λ) : PositionedTangles α :=
  (constructionIH α).positionedTangles

instance typedObjects (α : Λ) : TypedObjects α :=
  (constructionIH α).typedObjects

instance : ∀ β : TypeIndex, ModelData β
  | ⊥ => Bot.modelData
  | (β : Λ) => inferInstance

instance : ∀ β : TypeIndex, PositionedTangles β
  | ⊥ => Bot.positionedTangles
  | (β : Λ) => inferInstance

instance [Level] : ModelDataLt := ⟨fun _ _ => inferInstance⟩
instance [Level] : PositionedTanglesLt := ⟨fun _ _ => inferInstance⟩
instance [Level] : TypedObjectsLt := fun _ _ => inferInstance

theorem modelData_eq (α : Λ) :
    modelData α = (MainInduction.buildStep α
      (fun β _ => constructionIH β) (fun β _ => constructionIHProp β)).modelData := by
  rw [modelData, constructionIH_eq]

theorem positionedTangles_heq (α : Λ) :
    HEq (positionedTangles α) (MainInduction.buildStep α
      (fun β _ => constructionIH β) (fun β _ => constructionIHProp β)).positionedTangles := by
  rw [positionedTangles]
  congr 1
  rw [constructionIH_eq]

theorem typedObjects_heq (α : Λ) :
    HEq (typedObjects α) (MainInduction.buildStep α
      (fun β _ => constructionIH β) (fun β _ => constructionIHProp β)).typedObjects := by
  rw [typedObjects]
  congr 1
  rw [constructionIH_eq]

def tSetEquiv (α : Λ) :
    TSet α ≃ (MainInduction.buildStep α
      (fun β _ => constructionIH β) (fun β _ => constructionIHProp β)).TSet :=
  Equiv.cast (by rw [modelData_eq]; rfl)

def tangleEquiv (α : Λ) :
    Tangle α ≃ (MainInduction.buildStep α
      (fun β _ => constructionIH β) (fun β _ => constructionIHProp β)).Tangle :=
  Equiv.cast (by rw [modelData_eq]; rfl)

def allowableEquiv (α : Λ) :
    Allowable α ≃ (MainInduction.buildStep α
      (fun β _ => constructionIH β) (fun β _ => constructionIHProp β)).Allowable :=
  Equiv.cast (by rw [modelData_eq]; rfl)

theorem allowableEquiv_one (α : Λ) :
    allowableEquiv α 1 = 1 :=
  MainInduction.modelData_cast_one α _ _ (modelData_eq α)

theorem allowableEquiv_mul (α : Λ) (ρ₁ ρ₂ : Allowable α) :
    allowableEquiv α (ρ₁ * ρ₂) = allowableEquiv α ρ₁ * allowableEquiv α ρ₂ :=
  MainInduction.modelData_cast_mul α _ _ (modelData_eq α) ρ₁ ρ₂

def allowableIso (α : Λ) :
    Allowable α ≃* (MainInduction.buildStep α
      (fun β _ => constructionIH β) (fun β _ => constructionIHProp β)).Allowable where
  __ := allowableEquiv α
  map_mul' := allowableEquiv_mul α

theorem allowableIso_toStructPerm (α : Λ) (ρ : Allowable α) :
    (MainInduction.buildStep α
      (fun β _ => constructionIH β) (fun β _ => constructionIHProp β)).allowableToStructPerm
    (allowableIso α ρ) = Allowable.toStructPerm ρ :=
  (MainInduction.modelData_cast_toStructPerm α _ _ (modelData_eq α) ρ).symm

@[simp]
theorem tSetEquiv_toStructSet (α : Λ) (t : TSet α) :
    (MainInduction.buildStep α (fun β _ => constructionIH β)
      (fun β _ => constructionIHProp β)).toStructSet (tSetEquiv α t) = toStructSet t :=
  (MainInduction.modelData_cast_toStructSet α _ _ (modelData_eq α) t).symm

@[simp]
theorem tSetEquiv_smul (α : Λ) (ρ : Allowable α) (t : TSet α) :
    tSetEquiv α (ρ • t) = allowableIso α ρ • tSetEquiv α t :=
  MainInduction.modelData_cast_smul α _ _ (modelData_eq α) ρ t

@[simp]
theorem tangleEquiv_smul (α : Λ) (ρ : Allowable α) (t : Tangle α) :
    tangleEquiv α (ρ • t) = allowableIso α ρ • tangleEquiv α t :=
  MainInduction.modelData_cast_smul' α _ _ (modelData_eq α) ρ t

/-! Because we already defined names for things like `Tangle.set` in the inductive step,
we can't give them the same names here. -/

def Tangle.toSet : {β : TypeIndex} → Tangle β → TSet β
  | (β : Λ), t => TangleCoe.set t
  | ⊥, a => a

@[simp]
theorem Tangle.bot_toSet (t : Tangle ⊥) :
    t.toSet = t :=
  rfl

@[simp]
theorem Tangle.coe_toSet (β : Λ) (t : Tangle β) :
    t.toSet = TangleCoe.set t :=
  rfl

@[ext]
theorem Tangle.ext' {β : TypeIndex} (t₁ t₂ : Tangle β)
    (hs : t₁.toSet = t₂.toSet) (hS : t₁.support = t₂.support) : t₁ = t₂ := by
  revert t₁ t₂
  change (_ : _) → _
  refine WithBot.recBotCoe ?_ ?_ β
  · intro t₁ t₂ hs _
    exact hs
  · intro β t₁ t₂ hs hS
    exact TangleCoe.ext _ _ hs hS

@[simp]
theorem Tangle.smul_toSet {β : TypeIndex}
    (t : Tangle β) (ρ : Allowable β) :
    (ρ • t).toSet = ρ • t.toSet := by
  induction β using WithBot.recBotCoe <;> rfl

@[simp]
theorem tangleEquiv_toSet (α : Λ) (t : Tangle α) :
    (letI := (MainInduction.buildStep α (fun β _ => constructionIH β)
      (fun β _ => constructionIHProp β)).modelData
    TangleCoe.set (tangleEquiv α t)) = tSetEquiv α t.toSet :=
  (MainInduction.modelData_cast_set α _ _ (modelData_eq α) t).symm

@[simp]
theorem tangleEquiv_support (α : Λ) (t : Tangle α) :
    (letI := (MainInduction.buildStep α (fun β _ => constructionIH β)
      (fun β _ => constructionIHProp β)).modelData
    TangleCoe.support (tangleEquiv α t)) = t.support :=
  (MainInduction.modelData_cast_support α _ _ (modelData_eq α) t).symm

@[simp]
theorem tSetEquiv_typedNearLitter (α : Λ) (N : NearLitter) :
    tSetEquiv α (typedNearLitter N) = (MainInduction.buildStep α
      (fun β _ => constructionIH β) (fun β _ => constructionIHProp β)).typedNearLitter N :=
  (MainInduction.typedObjects_cast_typedNearLitter
    α _ _ (modelData_eq α) _ _ (positionedTangles_heq α) _ _ (typedObjects_heq α) N).symm

def cons'Coe {α β : Λ} (hβ : (β : TypeIndex) < α) :
    Allowable α → Allowable β :=
  Equiv.cast (by rw [buildCumul_apply_eq]; rfl) ∘
    (((MainInduction.buildCumul α).prop α le_rfl).canCons β (coe_lt_coe.mp hβ)).choose

theorem cons'Coe_spec {α β : Λ} (hβ : (β : TypeIndex) < α) (ρ : Allowable α) :
    Tree.comp (Hom.toPath hβ) (Allowable.toStructPerm ρ) =
      Allowable.toStructPerm (cons'Coe hβ ρ) := by
  refine ((((MainInduction.buildCumul α).prop α le_rfl).canCons β
    (coe_lt_coe.mp hβ)).choose_spec ρ).trans ?_
  unfold ConNF.cons'Coe
  have h₁ := buildCumul_apply_eq α β (coe_le_coe.mp hβ.le)
  erw [MainInduction.modelData_cast_toStructPerm β _ _ (congr_arg MainInduction.IH.modelData h₁)]
  rfl

def cons'Bot {α : Λ} :
    Allowable α → BasePerm :=
  ((MainInduction.buildCumul α).prop α le_rfl).canConsBot.choose

theorem cons'Bot_spec {α : Λ} (ρ : Allowable α) :
    Allowable.toStructPerm ρ (Hom.toPath (bot_lt_coe _)) = cons'Bot ρ :=
  (((MainInduction.buildCumul α).prop α le_rfl).canConsBot).choose_spec ρ

def cons'' : {α β : TypeIndex} → (h : β < α) → Allowable α → Allowable β
  | (α : Λ), (β : Λ), h => cons'Coe h
  | (α : Λ), ⊥, _ => cons'Bot
  | ⊥, _, h => (not_lt_bot h).elim

theorem cons''_one {α β : TypeIndex} (h : β < α) :
    cons'' h 1 = 1 := by
  induction α using recBotCoe
  case bot => cases not_lt_bot h
  case coe α =>
    induction β using recBotCoe
    case bot => simp only [ConNF.cons'', ← cons'Bot_spec, map_one, Tree.one_apply]
    case coe β =>
      simp [ConNF.cons'']
      refine Allowable.toStructPerm_injective β ?_
      rw [← cons'Coe_spec]
      simp only [map_one, Tree.comp_one]

theorem cons'_mul {α β : TypeIndex} (h : β < α) (ρ₁ ρ₂ : Allowable α) :
    cons'' h (ρ₁ * ρ₂) = cons'' h ρ₁ * cons'' h ρ₂ := by
  induction α using recBotCoe
  case bot => cases not_lt_bot h
  case coe α =>
    induction β using recBotCoe
    case bot => simp only [ConNF.cons'', ← cons'Bot_spec, map_mul, Tree.mul_apply]
    case coe β =>
      simp [ConNF.cons'']
      refine Allowable.toStructPerm_injective β ?_
      simp only [← cons'Coe_spec, map_mul, Tree.comp_mul]

def cons' {α β : TypeIndex} (h : β < α) : Allowable α →* Allowable β where
  toFun := cons'' h
  map_one' := cons''_one h
  map_mul' := cons'_mul h

theorem cons'_spec {α β : TypeIndex} (hβ : β < α) (ρ : Allowable α) :
    Tree.comp (Hom.toPath hβ) (Allowable.toStructPerm ρ) =
      Allowable.toStructPerm (cons' hβ ρ) := by
  induction α using recBotCoe
  case bot => cases not_lt_bot hβ
  case coe α =>
    induction β using recBotCoe
    case bot =>
      funext B
      cases path_eq_nil B
      simp only [Tree.comp_apply, Path.comp_nil, ConNF.cons', cons'',
        MonoidHom.coe_mk, OneHom.coe_mk, gt_iff_lt, bot_lt_coe]
      rw [← cons'Bot_spec]
      rfl
    case coe β =>
      simp only [ConNF.cons', cons'', MonoidHom.coe_mk, OneHom.coe_mk]
      rw [cons'Coe_spec]

@[simp]
theorem allowableIso_val {α β : Λ} (hβ : β < α) (ρ : Allowable α) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
    (allowableIso α ρ).val β = ConNF.cons' (coe_lt_coe.mpr hβ) ρ := by
  letI : Level := ⟨α⟩
  letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
  refine Allowable.toStructPerm_injective β ?_
  rw [← NewAllowable.comp_toPath_toStructPerm (allowableIso α ρ) β,
    ← cons'_spec, ← allowableIso_toStructPerm]
  rfl

def comp {α : TypeIndex} : {β : TypeIndex} → (A : Quiver.Path (α : TypeIndex) β) →
    Allowable α →* Allowable β :=
  Quiver.Path.rec
    (motive := fun β _ => Allowable α →* Allowable β)
    (MonoidHom.id _)
    (fun _ h f => (cons' h).comp f)

@[simp]
theorem comp_nil {α : TypeIndex} :
    comp Path.nil = MonoidHom.id (Allowable α) :=
  rfl

@[simp]
theorem comp_toPath {α β : TypeIndex} (h : β < α) :
    comp (Hom.toPath h) = cons' h :=
  rfl

@[simp]
theorem comp_cons {α β γ : TypeIndex} (A : Quiver.Path α β) (h : γ < β) :
    comp (A.cons h) = (cons' h).comp (comp A) :=
  rfl

@[simp]
theorem comp_comp {α β γ : TypeIndex} (A : Quiver.Path α β) (B : Quiver.Path β γ) :
    comp (A.comp B) = (comp B).comp (comp A) := by
  induction B with
  | nil => rfl
  | cons A h ih =>
    simp only [Path.comp_cons, comp_cons, ih]
    rfl

@[simp]
theorem comp_toStructPerm {α β : TypeIndex} (A : Quiver.Path α β) (ρ : Allowable α) :
    Allowable.toStructPerm (comp A ρ) = Tree.comp A (Allowable.toStructPerm ρ) := by
  induction A with
  | nil => simp only [comp_nil, MonoidHom.id_apply, Tree.comp_nil]
  | cons A h ih =>
    rw [Tree.comp_cons, ← ih, cons'_spec]
    rfl

@[simp]
theorem allowableIso_smul_address {α : Λ} (ρ : Allowable α) (c : Address α) :
    allowableIso α ρ • c = ρ • c := by
  change (MainInduction.buildStep α
      (fun β _ => constructionIH β) (fun β _ => constructionIHProp β)).allowableToStructPerm
      (allowableIso α ρ) • c = ρ • c
  rw [allowableIso_toStructPerm]
  rfl

theorem allowableIso_apply_eq {α β : Λ} (h : (β : TypeIndex) < α) (ρ : Allowable α) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨h⟩
    (allowableIso α ρ).val β = comp (Hom.toPath h) ρ := by
  letI : Level := ⟨α⟩
  letI : LtLevel β := ⟨h⟩
  refine Allowable.toStructPerm_injective β ?_
  simp only [comp_toStructPerm]
  rw [← NewAllowable.comp_toPath_toStructPerm (allowableIso α ρ) β,
    ← allowableIso_toStructPerm α ρ]
  rfl

def cons {α β : Λ} (h : β < α) : Allowable α →* Allowable β :=
  cons' (coe_lt_coe.mpr h)

@[simp]
theorem cons'_eq_cons {α β : Λ} (h : (β : TypeIndex) < α) :
    cons' h = cons (coe_lt_coe.mp h) :=
  rfl

@[simp]
theorem cons_toStructPerm {α β : Λ} (h : β < α) (ρ : Allowable α) :
    Allowable.toStructPerm (cons h ρ) =
      Tree.comp (Hom.toPath (coe_lt_coe.mpr h)) (Allowable.toStructPerm ρ) := by
  rw [cons, cons'_spec]

end ConNF
