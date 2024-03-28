import ConNF.NewTangle
import ConNF.Counting
import ConNF.Model.CountZero

open Cardinal Function MulAction Set Sum Quiver WithBot

open scoped Cardinal

universe u

namespace ConNF.Construction

variable [Params.{u}] [BasePositions]

@[ext]
structure Tang (α : Λ) (TSet : Type u) (Allowable : Type u)
    [Group Allowable] [MulAction Allowable TSet] [MulAction Allowable (Address α)] where
  set : TSet
  support : Support α
  support_supports : MulAction.Supports Allowable (support : Set (Address α)) set

/-- The data for the main inductive hypothesis,
containing the things we need to construct at each level `α`. -/
structure IH (α : Λ) where
  TSet : Type u
  Allowable : Type u
  [allowableGroup : Group Allowable]
  allowableToStructPerm : Allowable →* StructPerm α
  /-- We make this assumption for convenience, since it makes `IHProp` into a subsingleton,
  and so we can encode it as a `Prop`. -/
  allowableToStructPerm_injective : Function.Injective allowableToStructPerm
  [allowableAction : MulAction Allowable TSet]
  has_support (t : TSet) : ∃ S: Support α,
    letI : MulAction Allowable (Address α) :=
      MulAction.compHom _ allowableToStructPerm
    MulAction.Supports Allowable (S : Set (Address α)) t
  pos :
    letI : MulAction Allowable (Address α) :=
      MulAction.compHom _ allowableToStructPerm
    Tang α TSet Allowable ↪ μ
  typedAtom : Atom ↪ TSet
  typedNearLitter : NearLitter ↪ TSet
  pos_typedAtom :
    letI : MulAction Allowable (Address α) := MulAction.compHom _ allowableToStructPerm
    ∀ (a : Atom) (t : Tang α TSet Allowable),
    t.set = typedAtom a → ConNF.pos a ≤ pos t
  pos_typedNearLitter :
    letI : MulAction Allowable (Address α) := MulAction.compHom _ allowableToStructPerm
    ∀ (N : NearLitter) (t : Tang α TSet Allowable),
    t.set = typedNearLitter N → ConNF.pos N ≤ pos t
  smul_typedNearLitter :
    ∀ (ρ : Allowable) (N : NearLitter),
    ρ • typedNearLitter N =
    typedNearLitter ((allowableToStructPerm ρ) (Hom.toPath <| bot_lt_coe α) • N)
  toPretangle : TSet ↪ Pretangle α
  toPretangle_smul (ρ : Allowable) (t : TSet) :
    letI : MulAction Allowable (Pretangle α) :=
      MulAction.compHom _ allowableToStructPerm
    toPretangle (ρ • t) = ρ • toPretangle t

instance {α : Λ} {ih : IH α} : Group ih.Allowable := ih.allowableGroup
instance {α : Λ} {ih : IH α} : MulAction ih.Allowable ih.TSet := ih.allowableAction
instance {α : Λ} {ih : IH α} {X : Type _} [MulAction (StructPerm α) X] :
    MulAction ih.Allowable X :=
  MulAction.compHom _ ih.allowableToStructPerm

def IH.tangleData {α : Λ} (ih : IH α) : TangleData α where
  TSet := ih.TSet
  Allowable := ih.Allowable
  allowableToStructPerm := ih.allowableToStructPerm
  allowableToStructPerm_injective := ih.allowableToStructPerm_injective
  has_support := ih.has_support
  toPretangle := ih.toPretangle
  toPretangle_smul := ih.toPretangle_smul

protected def IH.Tangle {α : Λ} (ih : IH α) : Type u :=
  letI := ih.tangleData
  Tangle α

instance {α : Λ} {ih : IH α} : MulAction ih.Allowable ih.Tangle :=
  letI := ih.tangleData
  inferInstanceAs (MulAction (Allowable α) (Tangle α))

instance {α : Λ} {ih : IH α} : MulAction ih.Allowable (letI := ih.tangleData; Tangle α) :=
  letI := ih.tangleData
  inferInstanceAs (MulAction (Allowable α) (Tangle α))

def IH.tangleEquiv {α : Λ} (ih : IH α) :
    letI := ih.tangleData
    Tangle α ≃ Tang α ih.TSet ih.Allowable :=
  letI : Level := ⟨α⟩
  letI := ih.tangleData
  { toFun := fun t => ⟨TangleCoe.set t, TangleCoe.support t, TangleCoe.support_supports t⟩,
    invFun := fun t => ⟨t.set, t.support, t.support_supports⟩,
    left_inv := fun _ => rfl,
    right_inv := fun _ => rfl}

def IH.positionedTangles {α : Λ} (ih : IH α) :
    letI := ih.tangleData
    PositionedTangles α :=
  letI := ih.tangleData
  ⟨⟨fun t => ih.pos (ih.tangleEquiv t),
    fun _ _ h => ih.tangleEquiv.injective (ih.pos.injective h)⟩⟩

def IH.typedObjects {α : Λ} (ih : IH α) :
    letI := ih.tangleData
    TypedObjects α :=
  letI := ih.tangleData
  { typedAtom := ih.typedAtom
    typedNearLitter := ih.typedNearLitter
    smul_typedNearLitter := ih.smul_typedNearLitter }

@[simp]
theorem IH.pos_tangleEquiv {α : Λ} (ih : IH α) (t : letI := ih.tangleData; Tangle α) :
    letI := ih.tangleData
    letI := ih.positionedTangles
    ConNF.pos t = ih.pos (ih.tangleEquiv t) :=
  rfl

theorem IH.positionedObjects {α : Λ} (ih : IH α) :
    letI := ih.tangleData
    letI := ih.positionedTangles
    letI := ih.typedObjects
    PositionedObjects α := by
  letI := ih.tangleData
  letI := ih.positionedTangles
  letI := ih.typedObjects
  constructor
  · intro a t h
    exact ih.pos_typedAtom a (ih.tangleEquiv t) h
  · intro N t h
    exact ih.pos_typedNearLitter N (ih.tangleEquiv t) h

/-- A renaming of `fuzz` that uses only data from the `IH`s. -/
noncomputable def fuzz' {β γ : Λ} (ihβ : IH β) (ihγ : IH γ) (h : (β : TypeIndex) ≠ γ) :
    (letI := ihβ.tangleData; Tangle β) → Litter :=
  letI := ihβ.tangleData
  letI := ihβ.positionedTangles
  letI := ihγ.tangleData
  letI := ihγ.positionedTangles
  letI := ihγ.typedObjects
  fuzz h

/-- A renaming of `fuzz` that uses only data from the `IH`s. -/
noncomputable def fuzz'Bot {γ : Λ} (ihγ : IH γ) : Atom → Litter :=
  letI := ihγ.tangleData
  letI := ihγ.positionedTangles
  letI := ihγ.typedObjects
  fuzz (bot_ne_coe (a := γ))

def tangleDataStep (α : Λ) (ihs : (β : Λ) → β < α → IH β) : TangleData α :=
  letI : Level := ⟨α⟩
  letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
  letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
  letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
  letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
  {
    TSet := NewTSet
    Allowable := NewAllowable
    allowableToStructPerm := NewAllowable.toStructPerm
    allowableToStructPerm_injective := NewAllowable.toStructPerm_injective
    has_support := by
      intro t
      obtain ⟨S, hS⟩ := t.prop
      exact ⟨S, fun ρ hρ => Subtype.ext (hS ρ hρ)⟩
    toPretangle := ⟨NewTSet.toPretangle, NewTSet.toPretangle_injective⟩
    toPretangle_smul := NewTSet.toPretangle_smul
  }

def typedObjectsStep (α : Λ) (ihs : (β : Λ) → β < α → IH β) :
    letI := tangleDataStep α ihs
    TypedObjects α :=
  letI : Level := ⟨α⟩
  letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
  letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
  letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
  letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
  letI := tangleDataStep α ihs
  {
    typedAtom := ⟨newTypedAtom, newTypedAtom_injective⟩
    typedNearLitter := ⟨newTypedNearLitter, newTypedNearLitter_injective⟩
    smul_typedNearLitter := fun ρ N => NewAllowable.smul_newTypedNearLitter N ρ
  }

noncomputable def tangleDataStepFn (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β ≤ α) : TangleData β :=
  if hβ' : β = α then
    hβ' ▸ tangleDataStep α ihs
  else
    (ihs β (lt_of_le_of_ne hβ hβ')).tangleData

theorem tangleDataStepFn_eq (α : Λ) (ihs : (β : Λ) → β < α → IH β) :
    tangleDataStepFn α ihs α le_rfl = tangleDataStep α ihs := by
  rw [tangleDataStepFn, dif_pos rfl]

theorem tangleDataStepFn_lt (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) :
    tangleDataStepFn α ihs β hβ.le = (ihs β hβ).tangleData := by
  rw [tangleDataStepFn, dif_neg (ne_of_lt hβ)]

noncomputable def typedObjectsStepFn (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β ≤ α) :
    letI := tangleDataStepFn α ihs β hβ
    TypedObjects β :=
  if hβ' : β = α then
    hβ'.symm ▸ tangleDataStepFn_eq α ihs ▸ typedObjectsStep α ihs
  else
    cast (by rw [tangleDataStepFn_lt α ihs β (lt_of_le_of_ne hβ hβ')])
      (ihs β (lt_of_le_of_ne hβ hβ')).typedObjects

theorem typedObjectsStepFn_lt (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) :
    letI := tangleDataStepFn α ihs β hβ.le
    typedObjectsStepFn α ihs β hβ.le =
      cast (by rw [tangleDataStepFn_lt α ihs β hβ]) (ihs β hβ).typedObjects := by
  rw [typedObjectsStepFn, dif_neg (ne_of_lt hβ)]

noncomputable def buildStepFOAData (α : Λ) (ihs : (β : Λ) → β < α → IH β) :
    letI : Level := ⟨α⟩
    FOAData :=
  letI : Level := ⟨α⟩
  {
    lowerTangleData := fun β hβ => tangleDataStepFn α ihs β (coe_le_coe.mp hβ.elim)
    lowerPositionedTangles := fun β hβ =>
      cast (by rw [← tangleDataStepFn_lt α ihs β (coe_lt_coe.mp hβ.elim)])
        (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles
    lowerTypedObjects := fun β hβ => typedObjectsStepFn α ihs β (coe_le_coe.mp hβ.elim)
    lowerPositionedObjects := fun β hβ =>
      cast (by
        congr 1
        · rw [← tangleDataStepFn_lt α ihs β (coe_lt_coe.mp hβ.elim)]
        · simp only [← tangleDataStepFn_lt α ihs β (coe_lt_coe.mp hβ.elim)]
          exact (cast_heq _ _).symm
        · dsimp only
          rw [typedObjectsStepFn_lt α ihs β (coe_lt_coe.mp hβ.elim)]
          exact heq_of_cast_eq _ rfl)
        (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
  }

theorem buildStepFOAData_positioned_lt (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
    HEq ((buildStepFOAData α ihs).lowerPositionedTangles β) (ihs β hβ).positionedTangles := by
  unfold FOAData.lowerPositionedTangles buildStepFOAData
  simp only [id_eq, eq_mpr_eq_cast, cast_heq]

theorem foaData_tSet_eq (α : Λ) (ihs : (β : Λ) → β < α → IH β) :
    letI : Level := ⟨α⟩
    letI : LeLevel α := ⟨le_rfl⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
    letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
    letI : FOAData := buildStepFOAData α ihs
    TSet α = NewTSet := by
  change (tangleDataStepFn α ihs α le_rfl).TSet = _
  rw [tangleDataStepFn_eq]
  rfl

def foaData_tSet_eq_equiv (α : Λ) (ihs : (β : Λ) → β < α → IH β) :
    letI : Level := ⟨α⟩
    letI : LeLevel α := ⟨le_rfl⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
    letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
    letI : FOAData := buildStepFOAData α ihs
    TSet α ≃ NewTSet :=
  Equiv.cast (foaData_tSet_eq α ihs)

theorem foaData_tSet_lt (α : Λ) (ihs : (β : Λ) → β < α → IH β) (β : Λ) (hβ : β < α) :
    letI : Level := ⟨α⟩
    letI : LeLevel β := ⟨coe_le_coe.mpr hβ.le⟩
    letI : FOAData := buildStepFOAData α ihs
    TSet β = (ihs β hβ).TSet := by
  change (tangleDataStepFn α ihs β hβ.le).TSet = _
  rw [tangleDataStepFn_lt]
  rfl

def foaData_tSet_lt_equiv (α : Λ) (ihs : (β : Λ) → β < α → IH β) (β : Λ) (hβ : β < α) :
    letI : Level := ⟨α⟩
    letI : LeLevel β := ⟨coe_le_coe.mpr hβ.le⟩
    letI : FOAData := buildStepFOAData α ihs
    TSet β ≃ (ihs β hβ).TSet :=
  Equiv.cast (foaData_tSet_lt α ihs β hβ)

theorem foaData_tangle_lt (α : Λ) (ihs : (β : Λ) → β < α → IH β) (β : Λ) (hβ : β < α) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
    (letI : FOAData := buildStepFOAData α ihs
    Tangle β) =
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    Tangle β) := by
  letI : Level := ⟨α⟩
  letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
  change @TangleCoe _ β (tangleDataStepFn α ihs β hβ.le) = _
  rw [tangleDataStepFn_lt α ihs β hβ]
  rfl

def foaData_tangle_lt_equiv (α : Λ) (ihs : (β : Λ) → β < α → IH β) (β : Λ) (hβ : β < α) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
    (letI : FOAData := buildStepFOAData α ihs
    Tangle β) ≃
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    Tangle β) :=
  Equiv.cast (foaData_tangle_lt α ihs β hβ)

theorem foaData_allowable_eq (α : Λ) (ihs : (β : Λ) → β < α → IH β) :
    letI : Level := ⟨α⟩
    letI : LeLevel α := ⟨le_rfl⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
    letI : FOAData := buildStepFOAData α ihs
    Allowable α = NewAllowable := by
  change (tangleDataStepFn α ihs α le_rfl).Allowable = _
  rw [tangleDataStepFn_eq]
  rfl

def foaData_allowable_eq_equiv (α : Λ) (ihs : (β : Λ) → β < α → IH β) :
    letI : Level := ⟨α⟩
    letI : LeLevel α := ⟨le_rfl⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
    letI : FOAData := buildStepFOAData α ihs
    Allowable α ≃ NewAllowable :=
    Equiv.cast (foaData_allowable_eq α ihs)

theorem tangleData_cast_one (α : Λ) (i₁ i₂ : TangleData α) (h : i₁ = i₂) :
    cast (show i₁.Allowable = i₂.Allowable by rw [h]) i₁.allowableGroup.one =
      i₂.allowableGroup.one :=
  by subst h; rfl

theorem tangleData_cast_mul (α : Λ) (i₁ i₂ : TangleData α) (h : i₁ = i₂)
    (ρ₁ ρ₂ : i₁.Allowable) :
    cast (show i₁.Allowable = i₂.Allowable by rw [h]) (i₁.allowableGroup.mul ρ₁ ρ₂) =
    i₂.allowableGroup.mul
      (cast (show i₁.Allowable = i₂.Allowable by rw [h]) ρ₁)
      (cast (show i₁.Allowable = i₂.Allowable by rw [h]) ρ₂) :=
  by subst h; rfl

theorem tangleData_cast_toStructPerm (α : Λ) (i₁ i₂ : TangleData α) (h : i₁ = i₂) (ρ) :
    i₁.allowableToStructPerm ρ =
    i₂.allowableToStructPerm (cast (show i₁.Allowable = i₂.Allowable by rw [h]) ρ) :=
  by subst h; rfl

theorem tangleData_cast_toPretangle (α : Λ) (i₁ i₂ : TangleData α) (h : i₁ = i₂) (t) :
    i₁.toPretangle t =
    i₂.toPretangle (cast (show i₁.TSet = i₂.TSet by rw [h]) t) :=
  by subst h; rfl

theorem tangleData_cast_smul (α : Λ) (i₁ i₂ : TangleData α) (h : i₁ = i₂) (ρ t) :
    cast (show i₁.TSet = i₂.TSet by rw [h]) (i₁.allowableAction.smul ρ t) =
    i₂.allowableAction.smul
      (cast (show i₁.Allowable = i₂.Allowable by rw [h]) ρ)
      (cast (show i₁.TSet = i₂.TSet by rw [h]) t) :=
  by subst h; rfl

theorem tangleData_cast_smul' (α : Λ) (i₁ i₂ : TangleData α) (h : i₁ = i₂) (ρ t) :
    cast (show (letI := i₁; Tangle α) = (letI := i₂; Tangle α) by rw [h])
      ((inferInstanceAs (MulAction (letI := i₁; Allowable α) (letI := i₁; Tangle α))).smul ρ t) =
    (inferInstanceAs (MulAction (letI := i₂; Allowable α) (letI := i₂; Tangle α))).smul
      (cast (show i₁.Allowable = i₂.Allowable by rw [h]) ρ)
      (cast (show (letI := i₁; Tangle α) = (letI := i₂; Tangle α) by rw [h]) t) :=
  by subst h; rfl

theorem tangleData_cast_set (α : Λ) (i₁ i₂ : TangleData α) (hi : i₁ = i₂)
    (t) :
    cast (show i₁.TSet = i₂.TSet by rw [hi])
    (letI := i₁
    TangleCoe.set t) =
    (letI := i₂
    TangleCoe.set (cast (show (letI := i₁; Tangle α) = (letI := i₂; Tangle α) by rw [hi]) t)) :=
  by subst hi; rfl

theorem tangleData_cast_support (α : Λ) (i₁ i₂ : TangleData α) (hi : i₁ = i₂)
    (t) :
    (letI := i₁; t.support) =
      (cast (show (letI := i₁; Tangle α) = (letI := i₂; Tangle α) by rw [hi]) t).support :=
  by subst hi; rfl

theorem positionedTangles_cast_pos (α : Λ) (i₁ i₂ : TangleData α) (hi : i₁ = i₂)
    (j₁ : letI := i₁; PositionedTangles α) (j₂ : letI := i₂; PositionedTangles α) (hj : HEq j₁ j₂)
    (t) :
    pos t = pos (cast (show (letI := i₁; Tangle α) = (letI := i₂; Tangle α) by rw [hi]) t) :=
  by subst hi; subst hj; rfl

theorem typedObjects_cast_typedAtom (α : Λ) (i₁ i₂ : TangleData α) (hi : i₁ = i₂)
    (j₁ : letI := i₁; TypedObjects α) (j₂ : letI := i₂; TypedObjects α) (hj : HEq j₁ j₂)
    (a : Atom) :
    (letI := i₂; typedAtom a) =
    (letI := i₁; cast (show i₁.TSet = i₂.TSet by rw [hi]) (typedAtom a)) :=
  by subst hi; subst hj; rfl

theorem typedObjects_cast_typedNearLitter (α : Λ) (i₁ i₂ : TangleData α) (hi : i₁ = i₂)
    (j₁ : letI := i₁; TypedObjects α) (j₂ : letI := i₂; TypedObjects α) (hj : HEq j₁ j₂)
    (N : NearLitter) :
    (letI := i₂; typedNearLitter N) =
    (letI := i₁; cast (show i₁.TSet = i₂.TSet by rw [hi]) (typedNearLitter N)) :=
  by subst hi; subst hj; rfl

theorem fuzz_cast (β : TypeIndex) (γ : Λ) (hβγ : β ≠ γ)
    (i₁ i₂ : TangleData β) (hi : i₁ = i₂)
    (j₁ : letI := i₁; PositionedTangles β) (j₂ : letI := i₂; PositionedTangles β) (hj : HEq j₁ j₂)
    (t) :
    (letI := i₁; letI := j₁; fuzz hβγ t) =
    (letI := i₂; letI := j₂; fuzz hβγ
      (cast (show (letI := i₁; Tangle β) = (letI := i₂; Tangle β) by rw [hi]) t)) :=
  by subst hi; subst hj; rfl

@[simp]
theorem foaData_tSet_eq_equiv_toPretangle (α : Λ) (ihs : (β : Λ) → β < α → IH β) (t) :
    letI : Level := ⟨α⟩
    letI : LeLevel α := ⟨le_rfl⟩
    (letI : FOAData := buildStepFOAData α ihs
    toPretangle t) =
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
    letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
    NewTSet.toPretangle (foaData_tSet_eq_equiv α ihs t)) :=
  tangleData_cast_toPretangle α _ _ (tangleDataStepFn_eq α ihs) t

@[simp]
theorem foaData_allowable_eq_equiv_one (α : Λ) (ihs : (β : Λ) → β < α → IH β) :
    foaData_allowable_eq_equiv α ihs 1 = 1 :=
  tangleData_cast_one α _ _ (tangleDataStepFn_eq α ihs)

@[simp]
theorem foaData_allowable_eq_equiv_mul (α : Λ) (ihs : (β : Λ) → β < α → IH β) (ρ₁ ρ₂) :
    foaData_allowable_eq_equiv α ihs (ρ₁ * ρ₂) =
    foaData_allowable_eq_equiv α ihs ρ₁ * foaData_allowable_eq_equiv α ihs ρ₂ :=
  tangleData_cast_mul α _ _ (tangleDataStepFn_eq α ihs) ρ₁ ρ₂

@[simp]
theorem foaData_allowable_eq_equiv_toStructPerm (α : Λ) (ihs : (β : Λ) → β < α → IH β) (ρ) :
    letI : Level := ⟨α⟩
    letI : LeLevel α := ⟨le_rfl⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : FOAData := buildStepFOAData α ihs
    Allowable.toStructPerm ρ =
    NewAllowable.toStructPerm (foaData_allowable_eq_equiv α ihs ρ) :=
  tangleData_cast_toStructPerm α _ _ (tangleDataStepFn_eq α ihs) ρ

@[simp]
theorem foaData_allowable_eq_equiv_smul (α : Λ) (ihs : (β : Λ) → β < α → IH β) (ρ t) :
    letI : Level := ⟨α⟩
    letI : LeLevel α := ⟨le_rfl⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
    letI : FOAData := buildStepFOAData α ihs
    foaData_tSet_eq_equiv α ihs (ρ • t) =
    foaData_allowable_eq_equiv α ihs ρ • foaData_tSet_eq_equiv α ihs t :=
  tangleData_cast_smul α _ _ (tangleDataStepFn_eq α ihs) ρ t

@[simp]
theorem foaData_tSet_lt_equiv_toPretangle (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) (t) :
    letI : Level := ⟨α⟩
    letI : LeLevel β := ⟨coe_le_coe.mpr hβ.le⟩
    (letI : FOAData := buildStepFOAData α ihs
    toPretangle t) =
    (ihs β hβ).toPretangle (foaData_tSet_lt_equiv α ihs β hβ t) :=
  tangleData_cast_toPretangle β _ _ (tangleDataStepFn_lt α ihs β hβ) t

@[simp]
theorem foaData_tSet_lt_equiv_toPretangle' (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) (t) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
    (letI : FOAData := buildStepFOAData α ihs
    toPretangle t) =
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    toPretangle (foaData_tSet_lt_equiv α ihs β hβ t)) :=
  tangleData_cast_toPretangle β _ _ (tangleDataStepFn_lt α ihs β hβ) t

theorem foaData_allowable_lt (α : Λ) (ihs : (β : Λ) → β < α → IH β) (β : Λ) (hβ : β < α) :
    letI : Level := ⟨α⟩
    letI : LeLevel β := ⟨coe_le_coe.mpr hβ.le⟩
    letI : FOAData := buildStepFOAData α ihs
    Allowable β = (ihs β hβ).Allowable := by
  change (tangleDataStepFn α ihs β hβ.le).Allowable = _
  rw [tangleDataStepFn_lt]
  rfl

def foaData_allowable_lt_equiv (α : Λ) (ihs : (β : Λ) → β < α → IH β) (β : Λ) (hβ : β < α) :
    letI : Level := ⟨α⟩
    letI : LeLevel β := ⟨coe_le_coe.mpr hβ.le⟩
    letI : FOAData := buildStepFOAData α ihs
    Allowable β ≃ (ihs β hβ).Allowable :=
    Equiv.cast (foaData_allowable_lt α ihs β hβ)

@[simp]
theorem foaData_allowable_lt_equiv_one (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) :
    foaData_allowable_lt_equiv α ihs β hβ 1 = 1 :=
  tangleData_cast_one β _ _ (tangleDataStepFn_lt α ihs β hβ)

@[simp]
theorem foaData_allowable_lt_equiv_mul (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) (ρ₁ ρ₂) :
    foaData_allowable_lt_equiv α ihs β hβ (ρ₁ * ρ₂) =
    foaData_allowable_lt_equiv α ihs β hβ ρ₁ * foaData_allowable_lt_equiv α ihs β hβ ρ₂ :=
  tangleData_cast_mul β _ _ (tangleDataStepFn_lt α ihs β hβ) ρ₁ ρ₂

@[simp]
theorem foaData_allowable_lt_equiv_toStructPerm (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) (ρ) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
    (letI : FOAData := buildStepFOAData α ihs
    Allowable.toStructPerm ρ) =
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    Allowable.toStructPerm (foaData_allowable_lt_equiv α ihs β hβ ρ)) :=
  tangleData_cast_toStructPerm β _ _ (tangleDataStepFn_lt α ihs β hβ) ρ

@[simp]
theorem foaData_allowable_lt_equiv_smul (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) (ρ t) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
    foaData_tSet_lt_equiv α ihs β hβ
    (letI : FOAData := buildStepFOAData α ihs; ρ • t) =
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    foaData_allowable_lt_equiv α ihs β hβ ρ • foaData_tSet_lt_equiv α ihs β hβ t) :=
  tangleData_cast_smul β _ _ (tangleDataStepFn_lt α ihs β hβ) ρ t

@[simp]
theorem foaData_allowable_lt_equiv_smul' (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) (ρ t) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
    foaData_tangle_lt_equiv α ihs β hβ
    (letI : FOAData := buildStepFOAData α ihs; ρ • t) =
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    foaData_allowable_lt_equiv α ihs β hβ ρ • foaData_tangle_lt_equiv α ihs β hβ t) :=
  tangleData_cast_smul' β _ _ (tangleDataStepFn_lt α ihs β hβ) ρ t

theorem foaData_tangle_lt_set (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) (t) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
    foaData_tSet_lt_equiv α ihs β hβ
    (letI : FOAData := buildStepFOAData α ihs
    TangleCoe.set t) =
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    TangleCoe.set (show Tangle β from foaData_tangle_lt_equiv α ihs β hβ t)) :=
  tangleData_cast_set β _ _ (tangleDataStepFn_lt α ihs β hβ) _

theorem foaData_tangle_lt_support (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) (t) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
    (letI : FOAData := buildStepFOAData α ihs
    t.support) =
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    (foaData_tangle_lt_equiv α ihs β hβ t).support) :=
  tangleData_cast_support β _ _ (tangleDataStepFn_lt α ihs β hβ) _

@[simp]
theorem foaData_tSet_lt_equiv_pos (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) (t) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
    pos t = (ihs β hβ).pos ((ihs β hβ).tangleEquiv (foaData_tangle_lt_equiv α ihs β hβ t)) :=
  positionedTangles_cast_pos β _ _ (tangleDataStepFn_lt α ihs β hβ) _ _
    (buildStepFOAData_positioned_lt α ihs β hβ) t

@[simp]
theorem foaData_tSet_lt_equiv_typedAtom (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) (a : Atom) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
    (letI : FOAData := buildStepFOAData α ihs; typedAtom a) =
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    (foaData_tSet_lt_equiv α ihs β hβ).symm ((ihs β hβ).typedAtom a)) := by
  have := typedObjects_cast_typedAtom β _ _ (tangleDataStepFn_lt α ihs β hβ) _ _
    (heq_of_cast_eq _ (typedObjectsStepFn_lt α ihs β hβ).symm).symm a
  erw [this]
  simp only [foaData_tSet_lt_equiv, Equiv.cast_symm, Equiv.cast_apply, cast_cast, cast_eq]

@[simp]
theorem foaData_tSet_lt_equiv_typedNearLitter (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) (N : NearLitter) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
    (letI : FOAData := buildStepFOAData α ihs; typedNearLitter N) =
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    (foaData_tSet_lt_equiv α ihs β hβ).symm ((ihs β hβ).typedNearLitter N)) := by
  have := typedObjects_cast_typedNearLitter β _ _ (tangleDataStepFn_lt α ihs β hβ) _ _
    (heq_of_cast_eq _ (typedObjectsStepFn_lt α ihs β hβ).symm).symm N
  erw [this]
  simp only [foaData_tSet_lt_equiv, Equiv.cast_symm, Equiv.cast_apply, cast_cast, cast_eq]

@[simp]
theorem foaData_tSet_lt_equiv_fuzz (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) (γ : Λ) (hβγ : (β : TypeIndex) ≠ γ) (t) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
    (letI : FOAData := buildStepFOAData α ihs; fuzz hβγ t) =
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    fuzz hβγ (foaData_tangle_lt_equiv α ihs β hβ t)) :=
  fuzz_cast β γ hβγ _ _ (tangleDataStepFn_lt α ihs β hβ) _ _
    (buildStepFOAData_positioned_lt α ihs β hβ) _

theorem foaData_allowable_bot (α : Λ) (ihs : (β : Λ) → β < α → IH β) :
    letI : Level := ⟨α⟩
    letI : FOAData := buildStepFOAData α ihs
    Allowable ⊥ = NearLitterPerm :=
  rfl

theorem foaData_allowable_lt' (α : Λ) (ihs : (β : Λ) → β < α → IH β) (β : TypeIndex) (hβ : β < α) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨hβ⟩
    (letI : FOAData := buildStepFOAData α ihs
    Allowable β) =
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    Allowable β) := by
  revert hβ
  refine WithBot.recBotCoe ?_ ?_ β
  · intro hβ
    rfl
  · intro β hβ
    rw [foaData_allowable_lt]
    rfl

def foaData_allowable_lt'_equiv (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : TypeIndex) (hβ : β < α) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨hβ⟩
    (letI : FOAData := buildStepFOAData α ihs
    Allowable β) ≃
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    Allowable β) :=
    Equiv.cast (foaData_allowable_lt' α ihs β hβ)

theorem foaData_tSet_lt' (α : Λ) (ihs : (β : Λ) → β < α → IH β) (β : TypeIndex) (hβ : β < α) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨hβ⟩
    (letI : FOAData := buildStepFOAData α ihs
    TSet β) =
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    TSet β) := by
  revert hβ
  refine WithBot.recBotCoe ?_ ?_ β
  · intro hβ
    rfl
  · intro β hβ
    rw [foaData_tSet_lt]
    rfl

def foaData_tSet_lt'_equiv (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : TypeIndex) (hβ : β < α) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨hβ⟩
    (letI : FOAData := buildStepFOAData α ihs
    TSet β) ≃
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    TSet β) :=
    Equiv.cast (foaData_tSet_lt' α ihs β hβ)

theorem foaData_tangle_lt' (α : Λ) (ihs : (β : Λ) → β < α → IH β) (β : TypeIndex) (hβ : β < α) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨hβ⟩
    (letI : FOAData := buildStepFOAData α ihs
    Tangle β) =
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    Tangle β) := by
  revert hβ
  refine WithBot.recBotCoe ?_ ?_ β
  · intro hβ
    rfl
  · intro β hβ
    rw [foaData_tangle_lt]
    exact coe_lt_coe.mp hβ

def foaData_tangle_lt'_equiv (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : TypeIndex) (hβ : β < α) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨hβ⟩
    (letI : FOAData := buildStepFOAData α ihs
    Tangle β) ≃
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    Tangle β) :=
    Equiv.cast (foaData_tangle_lt' α ihs β hβ)

@[simp]
def foaData_allowable_lt'_equiv_eq_lt_equiv (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) :
    foaData_allowable_lt'_equiv α ihs β (coe_lt_coe.mpr hβ) =
    foaData_allowable_lt_equiv α ihs β hβ := rfl

@[simp]
def foaData_allowable_lt'_equiv_eq_refl (α : Λ) (ihs : (β : Λ) → β < α → IH β) :
    foaData_allowable_lt'_equiv α ihs ⊥ (bot_lt_coe _) = Equiv.refl _ := rfl

@[simp]
def foaData_tangle_lt'_equiv_eq_lt_equiv (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) :
    foaData_tangle_lt'_equiv α ihs β (coe_lt_coe.mpr hβ) =
    foaData_tangle_lt_equiv α ihs β hβ := rfl

@[simp]
def foaData_tangle_lt'_equiv_eq_refl (α : Λ) (ihs : (β : Λ) → β < α → IH β) :
    foaData_tangle_lt'_equiv α ihs ⊥ (bot_lt_coe _) = Equiv.refl _ := rfl

@[simp]
theorem foaData_allowable_lt'_equiv_one (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : TypeIndex) (hβ : β < α) :
    foaData_allowable_lt'_equiv α ihs β hβ 1 = 1 := by
  revert hβ
  refine WithBot.recBotCoe ?_ ?_ β
  · intro hβ
    rfl
  · intro β hβ
    rw [foaData_allowable_lt'_equiv_eq_lt_equiv α ihs β (coe_lt_coe.mp hβ)]
    exact foaData_allowable_lt_equiv_one α ihs β (coe_lt_coe.mp hβ)

@[simp]
theorem foaData_allowable_lt'_equiv_mul (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : TypeIndex) (hβ : β < α) (ρ₁ ρ₂) :
    foaData_allowable_lt'_equiv α ihs β hβ (ρ₁ * ρ₂) =
    foaData_allowable_lt'_equiv α ihs β hβ ρ₁ * foaData_allowable_lt'_equiv α ihs β hβ ρ₂ := by
  revert hβ
  refine WithBot.recBotCoe ?_ ?_ β
  · intro hβ
    simp only [foaData_allowable_lt'_equiv_eq_refl, Equiv.refl_apply, forall_const]
  · intro β hβ
    simp only [foaData_allowable_lt'_equiv_eq_lt_equiv α ihs β (coe_lt_coe.mp hβ)]
    exact foaData_allowable_lt_equiv_mul α ihs β (coe_lt_coe.mp hβ)

@[simp]
theorem foaData_allowable_lt'_equiv_toStructPerm (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : TypeIndex) (hβ : β < α) (ρ) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨hβ⟩
    (letI : FOAData := buildStepFOAData α ihs
    Allowable.toStructPerm ρ) =
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    Allowable.toStructPerm (foaData_allowable_lt'_equiv α ihs β hβ ρ)) := by
  revert hβ
  refine WithBot.recBotCoe ?_ ?_ β
  · intro hβ
    simp only [foaData_allowable_lt'_equiv_eq_refl, Equiv.refl_apply, forall_const]
  · intro β hβ
    simp only [foaData_allowable_lt'_equiv_eq_lt_equiv α ihs β (coe_lt_coe.mp hβ)]
    exact foaData_allowable_lt_equiv_toStructPerm α ihs β (coe_lt_coe.mp hβ)

@[simp]
theorem foaData_allowable_lt'_equiv_smul (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : TypeIndex) (hβ : β < α) (ρ t) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨hβ⟩
    foaData_tangle_lt'_equiv α ihs β hβ
    (letI : FOAData := buildStepFOAData α ihs; ρ • t) =
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    foaData_allowable_lt'_equiv α ihs β hβ ρ • foaData_tangle_lt'_equiv α ihs β hβ t) := by
  revert hβ
  refine WithBot.recBotCoe ?_ ?_ β
  · intro hβ ρ t
    rfl
  · intro β hβ ρ t
    rw [foaData_tangle_lt'_equiv_eq_lt_equiv α ihs β (coe_lt_coe.mp hβ)]
    exact foaData_allowable_lt_equiv_smul' α ihs β (coe_lt_coe.mp hβ) ρ t

@[simp]
theorem foaData_tangle_lt'_equiv_fuzz (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : TypeIndex) (hβ : β < α) (γ : Λ) (hβγ : β ≠ γ) (t) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨hβ⟩
    (letI : FOAData := buildStepFOAData α ihs; fuzz hβγ t) =
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : PositionedTangles β := PositionedTanglesLt.toPositionedTangles β
    fuzz hβγ (foaData_tangle_lt'_equiv α ihs β hβ t)) := by
  revert hβ hβγ
  refine WithBot.recBotCoe ?_ ?_ β
  · intro hβ hβγ t
    rfl
  · intro β hβ hβγ t
    rw [foaData_tangle_lt'_equiv_eq_lt_equiv α ihs β (coe_lt_coe.mp hβ)]
    exact foaData_tSet_lt_equiv_fuzz α ihs β (coe_lt_coe.mp hβ) γ hβγ t

-- TODO: Add `support` and `smul` lemmas.

/-- The hypotheses on how `IH` relates to previous `IH`s. -/
structure IHProp (α : Λ) (ih : ∀ β ≤ α, IH β) : Prop where
  canCons (β : Λ) (hβ : β < α) :
    ∃ f : (ih α le_rfl).Allowable →* (ih β hβ.le).Allowable,
    ∀ ρ : (ih α le_rfl).Allowable,
      Tree.comp (Hom.toPath (coe_lt_coe.mpr hβ))
        ((ih α le_rfl).allowableToStructPerm ρ) =
        (ih β hβ.le).allowableToStructPerm (f ρ)
  canConsBot :
    ∃ f : (ih α le_rfl).Allowable →* NearLitterPerm,
    ∀ ρ : (ih α le_rfl).Allowable,
      (ih α le_rfl).allowableToStructPerm ρ (Hom.toPath (bot_lt_coe _)) = f ρ
  pos_lt_pos_atom (t : (ih α le_rfl).Tangle)
    {A : ExtendedIndex α} {a : Atom}
    (ht : letI := (ih α le_rfl).tangleData; ⟨A, inl a⟩ ∈ t.support) :
    letI : Level := ⟨α⟩
    letI := (ih α le_rfl).tangleData
    TangleCoe.set t ≠ (ih α le_rfl).typedAtom a →
    pos a < (ih α le_rfl).pos ((ih α le_rfl).tangleEquiv t)
  pos_lt_pos_nearLitter (t : (ih α le_rfl).Tangle)
    {A : ExtendedIndex α} {N : NearLitter}
    (ht : letI := (ih α le_rfl).tangleData; ⟨A, inr N⟩ ∈ t.support) :
    letI : Level := ⟨α⟩
    letI := (ih α le_rfl).tangleData
    TangleCoe.set t ≠ (ih α le_rfl).typedNearLitter N →
    pos N < (ih α le_rfl).pos ((ih α le_rfl).tangleEquiv t)
  smul_fuzz (β : Λ) (hβ : β < α) (γ : Λ) (hγ : γ < α) (hβγ : (β : TypeIndex) ≠ γ)
    (ρ : (ih α le_rfl).Allowable) (t : (ih β hβ.le).Tangle)
    (fαβ : (ih α le_rfl).Allowable → (ih β hβ.le).Allowable)
    (hfαβ : ∀ ρ : (ih α le_rfl).Allowable,
      Tree.comp (Hom.toPath (coe_lt_coe.mpr hβ)) ((ih α le_rfl).allowableToStructPerm ρ) =
      (ih β hβ.le).allowableToStructPerm (fαβ ρ)) :
    (ih α le_rfl).allowableToStructPerm ρ ((Hom.toPath (coe_lt_coe.mpr hγ)).cons (bot_lt_coe _)) •
      fuzz' (ih β hβ.le) (ih γ hγ.le) hβγ t =
    fuzz' (ih β hβ.le) (ih γ hγ.le) hβγ (fαβ ρ • t)
  smul_fuzz_bot (γ : Λ) (hγ : γ < α)
    (ρ : (ih α le_rfl).Allowable) (t : Atom) :
    (ih α le_rfl).allowableToStructPerm ρ
      ((Hom.toPath (coe_lt_coe.mpr hγ)).cons (bot_lt_coe _)) • fuzz'Bot (ih γ hγ.le) t =
    fuzz'Bot (ih γ hγ.le)
      ((ih α le_rfl).allowableToStructPerm ρ (Hom.toPath (bot_lt_coe _)) • t)
  allowable_of_smulFuzz
    (ρs : ∀ (β : Λ) (hβ : β < α), (ih β hβ.le).Allowable) (π : NearLitterPerm)
    (hρs : ∀ (β : Λ) (hβ : β < α) (γ : Λ) (hγ : γ < α) (hβγ : (β : TypeIndex) ≠ γ)
      (t : (ih β hβ.le).Tangle),
      (ih γ hγ.le).allowableToStructPerm (ρs γ hγ) (Hom.toPath (bot_lt_coe _)) •
        fuzz' (ih β hβ.le) (ih γ hγ.le) hβγ t =
      fuzz' (ih β hβ.le) (ih γ hγ.le) hβγ (ρs β hβ • t))
    (hπ : ∀ (γ : Λ) (hγ : γ < α) (t : Atom),
      (ih γ hγ.le).allowableToStructPerm (ρs γ hγ)
        (Hom.toPath (bot_lt_coe _)) • fuzz'Bot (ih γ hγ.le) t =
      fuzz'Bot (ih γ hγ.le) (π • t)) :
    ∃ ρ : (ih α le_rfl).Allowable,
    (∀ (β : Λ) (hβ : β < α) (fαβ : (ih α le_rfl).Allowable → (ih β hβ.le).Allowable)
      (_hfαβ : ∀ ρ : (ih α le_rfl).Allowable,
        Tree.comp (Hom.toPath (coe_lt_coe.mpr hβ)) ((ih α le_rfl).allowableToStructPerm ρ) =
        (ih β hβ.le).allowableToStructPerm (fαβ ρ)),
      fαβ ρ = ρs β hβ) ∧
    (∀ (fα : (ih α le_rfl).Allowable → NearLitterPerm)
      (_hfα : ∀ ρ : (ih α le_rfl).Allowable,
        (ih α le_rfl).allowableToStructPerm ρ (Hom.toPath (bot_lt_coe _)) = fα ρ),
      fα ρ = π)
  eq_toPretangle_of_mem (β : Λ) (hβ : β < α) (t₁ : (ih α le_rfl).TSet) (t₂ : Pretangle β) :
    t₂ ∈ Pretangle.ofCoe ((ih α le_rfl).toPretangle t₁) β (coe_lt_coe.mpr hβ) →
    ∃ t₂' : (ih β hβ.le).TSet, t₂ = (ih β hβ.le).toPretangle t₂'
  toPretangle_ext (β : Λ) (hβ : β < α) (t₁ t₂ : (ih α le_rfl).TSet) :
    (∀ t : Pretangle β,
      t ∈ Pretangle.ofCoe ((ih α le_rfl).toPretangle t₁) β (coe_lt_coe.mpr hβ) ↔
      t ∈ Pretangle.ofCoe ((ih α le_rfl).toPretangle t₂) β (coe_lt_coe.mpr hβ)) →
    (ih α le_rfl).toPretangle t₁ = (ih α le_rfl).toPretangle t₂
  /-- It's useful to keep this `Prop`-valued, because then there is no data in `IH` that
  crosses levels. -/
  has_singletons (β : Λ) (hβ : β < α) :
    ∃ S : (ih β hβ.le).TSet → (ih α le_rfl).TSet,
    ∀ t : (ih β hβ.le).TSet,
      Pretangle.ofCoe ((ih α le_rfl).toPretangle (S t)) β (coe_lt_coe.mpr hβ) =
      {(ih β hβ.le).toPretangle t}
  step_zero : zeroTangleData = (ih 0 (Params.Λ_zero_le α)).tangleData

def newAllowableCons (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (γ : TypeIndex) [letI : Level := ⟨α⟩; LeLevel γ] (hγ : γ < α) :
    letI : Level := ⟨α⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
    letI : FOAData := buildStepFOAData α ihs
    NewAllowable → Allowable γ :=
  fun ρ =>
    letI : Level := ⟨α⟩
    letI : LtLevel γ := ⟨hγ⟩
    (foaData_allowable_lt'_equiv α ihs γ hγ).symm (ρ.val γ)

@[simp]
theorem newAllowableCons_map_one (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (γ : TypeIndex) [letI : Level := ⟨α⟩; LeLevel γ] (hγ : γ < α) :
    newAllowableCons α ihs γ hγ 1 = 1 := by
  simp only [newAllowableCons, NewAllowable.coe_one, SemiallowablePerm.one_apply,
    Equiv.symm_apply_eq, foaData_allowable_lt'_equiv_one]

@[simp]
theorem newAllowableCons_map_mul (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (γ : TypeIndex) [letI : Level := ⟨α⟩; LeLevel γ] (hγ : γ < α) (ρ₁ ρ₂) :
    newAllowableCons α ihs γ hγ (ρ₁ * ρ₂) =
    newAllowableCons α ihs γ hγ ρ₁ * newAllowableCons α ihs γ hγ ρ₂ := by
  simp only [newAllowableCons, NewAllowable.coe_mul, SemiallowablePerm.mul_apply,
    Equiv.symm_apply_eq, foaData_allowable_lt'_equiv_mul, Equiv.apply_symm_apply]

theorem newAllowableCons_toStructPerm (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (γ : TypeIndex) [letI : Level := ⟨α⟩; LtLevel γ] (hγ : γ < α)
    (ρ :
      letI : Level := ⟨α⟩
      letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
      letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
      letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
      NewAllowable) :
    letI : Level := ⟨α⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
    letI : FOAData := buildStepFOAData α ihs
    Tree.comp (Hom.toPath hγ) (NewAllowable.toStructPerm ρ) =
    Allowable.toStructPerm (newAllowableCons α ihs γ hγ ρ) := by
  letI : Level := ⟨α⟩
  letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
  letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
  letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
  rw [newAllowableCons, NewAllowable.comp_toPath_toStructPerm ρ γ,
    foaData_allowable_lt'_equiv_toStructPerm _ _ _ hγ, Equiv.apply_symm_apply]

theorem can_allowableConsStep (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ)))
    (β : TypeIndex) [iβ : letI : Level := ⟨α⟩; LeLevel β]
    (γ : TypeIndex) [iγ : letI : Level := ⟨α⟩; LeLevel γ] (hγ : γ < β) :
    letI : Level := ⟨α⟩
    letI : FOAData := buildStepFOAData α ihs
    ∃ f : Allowable β →* Allowable γ,
    ∀ ρ : Allowable β,
      Tree.comp (Hom.toPath hγ) (Allowable.toStructPerm ρ) = Allowable.toStructPerm (f ρ) := by
  by_cases hβ : β = α
  · cases hβ
    refine ⟨⟨⟨newAllowableCons α ihs γ hγ ∘ foaData_allowable_eq_equiv α ihs, ?_⟩, ?_⟩, ?_⟩
    · simp only [comp_apply, foaData_allowable_eq_equiv_one, newAllowableCons_map_one]
    · simp only [comp_apply, foaData_allowable_eq_equiv_mul, newAllowableCons_map_mul,
        forall_const]
    · intro ρ
      letI : Level := ⟨α⟩
      letI : LtLevel γ := ⟨hγ⟩
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, comp_apply]
      rw [← newAllowableCons_toStructPerm α ihs γ hγ (foaData_allowable_eq_equiv α ihs ρ),
        foaData_allowable_eq_equiv_toStructPerm]
  revert iβ iγ hγ hβ
  letI : Level := ⟨α⟩
  letI : FOAData := buildStepFOAData α ihs
  refine WithBot.recBotCoe ?_ ?_ β
  · intro iβ iγ hγ
    cases not_lt_bot hγ
  · intro β
    refine WithBot.recBotCoe ?_ ?_ γ
    · intro iβ iγ hγ hβ
      have hβ' := lt_of_le_of_ne (coe_le_coe.mp iβ.elim) (coe_ne_coe.mp hβ)
      obtain ⟨f, hf⟩ := (h β hβ').canConsBot
      refine ⟨⟨⟨f ∘ foaData_allowable_lt_equiv α ihs β hβ', ?_⟩, ?_⟩, ?_⟩
      · simp only [comp_apply, foaData_allowable_lt_equiv_one, map_one]
      · simp only [comp_apply, foaData_allowable_lt_equiv_mul, map_mul, forall_const]
      · intro ρ
        have := hf (foaData_allowable_lt_equiv α ihs β hβ' ρ)
        erw [← foaData_allowable_lt_equiv_toStructPerm α ihs β hβ' ρ] at this
        simp only [Tree.comp_bot, MonoidHom.coe_mk, OneHom.coe_mk, comp_apply, gt_iff_lt,
          bot_lt_coe, foaData_allowable_lt'_equiv_toStructPerm, foaData_allowable_lt'_equiv_eq_refl,
          Equiv.refl_apply]
        rw [this]
        rfl
    · intro γ iβ iγ hγ hβ
      have hβ' := lt_of_le_of_ne (coe_le_coe.mp iβ.elim) (coe_ne_coe.mp hβ)
      obtain ⟨f, hf⟩ := (h β hβ').canCons γ (coe_lt_coe.mp hγ)
      refine ⟨⟨⟨(foaData_allowable_lt_equiv α ihs γ ((coe_lt_coe.mp hγ).trans hβ')).symm ∘ f ∘
        foaData_allowable_lt_equiv α ihs β hβ', ?_⟩, ?_⟩, ?_⟩
      · simp only [comp_apply, foaData_allowable_lt_equiv_one, map_one, Equiv.symm_apply_eq]
      · simp only [comp_apply, foaData_allowable_lt_equiv_mul, map_mul, Equiv.symm_apply_eq,
          Equiv.apply_symm_apply, forall_const]
      · intro ρ
        have := hf (foaData_allowable_lt_equiv α ihs β hβ' ρ)
        erw [← foaData_allowable_lt_equiv_toStructPerm α ihs β hβ' ρ] at this
        rw [this]
        simp only [MonoidHom.coe_mk, OneHom.coe_mk, comp_apply]
        rw [foaData_allowable_lt_equiv_toStructPerm α ihs γ ((coe_lt_coe.mp hγ).trans hβ'),
          Equiv.apply_symm_apply]
        rfl

noncomputable def allowableConsStep (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ)))
    (β : TypeIndex) [letI : Level := ⟨α⟩; LeLevel β]
    (γ : TypeIndex) [letI : Level := ⟨α⟩; LeLevel γ] (hγ : γ < β) :
    letI : Level := ⟨α⟩
    letI : FOAData := buildStepFOAData α ihs
    Allowable β →* Allowable γ :=
  (can_allowableConsStep α ihs h β γ hγ).choose

theorem allowableConsStep_eq (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ)))
    (β : TypeIndex) [letI : Level := ⟨α⟩; LeLevel β]
    (γ : TypeIndex) [letI : Level := ⟨α⟩; LeLevel γ] (hγ : γ < β) (ρ) :
    letI : Level := ⟨α⟩
    letI : FOAData := buildStepFOAData α ihs
    Tree.comp (Hom.toPath hγ) (Allowable.toStructPerm ρ) =
    Allowable.toStructPerm (allowableConsStep α ihs h β γ hγ ρ) :=
  (can_allowableConsStep α ihs h β γ hγ).choose_spec ρ

theorem pos_lt_pos_atom_step (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ)))
    (β : Λ) [iβ : letI : Level := ⟨α⟩; LtLevel β]
    (t :
      letI : Level := ⟨α⟩
      letI : FOAData := buildStepFOAData α ihs
      Tangle β)
    {A : ExtendedIndex β} {a : Atom} :
    letI : Level := ⟨α⟩
    letI : FOAData := buildStepFOAData α ihs
    ⟨A, inl a⟩ ∈ t.support →
    t.set ≠ typedAtom a → pos a < pos t := by
  intro hc hta
  letI : Level := ⟨α⟩
  letI : FOAData := buildStepFOAData α ihs
  have hβ := coe_lt_coe.mp iβ.elim
  have := (h β hβ).pos_lt_pos_atom (foaData_tangle_lt_equiv α ihs β hβ t) (A := A) (a := a) ?_ ?_
  · rw [foaData_tSet_lt_equiv_pos α ihs β hβ t]
    exact this
  · rw [foaData_tangle_lt_support α ihs β hβ t] at hc
    exact hc
  · rw [foaData_tSet_lt_equiv_typedAtom α ihs β hβ a, ne_eq, Equiv.eq_symm_apply] at hta
    erw [foaData_tangle_lt_set] at hta
    exact hta

theorem pos_lt_pos_nearLitter_step (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ)))
    (β : Λ) [iβ : letI : Level := ⟨α⟩; LtLevel β]
    (t :
      letI : Level := ⟨α⟩
      letI : FOAData := buildStepFOAData α ihs
      Tangle β)
    {A : ExtendedIndex β} {N : NearLitter} :
    letI : Level := ⟨α⟩
    letI : FOAData := buildStepFOAData α ihs
    ⟨A, inr N⟩ ∈ t.support →
    t.set ≠ typedNearLitter N → pos N < pos t := by
  intro hc hta
  letI : Level := ⟨α⟩
  letI : FOAData := buildStepFOAData α ihs
  have hβ := coe_lt_coe.mp iβ.elim
  have := (h β hβ).pos_lt_pos_nearLitter (foaData_tangle_lt_equiv α ihs β hβ t)
      (A := A) (N := N) ?_ ?_
  · rw [foaData_tSet_lt_equiv_pos α ihs β hβ t]
    exact this
  · rw [foaData_tangle_lt_support α ihs β hβ t] at hc
    exact hc
  · rw [foaData_tSet_lt_equiv_typedNearLitter α ihs β hβ N, ne_eq, Equiv.eq_symm_apply] at hta
    erw [foaData_tangle_lt_set] at hta
    exact hta

theorem allowableConsStep_eq_lt (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ)))
    (β : Λ) (hβ : β < α)
    (γ : Λ) (hγ : γ < α)
    (hγβ : γ < β) (ρ : (ihs β hβ).Allowable) :
    letI : Level := ⟨α⟩
    letI : LeLevel β := ⟨coe_le_coe.mpr hβ.le⟩
    letI : LeLevel γ := ⟨coe_le_coe.mpr hγ.le⟩
    Tree.comp (Hom.toPath (coe_lt_coe.mpr hγβ)) ((ihs β hβ).allowableToStructPerm ρ) =
    (ihs γ hγ).allowableToStructPerm
    (foaData_allowable_lt_equiv α ihs γ hγ <| allowableConsStep α ihs h β γ (coe_lt_coe.mpr hγβ) <|
      (foaData_allowable_lt_equiv α ihs β hβ).symm ρ) := by
  letI : Level := ⟨α⟩
  letI : LeLevel β := ⟨coe_le_coe.mpr hβ.le⟩
  letI : LeLevel γ := ⟨coe_le_coe.mpr hγ.le⟩
  have := foaData_allowable_lt_equiv_toStructPerm α ihs β hβ
    ((foaData_allowable_lt_equiv α ihs β hβ).symm ρ)
  rw [Equiv.apply_symm_apply] at this
  erw [← this]
  rw [allowableConsStep_eq α ihs h β γ (coe_lt_coe.mpr hγβ)
    ((foaData_allowable_lt_equiv α ihs β hβ).symm ρ)]
  have := foaData_allowable_lt_equiv_toStructPerm α ihs γ hγ
  erw [← this]

theorem allowableConsStep_eq_eq (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ)))
    (γ : Λ) (hγ : γ < α) (ρ) :
    letI : Level := ⟨α⟩
    letI : LeLevel α := ⟨le_rfl⟩
    letI : LtLevel γ := ⟨coe_lt_coe.mpr hγ⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    (foaData_allowable_eq_equiv α ihs ρ : SemiallowablePerm) γ =
    foaData_allowable_lt_equiv α ihs γ hγ
      (allowableConsStep α ihs h α γ (coe_lt_coe.mpr hγ) ρ) := by
  letI : Level := ⟨α⟩
  letI : LeLevel α := ⟨le_rfl⟩
  letI : LtLevel γ := ⟨coe_lt_coe.mpr hγ⟩
  letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
  letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
  refine (ihs γ hγ).allowableToStructPerm_injective ?_
  have := allowableConsStep_eq α ihs h α γ (coe_lt_coe.mpr hγ) ρ
  rw [foaData_allowable_eq_equiv_toStructPerm,
    NewAllowable.comp_toPath_toStructPerm (foaData_allowable_eq_equiv α ihs ρ) γ,
    foaData_allowable_lt_equiv_toStructPerm] at this
  exact this

theorem allowableConsStep_eq_eq' (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ)))
    (γ : TypeIndex) (hγ : γ < α) (ρ) :
    letI : Level := ⟨α⟩
    letI : LeLevel α := ⟨le_rfl⟩
    letI : LtLevel γ := ⟨hγ⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    (foaData_allowable_eq_equiv α ihs ρ : SemiallowablePerm) γ =
    foaData_allowable_lt'_equiv α ihs γ hγ (allowableConsStep α ihs h α γ hγ ρ) := by
  revert hγ
  refine WithBot.recBotCoe ?_ ?_ γ
  · intro hγ
    letI : Level := ⟨α⟩
    letI : LeLevel α := ⟨le_rfl⟩
    have := congr_fun (allowableConsStep_eq α ihs h α ⊥ (bot_lt_coe _) ρ) Path.nil
    rw [Tree.comp_apply, Path.comp_nil, foaData_allowable_eq_equiv_toStructPerm α ihs] at this
    exact this
  · intro γ hγ
    rw [foaData_allowable_lt'_equiv_eq_lt_equiv, allowableConsStep_eq_eq]
    rfl

theorem smul_fuzz_step (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ)))
    (β : TypeIndex) [iβ : letI : Level := ⟨α⟩; LeLevel β]
    (γ : TypeIndex) [iγ : letI : Level := ⟨α⟩; LtLevel γ]
    (δ : Λ) [iδ : letI : Level := ⟨α⟩; LtLevel δ]
    (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
    (ρ :
      letI : Level := ⟨α⟩
      letI : FOAData := buildStepFOAData α ihs
      Allowable β)
    (t :
      letI : Level := ⟨α⟩
      letI : FOAData := buildStepFOAData α ihs
      Tangle γ) :
    letI : Level := ⟨α⟩
    letI : FOAData := buildStepFOAData α ihs
    Allowable.toStructPerm ρ ((Hom.toPath hδ).cons (bot_lt_coe _)) • fuzz hγδ t =
    fuzz hγδ (allowableConsStep α ihs h β γ hγ ρ • t) := by
  revert iβ γ δ ihs
  refine WithBot.recBotCoe ?_ ?_ β
  · intro ihs h iβ γ iγ δ _ hγ
    simp only [not_lt_bot] at hγ
  intro β ihs h iβ γ
  revert ihs h
  refine WithBot.recBotCoe ?_ ?_ γ
  · intro ihs h iγ δ iδ hγ hδ hγδ ρ a
    letI : Level := ⟨α⟩
    letI : FOAData := buildStepFOAData α ihs
    by_cases hβ : β = α
    · cases hβ
      rw [foaData_allowable_eq_equiv_toStructPerm]
      erw [(foaData_allowable_eq_equiv α ihs ρ).prop hγδ a]
      refine congr_arg _ ?_
      change _ = (Allowable.toStructPerm (allowableConsStep α ihs h α ⊥ hγ ρ)) • (show Atom from a)
      rw [← allowableConsStep_eq α ihs h α ⊥ (bot_lt_coe _) ρ]
      simp only [Tree.comp_bot, Tree.toBot_smul]
      rw [foaData_allowable_eq_equiv_toStructPerm α ihs ρ]
      rfl
    · have hβ' := lt_of_le_of_ne (coe_le_coe.mp iβ.elim) hβ
      rw [foaData_allowable_lt_equiv_toStructPerm α ihs β hβ' ρ]
      erw [(h β hβ').smul_fuzz_bot δ (coe_lt_coe.mp hδ)
        (foaData_allowable_lt_equiv α ihs β hβ' ρ) a]
      rw [fuzz'Bot]
      refine congr_arg _ ?_
      change _ = (Allowable.toStructPerm (allowableConsStep α ihs h β ⊥ hγ ρ)) • (show Atom from a)
      rw [← allowableConsStep_eq α ihs h β ⊥ (bot_lt_coe _) ρ]
      simp only [Tree.comp_bot, Tree.toBot_smul]
      rw [foaData_allowable_lt_equiv_toStructPerm α ihs β hβ' ρ]
      rfl
  · intro γ ihs h iγ δ iδ hγ hδ hγδ ρ t
    letI : Level := ⟨α⟩
    letI : FOAData := buildStepFOAData α ihs
    by_cases hβ : β = α
    · cases hβ
      have hγ' := coe_lt_coe.mp (hγ.trans_le iβ.elim)
      rw [foaData_allowable_eq_equiv_toStructPerm α ihs ρ,
        foaData_tSet_lt_equiv_fuzz α ihs γ hγ' δ hγδ t]
      erw [(foaData_allowable_eq_equiv α ihs ρ).prop hγδ (foaData_tangle_lt_equiv α ihs γ hγ' t)]
      rw [foaData_tSet_lt_equiv_fuzz α ihs γ hγ' δ hγδ,
        foaData_allowable_lt_equiv_smul',
        allowableConsStep_eq_eq α ihs h γ hγ' ρ]
    · have hβ' := lt_of_le_of_ne (coe_le_coe.mp iβ.elim) hβ
      have hγ' := coe_lt_coe.mp (hγ.trans_le iβ.elim)
      rw [foaData_allowable_lt_equiv_toStructPerm α ihs β hβ' ρ,
        foaData_tSet_lt_equiv_fuzz α ihs γ hγ' δ hγδ t]
      erw [(h β hβ').smul_fuzz γ (coe_lt_coe.mp hγ) δ (coe_lt_coe.mp hδ) hγδ
        (foaData_allowable_lt_equiv α ihs β hβ' ρ)
        (foaData_tangle_lt_equiv α ihs γ hγ' t)
        (foaData_allowable_lt_equiv α ihs γ hγ' ∘ allowableConsStep α ihs h β γ hγ ∘
          (foaData_allowable_lt_equiv α ihs β hβ').symm)
        (allowableConsStep_eq_lt α ihs h β hβ' γ hγ' (coe_lt_coe.mp hγ))]
      rw [foaData_tSet_lt_equiv_fuzz α ihs γ hγ' δ hγδ,
        foaData_allowable_lt_equiv_smul']
      simp only [comp_apply, Equiv.symm_apply_apply]
      rfl

theorem allowable_of_smulFuzz_step (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ)))
    (β : Λ) [iβ : letI : Level := ⟨α⟩; LeLevel β]
    (ρs :
      letI : Level := ⟨α⟩
      letI : FOAData := buildStepFOAData α ihs
      (γ : TypeIndex) → [LtLevel γ] → γ < β → Allowable γ)
    (hρs :
      letI : Level := ⟨α⟩
      letI : FOAData := buildStepFOAData α ihs
      ∀ (γ : TypeIndex) [LtLevel γ] (δ : Λ) [LtLevel δ]
        (hγ : γ < β) (hδ : (δ : TypeIndex) < β) (hγδ : γ ≠ δ) (t : Tangle γ),
        Allowable.toStructPerm (ρs δ hδ) (Hom.toPath (bot_lt_coe _)) • fuzz hγδ t =
          fuzz hγδ (ρs γ hγ • t)) :
    letI : Level := ⟨α⟩
    letI : FOAData := buildStepFOAData α ihs
    ∃ ρ : Allowable β, ∀ (γ : TypeIndex) [LtLevel γ] (hγ : γ < β),
    allowableConsStep α ihs h β γ hγ ρ = ρs γ hγ := by
  letI : Level := ⟨α⟩
  letI : FOAData := buildStepFOAData α ihs
  by_cases hβ : β = α
  · cases hβ
    have hρ :
      letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
      letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
      SemiallowablePerm.IsAllowable
        (fun γ hγ => foaData_allowable_lt'_equiv α ihs γ hγ.elim (ρs γ hγ.elim))
    · intro γ iγ δ iδ hγδ t
      have := hρs γ δ iγ.elim iδ.elim hγδ ((foaData_tangle_lt'_equiv α ihs γ iγ.elim).symm t)
      rw [foaData_tangle_lt'_equiv_fuzz α ihs γ iγ.elim δ hγδ,
        foaData_tangle_lt'_equiv_fuzz α ihs γ iγ.elim δ hγδ, Equiv.apply_symm_apply,
        foaData_allowable_lt'_equiv_toStructPerm α ihs δ iδ.elim,
        foaData_allowable_lt'_equiv_smul α ihs γ iγ.elim,
        Equiv.apply_symm_apply] at this
      exact this
    refine ⟨(foaData_allowable_eq_equiv α ihs).symm ⟨_, hρ⟩, ?_⟩
    intro γ iγ hγ
    have := allowableConsStep_eq_eq' α ihs h γ hγ ((foaData_allowable_eq_equiv α ihs).symm ⟨_, hρ⟩)
    simp only [Equiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq] at this
    exact this.symm
  · have hβ' := lt_of_le_of_ne (coe_le_coe.mp iβ.elim) hβ
    have := (h β hβ').allowable_of_smulFuzz
        (fun γ hγ =>
          letI : LtLevel γ := ⟨coe_lt_coe.mpr (hγ.trans hβ')⟩
          foaData_allowable_lt_equiv α ihs γ (hγ.trans hβ') (ρs γ (coe_lt_coe.mpr hγ)))
        (ρs ⊥ (bot_lt_coe _)) ?_ ?_
    · obtain ⟨ρ, hρ, hρπ⟩ := this
      refine ⟨(foaData_allowable_lt_equiv α ihs β hβ').symm ρ, ?_⟩
      rintro (_ | γ) iγ hγ
      · refine hρπ (allowableConsStep α ihs h β ⊥ (bot_lt_coe _) ∘
          (foaData_allowable_lt_equiv α ihs β hβ').symm) ?_
        intro ρ'
        have := congr_fun (allowableConsStep_eq α ihs h β ⊥ (bot_lt_coe _)
          ((foaData_allowable_lt_equiv α ihs β hβ').symm ρ')) Path.nil
        rw [Tree.comp_apply, Path.comp_nil,
          foaData_allowable_lt_equiv_toStructPerm α ihs β hβ',
          Equiv.apply_symm_apply] at this
        exact this
      · have hγ' := coe_lt_coe.mp hγ
        have := hρ γ hγ'
            (foaData_allowable_lt_equiv α ihs γ (hγ'.trans hβ') ∘
              allowableConsStep α ihs h β γ hγ ∘
              (foaData_allowable_lt_equiv α ihs β hβ').symm) ?_
        · simp only [comp_apply, EmbeddingLike.apply_eq_iff_eq] at this
          exact this
        · intro ρ'
          rw [allowableConsStep_eq_lt α ihs h β hβ' γ (hγ'.trans hβ') hγ']
          rfl
    · intro γ hγ δ hδ hγδ t
      haveI : LtLevel γ := ⟨coe_lt_coe.mpr (hγ.trans hβ')⟩
      haveI : LtLevel δ := ⟨coe_lt_coe.mpr (hδ.trans hβ')⟩
      have := hρs γ δ (coe_lt_coe.mpr hγ) (coe_lt_coe.mpr hδ) hγδ
        ((foaData_tangle_lt_equiv α ihs γ (hγ.trans hβ')).symm t)
      rw [foaData_tSet_lt_equiv_fuzz α ihs γ (hγ.trans hβ') δ hγδ,
        foaData_tSet_lt_equiv_fuzz α ihs γ (hγ.trans hβ') δ hγδ,
        Equiv.apply_symm_apply, foaData_allowable_lt_equiv_smul', Equiv.apply_symm_apply,
        foaData_allowable_lt_equiv_toStructPerm α ihs δ (hδ.trans hβ')] at this
      erw [this]
      rfl
    · intro δ hδ a
      haveI : LtLevel δ := ⟨coe_lt_coe.mpr (hδ.trans hβ')⟩
      have := hρs ⊥ δ (bot_lt_coe _) (coe_lt_coe.mpr hδ) bot_ne_coe a
      rw [foaData_allowable_lt_equiv_toStructPerm α ihs δ (hδ.trans hβ')] at this
      erw [this]
      rfl

noncomputable def buildStepFOAAssumptions (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ))) :
    letI : Level := ⟨α⟩
    FOAAssumptions :=
  letI : Level := ⟨α⟩
  letI : FOAData := buildStepFOAData α ihs
  {
    allowableCons := fun {β _ γ _} => allowableConsStep α ihs h β γ
    allowableCons_eq := allowableConsStep_eq α ihs h
    pos_lt_pos_atom := pos_lt_pos_atom_step α ihs h _
    pos_lt_pos_nearLitter := pos_lt_pos_nearLitter_step α ihs h _
    smul_fuzz := smul_fuzz_step α ihs h _ _ _
    allowable_of_smulFuzz := allowable_of_smulFuzz_step α ihs h
  }

theorem eq_toPretangle_of_mem_step (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ)))
    (β : Λ) [iβ : letI : Level := ⟨α⟩; LeLevel β]
    (γ : Λ) [iγ : letI : Level := ⟨α⟩; LeLevel γ]
    (hγβ : (γ : TypeIndex) < β)
    (t₁ :
      letI : Level := ⟨α⟩
      letI : FOAData := buildStepFOAData α ihs
      TSet β) :
    letI : Level := ⟨α⟩
    letI : FOAData := buildStepFOAData α ihs
    ∀ t₂ ∈ Pretangle.ofCoe (toPretangle t₁) γ hγβ, ∃ t₂', t₂ = toPretangle t₂' := by
  by_cases hβ : β = α
  · cases hβ
    intro t₂ ht₂
    erw [foaData_tSet_eq_equiv_toPretangle α ihs t₁] at ht₂
    simp only [NewTSet.toPretangle, Semitangle.toPretangle, Pretangle.ofCoe_symm, exists_and_right,
      Pretangle.ofCoe_toCoe, mem_setOf_eq] at ht₂
    obtain ⟨s, _, rfl⟩ := ht₂
    have := foaData_tSet_lt_equiv_toPretangle α ihs γ (coe_lt_coe.mp hγβ)
      ((foaData_tSet_lt_equiv α ihs γ (coe_lt_coe.mp hγβ)).symm s)
    rw [Equiv.apply_symm_apply] at this
    exact ⟨(foaData_tSet_lt_equiv α ihs γ (coe_lt_coe.mp hγβ)).symm s, this.symm⟩
  · letI : Level := ⟨α⟩
    have hβ' := lt_of_le_of_ne (coe_le_coe.mp iβ.elim) hβ
    have hγ' := coe_lt_coe.mp (hγβ.trans_le iβ.elim)
    intro t₂ ht₂
    have := (h β hβ').eq_toPretangle_of_mem γ (coe_lt_coe.mp hγβ)
        (foaData_tSet_lt_equiv α ihs β hβ' t₁) t₂ ?_
    · obtain ⟨t₂', rfl⟩ := this
      refine ⟨(foaData_tSet_lt_equiv α ihs γ hγ').symm t₂', ?_⟩
      rw [foaData_tSet_lt_equiv_toPretangle α ihs γ hγ', Equiv.apply_symm_apply]
    · rw [foaData_tSet_lt_equiv_toPretangle α ihs β hβ'] at ht₂
      exact ht₂

theorem toPretangle_ext_step (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ)))
    (β : Λ) (γ : Λ)
    [iβ : letI : Level := ⟨α⟩; LeLevel β] [letI : Level := ⟨α⟩; LeLevel γ]
    (hγβ : (γ : TypeIndex) < β)
    (t₁ t₂ :
      letI : Level := ⟨α⟩
      letI : FOAData := buildStepFOAData α ihs
      TSet β) :
    letI : Level := ⟨α⟩
    letI : FOAData := buildStepFOAData α ihs
    (∀ t : Pretangle γ, t ∈ Pretangle.ofCoe (toPretangle t₁) γ hγβ ↔
      t ∈ Pretangle.ofCoe (toPretangle t₂) γ hγβ) →
    toPretangle t₁ = toPretangle t₂ := by
  letI : Level := ⟨α⟩
  by_cases hβ : β = α
  · cases hβ
    intro ht
    erw [foaData_tSet_eq_equiv_toPretangle α ihs t₁,
      foaData_tSet_eq_equiv_toPretangle α ihs t₂] at ht ⊢
    have : LtLevel γ := ⟨hγβ⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
    letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
    have := NewTSet.ext γ (foaData_tSet_eq_equiv α ihs t₁) (foaData_tSet_eq_equiv α ihs t₂) ht
    rw [EmbeddingLike.apply_eq_iff_eq] at this
    cases this
    rfl
  · have hβ' := lt_of_le_of_ne (coe_le_coe.mp iβ.elim) hβ
    intro ht
    simp only [foaData_tSet_lt_equiv_toPretangle α ihs β hβ'] at ht ⊢
    exact (h β hβ').toPretangle_ext γ (coe_lt_coe.mp hγβ)
      (foaData_tSet_lt_equiv α ihs β hβ' t₁) (foaData_tSet_lt_equiv α ihs β hβ' t₂) ht

theorem has_singletons (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ)))
    (β : Λ) (hβ : β ≤ α) (γ : Λ) (hγβ : γ < β) :
    letI : Level := ⟨α⟩
    letI : FOAData := buildStepFOAData α ihs
    letI : LeLevel β := ⟨coe_le_coe.mpr hβ⟩
    letI : LeLevel γ := ⟨coe_le_coe.mpr (hγβ.le.trans hβ)⟩
    ∃ S : TSet γ → TSet β,
    ∀ t : TSet γ, Pretangle.ofCoe (toPretangle (S t)) γ (coe_lt_coe.mpr hγβ) = {toPretangle t} := by
  by_cases hβ' : β = α
  · cases hβ'
    letI : Level := ⟨α⟩
    have : LtLevel γ := ⟨coe_lt_coe.mpr hγβ⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
    letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
    refine ⟨(foaData_tSet_eq_equiv α ihs).symm ∘
      newSingleton γ ∘ foaData_tSet_lt_equiv α ihs γ hγβ, ?_⟩
    intro t
    have := NewTSet.newSingleton_toPretangle γ (foaData_tSet_lt_equiv α ihs γ hγβ t)
    rw [foaData_tSet_lt_equiv_toPretangle' α ihs γ hγβ, ← this]
    have := foaData_tSet_eq_equiv_toPretangle α ihs
      ((foaData_tSet_eq_equiv α ihs).symm (newSingleton γ (foaData_tSet_lt_equiv α ihs γ hγβ t)))
    rw [Equiv.apply_symm_apply] at this
    rw [← this]
    rfl
  · have hβ' := lt_of_le_of_ne hβ hβ'
    have hγ' := hγβ.trans hβ'
    obtain ⟨S, hS⟩ := (h β hβ').has_singletons γ hγβ
    refine ⟨fun t => (foaData_tSet_lt_equiv α ihs β hβ').symm
      (S (foaData_tSet_lt_equiv α ihs γ hγ' t)), ?_⟩
    intro t
    rw [foaData_tSet_lt_equiv_toPretangle α ihs β hβ', Equiv.apply_symm_apply,
      foaData_tSet_lt_equiv_toPretangle α ihs γ hγ']
    exact hS _

noncomputable def singleton_step (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ)))
    (β : Λ) (hβ : β ≤ α) (γ : Λ) (hγβ : γ < β) :
    letI : Level := ⟨α⟩
    letI : FOAData := buildStepFOAData α ihs
    letI : LeLevel β := ⟨coe_le_coe.mpr hβ⟩
    letI : LeLevel γ := ⟨coe_le_coe.mpr (hγβ.le.trans hβ)⟩
    TSet γ → TSet β :=
  (has_singletons α ihs h β hβ γ hγβ).choose

theorem singleton_step_spec (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ)))
    (β : Λ) (hβ : β ≤ α) (γ : Λ) (hγβ : γ < β) :
    letI : Level := ⟨α⟩
    letI : FOAData := buildStepFOAData α ihs
    letI : LeLevel β := ⟨coe_le_coe.mpr hβ⟩
    letI : LeLevel γ := ⟨coe_le_coe.mpr (hγβ.le.trans hβ)⟩
    ∀ t : TSet γ,
      Pretangle.ofCoe (toPretangle (singleton_step α ihs h β hβ γ hγβ t)) γ (coe_lt_coe.mpr hγβ) =
      {toPretangle t} :=
  (has_singletons α ihs h β hβ γ hγβ).choose_spec

noncomputable def buildStepCountingAssumptions (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ))) :
    letI : Level := ⟨α⟩
    CountingAssumptions :=
  letI : Level := ⟨α⟩
  letI : FOAAssumptions := buildStepFOAAssumptions α ihs h
  {
    eq_toPretangle_of_mem := eq_toPretangle_of_mem_step α ihs h
    toPretangle_ext := toPretangle_ext_step α ihs h
    singleton := fun β iβ γ _ hγβ =>
      singleton_step α ihs h β (coe_le_coe.mp iβ.elim) γ (coe_lt_coe.mp hγβ)
    singleton_toPretangle := fun β iβ γ _ hγβ =>
      singleton_step_spec α ihs h β (coe_le_coe.mp iβ.elim) γ (coe_lt_coe.mp hγβ)
  }

theorem zeroTangleData_eq (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ))) :
    zeroTangleData = tangleDataStepFn α ihs 0 (Params.Λ_zero_le α) := by
  letI : Level := ⟨α⟩
  by_cases hz : α = 0
  · cases hz
    rw [tangleDataStepFn_eq 0 ihs, zeroTangleData, tangleDataStep]
    exact zeroTangleData_subsingleton _ _ _ _ _ _ _
      (fun β hβ => ((Params.Λ_zero_le β).not_lt (coe_lt_coe.mp hβ.elim)).elim)
  · have hz := lt_of_le_of_ne (Params.Λ_zero_le α) (Ne.symm hz)
    rw [(h 0 hz).step_zero, tangleDataStepFn_lt α ihs 0 hz]

theorem mk_codingFunction_le (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ))) :
    letI : Level := ⟨α⟩
    letI : CountingAssumptions := buildStepCountingAssumptions α ihs h
    #(CodingFunction 0) < #μ := by
  convert mk_codingFunction_zero_le
  rw [zeroTangleData_eq α ihs h]
  rfl

theorem mk_tSet_step (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ))) :
    letI : Level := ⟨α⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
    letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
    #NewTSet = #μ := by
  letI : Level := ⟨α⟩
  letI : CountingAssumptions := buildStepCountingAssumptions α ihs h
  haveI : LeLevel α := ⟨le_rfl⟩
  rw [← foaData_tSet_eq]
  exact mk_tSet α (mk_codingFunction_le α ihs h)

noncomputable def posStep (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ))) :
    letI : Level := ⟨α⟩
    letI := tangleDataStep α ihs
    Tang α (TSet α) (Allowable α) → μ :=
  letI : Level := ⟨α⟩
  letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
  letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
  letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
  letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
  fun t => NewTangle.pos (mk_tSet_step α ihs h) (t.set, t.support)

theorem posStep_injective (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ))) :
    letI : Level := ⟨α⟩
    letI := tangleDataStep α ihs
    Function.Injective (posStep α ihs h) := by
  letI : Level := ⟨α⟩
  letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
  letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
  letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
  letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
  intro t₁ t₂ ht
  have := NewTangle.pos_injective (mk_tSet_step α ihs h) ht
  simp only [Prod.mk.injEq] at this
  exact Tang.ext _ _ this.1 this.2

theorem posStep_typedAtom (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ))) :
    letI : Level := ⟨α⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
    letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
    letI := tangleDataStep α ihs
    ∀ (a : Atom) (t : Tang α (TSet α) (Allowable α)),
    t.set = newTypedAtom a → pos a ≤ posStep α ihs h t := by
  letI : Level := ⟨α⟩
  letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
  letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
  letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
  letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
  intro a t ha
  have := NewTangle.pos_not_mem_deny (mk_tSet_step α ihs h) (t.set, t.support)
  contrapose! this
  refine ⟨pos a, ?_, this.le⟩
  exact Or.inl (Or.inr ⟨a, ha, rfl⟩)

theorem posStep_typedNearLitter (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ))) :
    letI : Level := ⟨α⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
    letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
    letI := tangleDataStep α ihs
    ∀ (N : NearLitter) (t : Tang α (TSet α) (Allowable α)),
    t.set = newTypedNearLitter N → pos N ≤ posStep α ihs h t := by
  letI : Level := ⟨α⟩
  letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
  letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
  letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
  letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
  intro N t hN
  have := NewTangle.pos_not_mem_deny (mk_tSet_step α ihs h) (t.set, t.support)
  contrapose! this
  refine ⟨pos N, ?_, this.le⟩
  exact Or.inr ⟨N, hN, rfl⟩

noncomputable def buildStep (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ))) : IH α :=
  letI : Level := ⟨α⟩
  letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
  letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
  letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
  letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
  letI : (β : Λ) → [LeLevel β] → TangleData β :=
    fun β hβ => tangleDataStepFn α ihs β (coe_le_coe.mp hβ.elim)
  letI : FOAData := buildStepFOAData α ihs
  {
    __ := tangleDataStep α ihs
    __ := typedObjectsStep α ihs
    pos := ⟨posStep α ihs h, posStep_injective α ihs h⟩
    pos_typedAtom := posStep_typedAtom α ihs h
    pos_typedNearLitter := posStep_typedNearLitter α ihs h
  }

noncomputable def buildStepFn (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ)))
    (β : Λ) (hβ : β ≤ α) : IH β :=
  if hβ' : β = α then
    hβ' ▸ buildStep α ihs h
  else
    ihs β (lt_of_le_of_ne hβ hβ')

theorem buildStepFn_eq (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ))) :
    buildStepFn α ihs h α le_rfl = buildStep α ihs h := by
  rw [buildStepFn, dif_pos rfl]

theorem buildStepFn_lt (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ)))
    (β : Λ) (hβ : β < α) :
    buildStepFn α ihs h β hβ.le = ihs β hβ := by
  rw [buildStepFn, dif_neg (ne_of_lt hβ)]

theorem buildStep_prop (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ))) :
    IHProp α (buildStepFn α ihs h) :=
  sorry

structure IHCumul (α : Λ) where
  ih (β : Λ) (hβ : β ≤ α) : IH β
  prop (β : Λ) (hβ : β ≤ α) : IHProp β (fun γ hγ => ih γ (hγ.trans hβ))
  ih_eq (β : Λ) (hβ : β ≤ α) : ih β hβ =
    buildStep β (fun γ hγ => ih γ (hγ.le.trans hβ)) (fun γ hγ => prop γ (hγ.le.trans hβ))

theorem ihs_eq (α : Λ) (ihs : ∀ β < α, IHCumul β)
    (β : Λ) (hβ : β < α) (γ : Λ) (hγ : γ < α) (δ : Λ) (hδβ : δ ≤ β) (hδγ : δ ≤ γ) :
    (ihs β hβ).ih δ hδβ = (ihs γ hγ).ih δ hδγ := by
  revert hδβ hδγ
  refine Params.Λ_isWellOrder.wf.induction
    (C := fun δ => (hδβ : δ ≤ β) → (hδγ : δ ≤ γ) → (ihs β hβ).ih δ hδβ = (ihs γ hγ).ih δ hδγ) δ ?_
  intro δ ih hδβ hδγ
  rw [(ihs β hβ).ih_eq, (ihs γ hγ).ih_eq]
  congr 1
  ext ε hε
  exact ih ε hε (hε.le.trans hδβ) (hε.le.trans hδγ)

noncomputable def buildCumulStep (α : Λ) (ihs : ∀ β < α, IHCumul β) : IHCumul α where
  ih := buildStepFn α (fun β hβ => (ihs β hβ).ih β le_rfl) (by
    intro β hβ
    convert buildStep_prop β (fun γ hγ => (ihs β hβ).ih γ hγ.le)
      (fun γ hγ => (ihs β hβ).prop γ hγ.le) using 1
    ext γ hγ : 2
    dsimp only
    by_cases hγ' : γ = β
    · cases hγ'
      rw [buildStepFn_eq, (ihs β hβ).ih_eq β le_rfl]
    · rw [buildStepFn_lt _ _ _ _ (lt_of_le_of_ne hγ hγ'),
        (ihs β hβ).ih_eq γ hγ, (ihs γ (hγ.trans_lt hβ)).ih_eq γ le_rfl]
      congr 1
      ext δ hδ
      rw [ihs_eq])
  prop := by
    intro β hβ
    by_cases hβ' : β = α
    · cases hβ'
      exact buildStep_prop _ _ _
    · have hβ'' := lt_of_le_of_ne hβ hβ'
      convert buildStep_prop β (fun γ hγ => (ihs β hβ'').ih γ hγ.le)
        (fun γ hγ => (ihs β hβ'').prop γ hγ.le) using 1
      ext γ hγ : 2
      dsimp only
      rw [buildStepFn_lt _ _ _ _ (hγ.trans_lt hβ''), (ihs γ _).ih_eq γ le_rfl]
      by_cases hγ' : γ = β
      · cases hγ'
        rw [buildStepFn_eq]
      · rw [buildStepFn_lt _ _ _ _ (lt_of_le_of_ne hγ hγ'), (ihs β hβ'').ih_eq γ hγ]
        congr 1
        ext δ hδ
        rw [ihs_eq]
  ih_eq := by
    intro β hβ
    by_cases hβ' : β = α
    · cases hβ'
      rw [buildStepFn_eq]
      congr 1
      ext β hβ
      rw [buildStepFn_lt _ _ _ _ hβ]
    · rw [buildStepFn_lt, (ihs β (lt_of_le_of_ne hβ hβ')).ih_eq β le_rfl]
      congr 1
      ext γ hγ
      rw [buildStepFn_lt _ _ _ _ (hγ.trans_le hβ), ihs_eq]

noncomputable def buildCumul (α : Λ) : IHCumul α :=
  Params.Λ_isWellOrder.wf.recursion α buildCumulStep

end ConNF.Construction
