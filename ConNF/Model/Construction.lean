import ConNF.NewTangle
import ConNF.Counting

open Cardinal Function MulAction Set Sum Quiver WithBot

open scoped Cardinal

universe u

namespace ConNF.Construction

variable [Params.{u}] [BasePositions]

/-- The data for the main inductive hypothesis,
containing the things we need to construct at each level `α`. -/
structure IH (α : Λ) where
  Tangle : Type u
  Allowable : Type u
  [allowableGroup : Group Allowable]
  allowableToStructPerm : Allowable →* StructPerm α
  /-- We make this assumption for convenience, since it makes `IHProp` into a subsingleton,
  and so we can encode it as a `Prop`. -/
  allowableToStructPerm_injective : Function.Injective allowableToStructPerm
  [allowableAction : MulAction Allowable Tangle]
  support : Tangle → Support α
  support_supports (t : Tangle) :
    haveI : MulAction Allowable (Address α) :=
      MulAction.compHom _ allowableToStructPerm
    MulAction.Supports Allowable (support t : Set (Address α)) t
  pos : Tangle ↪ μ
  typedAtom : Atom ↪ Tangle
  typedNearLitter : NearLitter ↪ Tangle
  pos_typedAtom (a : Atom) : pos (typedAtom a) = ConNF.pos a
  pos_typedNearLitter (N : NearLitter) : pos (typedNearLitter N) = ConNF.pos N
  smul_typedNearLitter :
    ∀ (ρ : Allowable) (N : NearLitter),
    ρ • typedNearLitter N =
    typedNearLitter ((allowableToStructPerm ρ) (Hom.toPath <| bot_lt_coe α) • N)
  toPretangle : Tangle → Pretangle α

instance {α : Λ} {ih : IH α} : Group ih.Allowable := ih.allowableGroup
instance {α : Λ} {ih : IH α} : MulAction ih.Allowable ih.Tangle := ih.allowableAction
instance {α : Λ} {ih : IH α} {X : Type _} [MulAction (StructPerm α) X] :
    MulAction ih.Allowable X :=
  MulAction.compHom _ ih.allowableToStructPerm
instance {α : Λ} {ih : IH α} : Position ih.Tangle μ := ⟨ih.pos⟩

def IH.tangleData {α : Λ} (ih : IH α) : TangleData α where
  Tangle := ih.Tangle
  Allowable := ih.Allowable
  allowableToStructPerm := ih.allowableToStructPerm
  support := ih.support
  support_supports := ih.support_supports

def IH.positionedTangles {α : Λ} (ih : IH α) :
    letI := ih.tangleData
    PositionedTangles α :=
  letI := ih.tangleData
  ⟨ih.pos⟩

def IH.typedObjects {α : Λ} (ih : IH α) :
    letI := ih.tangleData
    TypedObjects α :=
  letI := ih.tangleData
  { typedAtom := ih.typedAtom
    typedNearLitter := ih.typedNearLitter
    smul_typedNearLitter := ih.smul_typedNearLitter }

def IH.positionedObjects {α : Λ} (ih : IH α) :
    letI := ih.tangleData
    letI := ih.positionedTangles
    letI := ih.typedObjects
    PositionedObjects α :=
  letI := ih.tangleData
  letI := ih.positionedTangles
  letI := ih.typedObjects
  { pos_typedAtom := ih.pos_typedAtom
    pos_typedNearLitter := ih.pos_typedNearLitter }

/-- A renaming of `fuzz` that uses only data from the `IH`s. -/
noncomputable def fuzz' {β γ : Λ} (ihβ : IH β) (ihγ : IH γ) (h : (β : TypeIndex) ≠ γ) :
    ihβ.Tangle → Litter :=
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
  smul_support (t : (ih α le_rfl).Tangle) (ρ : (ih α le_rfl).Allowable) :
    (ih α le_rfl).support (ρ • t) = ρ • (ih α le_rfl).support t
  pos_lt_pos_atom (t : (ih α le_rfl).Tangle)
    {A : ExtendedIndex α} {a : Atom} (ht : ⟨A, inl a⟩ ∈ (ih α le_rfl).support t) :
    t ≠ (ih α le_rfl).typedAtom a → pos a < (ih α le_rfl).pos t
  pos_lt_pos_nearLitter (t : (ih α le_rfl).Tangle)
    {A : ExtendedIndex α} {N : NearLitter} (ht : ⟨A, inr N⟩ ∈ (ih α le_rfl).support t) :
    t ≠ (ih α le_rfl).typedNearLitter N → pos N < (ih α le_rfl).pos t
  smul_fuzz (β : Λ) (hβ : β < α) (γ : Λ) (hγ : γ < α) (hβγ : (β : TypeIndex) ≠ γ)
    (ρ : (ih α le_rfl).Allowable) (t : (ih β hβ.le).Tangle)
    (fαβ : (ih α le_rfl).Allowable →* (ih β hβ.le).Allowable)
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
      (t : (ih β hβ.le).Tangle)
      (fαβ : (ih α le_rfl).Allowable →* (ih β hβ.le).Allowable)
      (_hfαβ : ∀ ρ : (ih α le_rfl).Allowable,
        Tree.comp (Hom.toPath (coe_lt_coe.mpr hβ)) ((ih α le_rfl).allowableToStructPerm ρ) =
        (ih β hβ.le).allowableToStructPerm (fαβ ρ)),
      (ih γ hγ.le).allowableToStructPerm (ρs γ hγ) (Hom.toPath (bot_lt_coe _)) •
        fuzz' (ih β hβ.le) (ih γ hγ.le) hβγ t =
      fuzz' (ih β hβ.le) (ih γ hγ.le) hβγ (ρs β hβ • t))
    (hπ : ∀ (γ : Λ) (hγ : γ < α) (t : Atom),
      (ih γ hγ.le).allowableToStructPerm (ρs γ hγ)
        (Hom.toPath (bot_lt_coe _)) • fuzz'Bot (ih γ hγ.le) t =
      fuzz'Bot (ih γ hγ.le) (π • t)) :
    ∃ ρ : (ih α le_rfl).Allowable,
    ∀ (β : Λ) (hβ : β < α) (fαβ : (ih α le_rfl).Allowable →* (ih β hβ.le).Allowable)
      (_hfαβ : ∀ ρ : (ih α le_rfl).Allowable,
        Tree.comp (Hom.toPath (coe_lt_coe.mpr hβ)) ((ih α le_rfl).allowableToStructPerm ρ) =
        (ih β hβ.le).allowableToStructPerm (fαβ ρ)),
      fαβ ρ = ρs β hβ
  toPretangle_smul (t : (ih α le_rfl).Tangle) (ρ : (ih α le_rfl).Allowable) :
    (ih α le_rfl).toPretangle (ρ • t) = ρ • (ih α le_rfl).toPretangle t
  eq_toPretangle_of_mem (β : Λ) (hβ : β < α) (t₁ : (ih α le_rfl).Tangle) (t₂ : Pretangle β) :
    t₂ ∈ Pretangle.ofCoe ((ih α le_rfl).toPretangle t₁) β (coe_lt_coe.mpr hβ) →
    ∃ t₂' : (ih β hβ.le).Tangle, t₂ = (ih β hβ.le).toPretangle t₂'
  /-- It's useful to keep this `Prop`-valued, because then there is no data in `IH` that
  crosses levels. -/
  has_singletons (β : Λ) (hβ : β < α) :
    ∃! S : (ih β hβ.le).Tangle ↪ (ih α le_rfl).Tangle,
    ∀ t : (ih β hβ.le).Tangle,
      Pretangle.ofCoe ((ih α le_rfl).toPretangle (S t)) β (coe_lt_coe.mpr hβ) =
      {(ih β hβ.le).toPretangle t}

def tangleDataStep (α : Λ) (ihs : (β : Λ) → β < α → IH β) : TangleData α :=
  letI : Level := ⟨α⟩
  letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
  letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
  letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
  letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
  {
    Tangle := NewTangle
    Allowable := NewAllowable
    allowableToStructPerm := NewAllowable.toStructPerm
    support := NewTangle.S
    support_supports := by
      intro t ρ h
      refine NewTangle.ext _ _ (t.h ρ h) ?_
      refine Enumeration.ext' rfl ?_
      intro i hS _
      exact h ⟨i, hS, rfl⟩
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
    tangleDataStepFn_lt α ihs β (lt_of_le_of_ne hβ hβ') ▸
      (ihs β (lt_of_le_of_ne hβ hβ')).typedObjects

theorem typedObjectsStepFn_lt (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) :
    letI := tangleDataStepFn α ihs β hβ.le
    typedObjectsStepFn α ihs β hβ.le =
      tangleDataStepFn_lt α ihs β hβ ▸ (ihs β hβ).typedObjects := by
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
          rw [typedObjectsStepFn_lt α ihs β (coe_lt_coe.mp hβ.elim),
            heq_eqRec_iff_heq, heq_eq_eq])
        (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
  }

theorem foaData_tangle_eq (α : Λ) (ihs : (β : Λ) → β < α → IH β) :
    letI : Level := ⟨α⟩
    letI : LeLevel α := ⟨le_rfl⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
    letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
    letI : FOAData := buildStepFOAData α ihs
    Tangle α = NewTangle := by
  change (tangleDataStepFn α ihs α le_rfl).Tangle = _
  rw [tangleDataStepFn_eq]
  rfl

def foaData_tangle_eq_equiv (α : Λ) (ihs : (β : Λ) → β < α → IH β) :
    letI : Level := ⟨α⟩
    letI : LeLevel α := ⟨le_rfl⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
    letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
    letI : FOAData := buildStepFOAData α ihs
    Tangle α ≃ NewTangle :=
  Equiv.cast (foaData_tangle_eq α ihs)

theorem foaData_tangle_lt (α : Λ) (ihs : (β : Λ) → β < α → IH β) (β : Λ) (hβ : β < α) :
    letI : Level := ⟨α⟩
    letI : LeLevel β := ⟨coe_le_coe.mpr hβ.le⟩
    letI : FOAData := buildStepFOAData α ihs
    Tangle β = (ihs β hβ).Tangle := by
  change (tangleDataStepFn α ihs β hβ.le).Tangle = _
  rw [tangleDataStepFn_lt]
  rfl

def foaData_tangle_lt_equiv (α : Λ) (ihs : (β : Λ) → β < α → IH β) (β : Λ) (hβ : β < α) :
    letI : Level := ⟨α⟩
    letI : LeLevel β := ⟨coe_le_coe.mpr hβ.le⟩
    letI : FOAData := buildStepFOAData α ihs
    Tangle β ≃ (ihs β hβ).Tangle :=
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

theorem tangleData_cast_support (α : Λ) (i₁ i₂ : TangleData α) (h : i₁ = i₂) (t) :
    i₁.support t =
    i₂.support (cast (show i₁.Tangle = i₂.Tangle by rw [h]) t) :=
  by subst h; rfl

theorem tangleData_cast_smul (α : Λ) (i₁ i₂ : TangleData α) (h : i₁ = i₂) (ρ t) :
    cast (show i₁.Tangle = i₂.Tangle by rw [h]) (i₁.allowableAction.smul ρ t) =
    i₂.allowableAction.smul
      (cast (show i₁.Allowable = i₂.Allowable by rw [h]) ρ)
      (cast (show i₁.Tangle = i₂.Tangle by rw [h]) t) :=
  by subst h; rfl

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
theorem foaData_allowable_eq_equiv_support (α : Λ) (ihs : (β : Λ) → β < α → IH β) (t) :
    letI : Level := ⟨α⟩
    letI : LeLevel α := ⟨le_rfl⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
    letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
    letI : FOAData := buildStepFOAData α ihs
    TangleData.Tangle.support t =
    NewTangle.S (foaData_tangle_eq_equiv α ihs t) :=
  tangleData_cast_support α _ _ (tangleDataStepFn_eq α ihs) t

@[simp]
theorem foaData_allowable_eq_equiv_smul (α : Λ) (ihs : (β : Λ) → β < α → IH β) (ρ t) :
    letI : Level := ⟨α⟩
    letI : LeLevel α := ⟨le_rfl⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
    letI : FOAData := buildStepFOAData α ihs
    foaData_tangle_eq_equiv α ihs (ρ • t) =
    foaData_allowable_eq_equiv α ihs ρ • foaData_tangle_eq_equiv α ihs t :=
  tangleData_cast_smul α _ _ (tangleDataStepFn_eq α ihs) ρ t

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
theorem foaData_allowable_lt_equiv_support (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) (t) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
    (letI : FOAData := buildStepFOAData α ihs
    TangleData.Tangle.support t) =
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    TangleData.Tangle.support (foaData_tangle_lt_equiv α ihs β hβ t)) :=
  tangleData_cast_support β _ _ (tangleDataStepFn_lt α ihs β hβ) t

@[simp]
theorem foaData_allowable_lt_equiv_smul (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) (ρ t) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
    foaData_tangle_lt_equiv α ihs β hβ
    (letI : FOAData := buildStepFOAData α ihs; ρ • t) =
    (letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    foaData_allowable_lt_equiv α ihs β hβ ρ • foaData_tangle_lt_equiv α ihs β hβ t) :=
  tangleData_cast_smul β _ _ (tangleDataStepFn_lt α ihs β hβ) ρ t

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

@[simp]
def foaData_allowable_lt'_equiv_eq_lt_equiv (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (β : Λ) (hβ : β < α) :
    foaData_allowable_lt'_equiv α ihs β (coe_lt_coe.mpr hβ) =
    foaData_allowable_lt_equiv α ihs β hβ := rfl

@[simp]
def foaData_allowable_lt'_equiv_eq_refl (α : Λ) (ihs : (β : Λ) → β < α → IH β) :
    foaData_allowable_lt'_equiv α ihs ⊥ (bot_lt_coe _) = Equiv.refl _ := rfl

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

-- TODO: Add `support` and `smul` lemmas.

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

theorem smul_support_step (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ)))
    (β : Λ) [iβ : letI : Level := ⟨α⟩; LeLevel β]
    (t :
      letI : Level := ⟨α⟩
      letI : FOAData := buildStepFOAData α ihs
      Tangle β)
    (ρ :
      letI : Level := ⟨α⟩
      letI : FOAData := buildStepFOAData α ihs
      Allowable β) :
    letI : Level := ⟨α⟩
    letI : FOAData := buildStepFOAData α ihs
    (ρ • t).support = ρ • t.support := by
  letI : Level := ⟨α⟩
  letI : FOAData := buildStepFOAData α ihs
  by_cases hβ : β = α
  · cases hβ
    simp only [foaData_allowable_eq_equiv_support, foaData_allowable_eq_equiv_smul,
      NewAllowable.smul_newTangle_S]
    rw [Allowable.toStructPerm_smul, foaData_allowable_eq_equiv_toStructPerm]
    rfl
  · have hβ' := lt_of_le_of_ne (coe_le_coe.mp iβ.elim) hβ
    have := (h β hβ').smul_support
      (foaData_tangle_lt_equiv α ihs β hβ' t)
      (foaData_allowable_lt_equiv α ihs β hβ' ρ)
    simp only [foaData_allowable_lt_equiv_support α ihs β hβ',
      foaData_allowable_lt_equiv_smul α ihs β hβ']
    rw [Allowable.toStructPerm_smul, foaData_allowable_lt_equiv_toStructPerm α ihs β hβ']
    exact this

noncomputable def buildStepFOAAssumptions (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ))) :
    letI : Level := ⟨α⟩
    FOAAssumptions :=
  letI : Level := ⟨α⟩
  letI : FOAData := buildStepFOAData α ihs
  {
    allowableCons := fun {β _ γ _} => allowableConsStep α ihs h β γ
    allowableCons_eq := allowableConsStep_eq α ihs h
    smul_support := smul_support_step α ihs h _
    pos_lt_pos_atom := sorry
    pos_lt_pos_nearLitter := sorry
    smul_fuzz := sorry
    allowable_of_smulFuzz := sorry
  }

noncomputable def buildStepCountingAssumptions (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ))) :
    letI : Level := ⟨α⟩
    CountingAssumptions :=
  letI : Level := ⟨α⟩
  letI : FOAAssumptions := buildStepFOAAssumptions α ihs h
  {
    toPretangle := sorry
    toPretangle_smul := sorry
    eq_toPretangle_of_mem := sorry
    toPretangle_ext := sorry
    singleton := sorry
    singleton_injective := sorry
    singleton_toPretangle := sorry
    mk_codingFunction_zero := sorry
  }

theorem mk_tangle_step (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ))) :
    letI : Level := ⟨α⟩
    letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
    letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
    letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
    letI : PositionedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedObjects
    #NewTangle = #μ := by
  letI : Level := ⟨α⟩
  letI : CountingAssumptions := buildStepCountingAssumptions α ihs h
  haveI : LeLevel α := ⟨le_rfl⟩
  rw [← foaData_tangle_eq]
  exact mk_tangle α

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
    allowableToStructPerm_injective := sorry
    pos := sorry
    pos_typedAtom := sorry
    pos_typedNearLitter := sorry
    toPretangle := sorry
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
