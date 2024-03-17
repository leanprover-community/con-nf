import ConNF.NewTangle
import ConNF.Counting

open Cardinal Function MulAction Set Sum Quiver WithBot

open scoped Cardinal

universe u

namespace ConNF.Construction

variable [Params.{u}]

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
    ∃ f : (ih α le_rfl).Allowable → NearLitterPerm,
    ∀ ρ : (ih α le_rfl).Allowable,
      (ih α le_rfl).allowableToStructPerm ρ (Hom.toPath (bot_lt_coe _)) = f ρ
  smul_support (t : (ih α le_rfl).Tangle) (ρ : (ih α le_rfl).Allowable) :
    (ih α le_rfl).support (ρ • t) = ρ • (ih α le_rfl).support t
  pos_lt_pos_atom (t : (ih α le_rfl).Tangle)
    {A : ExtendedIndex α} {a : Atom} (ht : ⟨A, inl a⟩ ∈ (ih α le_rfl).support t)
    (β : Λ) (hβ : β < α) (s : (ih β hβ.le).Tangle)
    (γ : Λ) (hγ : γ < α) (hβγ : (β : TypeIndex) ≠ γ)
    (ha : a.1 = fuzz' (ih β hβ.le) (ih γ hγ.le) hβγ s) :
    pos s < pos t
  pos_lt_pos_atom_bot (t : (ih α le_rfl).Tangle)
    {A : ExtendedIndex α} {a : Atom} (ht : ⟨A, inl a⟩ ∈ (ih α le_rfl).support t)
    (s : Atom) (γ : Λ) (hγ : γ < α)
    (ha : a.1 = fuzz'Bot (ih γ hγ.le) s) :
    pos s < pos t
  pos_lt_pos_nearLitter (t : (ih α le_rfl).Tangle)
    {A : ExtendedIndex α} {N : NearLitter} (ht : ⟨A, inr N⟩ ∈ (ih α le_rfl).support t)
    (β : Λ) (hβ : β < α) (s : (ih β hβ.le).Tangle)
    (γ : Λ) (hγ : γ < α) (hβγ : (β : TypeIndex) ≠ γ)
    (ha : Set.Nonempty ((N : Set Atom) ∩ (fuzz' (ih β hβ.le) (ih γ hγ.le) hβγ s).toNearLitter)) :
    pos s < pos t
  pos_lt_pos_nearLitter_bot (t : (ih α le_rfl).Tangle)
    {A : ExtendedIndex α} {N : NearLitter} (ht : ⟨A, inr N⟩ ∈ (ih α le_rfl).support t)
    (s : Atom) (γ : Λ) (hγ : γ < α)
    (ha : Set.Nonempty ((N : Set Atom) ∩ (fuzz'Bot (ih γ hγ.le) s).toNearLitter)) :
    pos s < pos t
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

noncomputable def buildStep (α : Λ) (ihs : (β : Λ) → β < α → IH β)
    (h : ∀ (β : Λ) (hβ : β < α), IHProp β (fun γ hγ => ihs γ (hγ.trans_lt hβ))) : IH α :=
  letI : Level := ⟨α⟩
  letI : TangleDataLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).tangleData⟩
  letI : PositionedTanglesLt := ⟨fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).positionedTangles⟩
  letI : TypedObjectsLt := fun β hβ => (ihs β (coe_lt_coe.mp hβ.elim)).typedObjects
  {
    Tangle := NewTangle
    Allowable := NewAllowable
    allowableToStructPerm := NewAllowable.toStructPerm
    allowableToStructPerm_injective := sorry
    support := NewTangle.S
    support_supports := sorry
    pos := sorry
    typedAtom := ⟨newTypedAtom, newTypedAtom_injective⟩
    typedNearLitter := ⟨newTypedNearLitter, newTypedNearLitter_injective⟩
    smul_typedNearLitter := fun ρ N => NewAllowable.smul_newTypedNearLitter N ρ
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
