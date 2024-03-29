import ConNF.NewTangle.NewTangle

/-!
# Position function
-/

open Function Set Sum WithBot

open scoped Cardinal Pointwise

universe u

namespace ConNF.NewTangle

variable [Params.{u}] [Level] [BasePositions] [TangleDataLt] [PositionedTanglesLt] [TypedObjectsLt]
  [PositionedObjectsLt]

def posBound (t : NewTSet) (S : Support α) : Set μ :=
  {ν | ∃ (A : ExtendedIndex α) (a : Atom), ⟨A, inl a⟩ ∈ S ∧
    ∃ (β : TypeIndex) (_ : LtLevel β) (s : Tangle β) (γ : Λ) (_ : LtLevel γ) (hβγ : β ≠ γ),
    a.1 = fuzz hβγ s ∧ ν = pos s} ∪
  {ν | ∃ (A : ExtendedIndex α) (N : NearLitter), ⟨A, inr N⟩ ∈ S ∧
    ∃ (β : TypeIndex) (_ : LtLevel β) (s : Tangle β) (γ : Λ) (_ : LtLevel γ) (hβγ : β ≠ γ),
    Set.Nonempty ((N : Set Atom) ∩ (fuzz hβγ s).toNearLitter) ∧ ν = pos s} ∪
  {ν | ∃ a : Atom, t = newTypedAtom a ∧ ν = pos a} ∪
  {ν | ∃ N : NearLitter, t = newTypedNearLitter N ∧ ν = pos N}

def posBound' (t : NewTSet) (S : Support α) : Set μ :=
  (⋃ (c ∈ S) (A ∈ {A | c.1 = A}) (a ∈ {a | c.2 = inl a}) (β : TypeIndex) (_ : LtLevel β)
    (γ : Λ) (_ : LtLevel γ) (hβγ : β ≠ γ)
    (s : Tangle β) (_ : s ∈ {s | a.1 = fuzz hβγ s}),
    {ν | ν = pos s}) ∪
  (⋃ (c ∈ S) (A ∈ {A | c.1 = A}) (N ∈ {N | c.2 = inr N}) (β : TypeIndex) (_ : LtLevel β)
    (γ : Λ) (_ : LtLevel γ)(hβγ : β ≠ γ)
    (s : Tangle β) (_ : s ∈ {s | Set.Nonempty ((N : Set Atom) ∩ (fuzz hβγ s).toNearLitter)}),
    {ν | ν = pos s}) ∪
  (⋃ (a ∈ {a | t = newTypedAtom a}), {pos a}) ∪
  (⋃ (N ∈ {a | t = newTypedNearLitter a}), {pos N})

theorem posBound_eq_posBound' (t : NewTSet) (S : Support α) : posBound t S = posBound' t S := by
  rw [posBound, posBound']
  refine congr_arg₂ _ (congr_arg₂ _ (congr_arg₂ _ ?_ ?_) ?_) ?_
  · ext ν
    simp only [ne_eq, exists_and_right, mem_setOf_eq, setOf_eq_eq_singleton', mem_singleton_iff,
      setOf_eq_eq_singleton, iUnion_exists, iUnion_iUnion_eq_left, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨A, a, haS, β, _, s, ⟨γ, _, hβγ, has⟩, hν⟩
      exact ⟨⟨A, inl a⟩, haS, a, rfl, β, inferInstance, γ, inferInstance, hβγ, s, has, hν⟩
    · rintro ⟨⟨A, x⟩, haS, a, rfl, β, _, γ, _, hβγ, s, has, hν⟩
      exact ⟨A, a, haS, β, inferInstance, s, ⟨γ, inferInstance, hβγ, has⟩, hν⟩
  · ext ν
    simp only [ne_eq, exists_and_right, mem_setOf_eq, setOf_eq_eq_singleton', mem_singleton_iff,
      setOf_eq_eq_singleton, iUnion_exists, iUnion_iUnion_eq_left, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨A, N, hNS, β, _, s, ⟨γ, _, hβγ, hNs⟩, hν⟩
      exact ⟨⟨A, inr N⟩, hNS, N, rfl, β, inferInstance, γ, inferInstance, hβγ, s, hNs, hν⟩
    · rintro ⟨⟨A, x⟩, hNS, N, rfl, β, _, γ, _, hβγ, s, hNs, hν⟩
      exact ⟨A, N, hNS, β, inferInstance, s, ⟨γ, inferInstance, hβγ, hNs⟩, hν⟩
  · ext ν
    simp only [mem_setOf_eq, mem_iUnion, mem_singleton_iff, exists_prop]
  · ext ν
    simp only [mem_setOf_eq, mem_iUnion, mem_singleton_iff, exists_prop]

theorem small_posBound (t : NewTSet) (S : Support α) : Small (posBound t S) := by
  rw [posBound_eq_posBound', posBound']
  refine Small.union (Small.union (Small.union ?_ ?_) ?_) ?_
  · refine Small.bUnion S.small (fun c _ => ?_)
    refine Small.bUnion (by simp only [setOf_eq_eq_singleton', small_singleton]) (fun A _ => ?_)
    refine Small.bUnion ?_ (fun a _ => ?_)
    · refine Set.Subsingleton.small ?_
      intro a ha b hb
      cases ha.symm.trans hb
      rfl
    refine small_iUnion (by rw [mk_typeIndex]; exact Params.Λ_lt_κ) (fun β => ?_)
    refine small_iUnion_Prop (fun _ => ?_)
    refine small_iUnion Params.Λ_lt_κ (fun γ => ?_)
    refine small_iUnion_Prop (fun _ => ?_)
    refine small_iUnion_Prop (fun hβγ => ?_)
    refine Small.bUnion ?_ ?_
    · refine Set.Subsingleton.small ?_
      intro s₁ h₁ s₂ h₂
      exact fuzz_injective _ (h₁.symm.trans h₂)
    · simp only [ne_eq, mem_setOf_eq, setOf_eq_eq_singleton, small_singleton, forall_exists_index,
        implies_true, forall_const]
  · refine Small.bUnion S.small (fun c _ => ?_)
    refine Small.bUnion (by simp only [setOf_eq_eq_singleton', small_singleton]) (fun A _ => ?_)
    refine Small.bUnion ?_ (fun N _ => ?_)
    · refine Set.Subsingleton.small ?_
      intro N hN N hN'
      cases hN.symm.trans hN'
      rfl
    refine small_iUnion (by rw [mk_typeIndex]; exact Params.Λ_lt_κ) (fun β => ?_)
    refine small_iUnion_Prop (fun _ => ?_)
    refine small_iUnion Params.Λ_lt_κ (fun γ => ?_)
    refine small_iUnion_Prop (fun _ => ?_)
    refine small_iUnion_Prop (fun hβγ => ?_)
    refine Small.bUnion ?_ ?_
    · suffices : Small {L : Litter | Set.Nonempty ((N : Set Atom) ∩ L.toNearLitter)}
      · refine this.image_subset (f := fuzz hβγ) (fuzz_injective hβγ) ?_
        simp only [Litter.coe_toNearLitter, image_subset_iff, preimage_setOf_eq, setOf_subset_setOf,
          imp_self, implies_true]
      refine ((Small.image N.2.prop (f := fun a => a.1)).union (small_singleton N.1)).mono ?_
      rintro L ⟨a, ha, rfl⟩
      by_cases ha' : a.1 = N.1
      · exact Or.inr ha'
      · exact Or.inl ⟨a, Or.inr ⟨ha, ha'⟩, rfl⟩
    · simp only [ne_eq, mem_setOf_eq, setOf_eq_eq_singleton, small_singleton, forall_exists_index,
        implies_true, forall_const]
  · refine Small.bUnion ?_ (fun _ _ => small_singleton _)
    refine Set.Subsingleton.small ?_
    intro a₁ ha₁ a₂ ha₂
    exact newTypedAtom_injective (ha₁.symm.trans ha₂)
  · refine Small.bUnion ?_ (fun _ _ => small_singleton _)
    refine Set.Subsingleton.small ?_
    intro N₁ hN₁ N₂ hN₂
    exact newTypedNearLitter_injective (hN₁.symm.trans hN₂)

def posDeny (t : NewTSet × Support α) : Set μ :=
  {ν | ∃ ν' ∈ posBound t.1 t.2, ν ≤ ν'}

theorem mk_posDeny (t : NewTSet × Support α) : #(posDeny t) < #μ := by
  have := (small_posBound t.1 t.2).trans_le Params.κ_le_μ_ord_cof
  rw [← Params.μ_ord] at this
  obtain ⟨ν, hν⟩ := Ordinal.lt_cof_type this
  refine (Cardinal.mk_subtype_le_of_subset ?_).trans_lt (card_Iic_lt ν)
  rintro ν₁ ⟨ν₂, hν₂, hν₁⟩
  exact hν₁.trans (hν ν₂ hν₂).le

theorem exists_wellOrder (h : #NewTSet = #μ) :
    ∃ (r : NewTSet × Support α → NewTSet × Support α → Prop)
    (_ : IsWellOrder (NewTSet × Support α) r),
    Ordinal.type r = Cardinal.ord #μ := by
  have : #(NewTSet × Support α) = #μ
  · simp only [Cardinal.mk_prod, Cardinal.lift_id, h, mk_support]
    exact Cardinal.mul_eq_self Params.μ_isStrongLimit.isLimit.aleph0_le
  rw [Cardinal.eq] at this
  obtain ⟨e⟩ := this
  refine ⟨e ⁻¹'o (· < ·), RelIso.IsWellOrder.preimage ((· < ·) : μ → μ → Prop) e, ?_⟩
  rw [Ordinal.type_preimage ((· < ·) : μ → μ → Prop) e, Params.μ_ord]

def wellOrder (h : #NewTSet = #μ) : NewTSet × Support α → NewTSet × Support α → Prop :=
  (exists_wellOrder h).choose

instance wellOrder_isWellOrder (h : #NewTSet = #μ) :
    IsWellOrder (NewTSet × Support α) (wellOrder h) :=
  (exists_wellOrder h).choose_spec.choose

theorem wellOrder_type (h : #NewTSet = #μ) :
    Ordinal.type (wellOrder h) = Cardinal.ord #μ :=
  (exists_wellOrder h).choose_spec.choose_spec

theorem mk_posDeny' (h : #NewTSet = #μ) (t : NewTSet × Support α) :
    #{ s // wellOrder h s t } + #(posDeny t) < #μ := by
  refine Cardinal.add_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le ?_ (mk_posDeny t)
  simp only [Ordinal.card_typein]
  have := Ordinal.typein_lt_type (wellOrder h) t
  rw [wellOrder_type, Cardinal.lt_ord] at this
  exact this

noncomputable def pos (h : #NewTSet = #μ) : NewTSet × Support α → μ :=
  chooseWf posDeny (mk_posDeny' h)

theorem pos_injective (h : #NewTSet = #μ) : Injective (pos h) :=
  chooseWf_injective

theorem pos_not_mem_deny (h : #NewTSet = #μ) (t : NewTSet × Support α) :
    pos h t ∉ posDeny t :=
  chooseWf_not_mem_deny t

end ConNF.NewTangle
