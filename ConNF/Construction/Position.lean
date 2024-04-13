import ConNF.Construction.NewTSet

/-!
# Construction of position functions

Assuming that there are only `μ` t-sets at level `α`, we can construct a position function for them.

## Main declarations

* `CoNNF.Construction.pos`: A position function for type `α` t-sets.
-/

open Function Set Sum WithBot

open scoped Cardinal Pointwise

universe u

namespace ConNF.Construction

variable [Params.{u}] [Level] [BasePositions] [ModelDataLt] [PositionedTanglesLt] [TypedObjectsLt]
  [PositionedObjectsLt]

/-- The position of `t` must be greater than elements of this small set. Since it is small, it
cannot be cofinal in `μ`. -/
def posBound (t : NewTSet) (S : Support α) : Set μ :=
  {ν | ∃ (A : ExtendedIndex α) (a : Atom), ⟨A, inl a⟩ ∈ S ∧ ν = pos a} ∪
  {ν | ∃ (A : ExtendedIndex α) (N : NearLitter), ⟨A, inr N⟩ ∈ S ∧
    t ≠ newTypedNearLitter N ∧ ν = pos N} ∪
  {ν | ∃ N : NearLitter, t = newTypedNearLitter N ∧ ν = pos N}

def posBound' (t : NewTSet) (S : Support α) : Set μ :=
  (⋃ (c ∈ S) (A ∈ {A | c.1 = A}) (a ∈ {a | c.2 = inl a}), {pos a}) ∪
  (⋃ (c ∈ S) (A ∈ {A | c.1 = A}) (N ∈ {N | c.2 = inr N ∧ t ≠ newTypedNearLitter N}),{pos N}) ∪
  (⋃ (N ∈ {a | t = newTypedNearLitter a}), {pos N})

theorem posBound_eq_posBound' (t : NewTSet) (S : Support α) : posBound t S = posBound' t S := by
  rw [posBound, posBound']
  refine congr_arg₂ _ (congr_arg₂ _ ?_ ?_) ?_
  · ext ν
    simp only [mem_setOf_eq, setOf_eq_eq_singleton', mem_singleton_iff, mem_iUnion]
    constructor
    · rintro ⟨A, a, haS, rfl⟩
      exact ⟨⟨A, inl a⟩, haS, A, rfl, a, rfl, rfl⟩
    · rintro ⟨⟨A, _⟩, haS, A, rfl, a, rfl, rfl⟩
      exact ⟨A, a, haS, rfl⟩
  · ext ν
    simp only [mem_setOf_eq, setOf_eq_eq_singleton', mem_singleton_iff, mem_iUnion]
    constructor
    · rintro ⟨A, N, hNS, ht, rfl⟩
      exact ⟨⟨A, inr N⟩, hNS, A, rfl, N, ⟨rfl, ht⟩, rfl⟩
    · rintro ⟨⟨A, _⟩, hNS, A, rfl, N, ⟨rfl, ht⟩, rfl⟩
      exact ⟨A, N, hNS, ht, rfl⟩
  · ext ν
    simp only [mem_setOf_eq, mem_iUnion, mem_singleton_iff, exists_prop]

theorem small_posBound (t : NewTSet) (S : Support α) : Small (posBound t S) := by
  rw [posBound_eq_posBound', posBound']
  refine Small.union (Small.union ?_ ?_) ?_
  · refine Small.bUnion S.small (fun c _ => ?_)
    refine Small.bUnion (by simp only [setOf_eq_eq_singleton', small_singleton]) (fun A _ => ?_)
    refine Small.bUnion ?_ (fun _ _ => small_singleton _)
    refine Set.Subsingleton.small ?_
    intro a ha b hb
    cases ha.symm.trans hb
    rfl
  · refine Small.bUnion S.small (fun c _ => ?_)
    refine Small.bUnion (by simp only [setOf_eq_eq_singleton', small_singleton]) (fun A _ => ?_)
    refine Small.bUnion ?_ (fun _ _ => small_singleton _)
    refine Set.Subsingleton.small ?_
    intro N hN N hN'
    cases hN.1.symm.trans hN'.1
    rfl
  · refine Small.bUnion ?_ (fun _ _ => small_singleton _)
    refine Set.Subsingleton.small ?_
    intro N₁ hN₁ N₂ hN₂
    exact newTypedNearLitter_injective (hN₁.symm.trans hN₂)

/-- The position of `t` must be greater than elements of this set, which is not cofinal in `μ`. -/
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

/-- A position function for type `α` t-sets. -/
noncomputable def pos (h : #NewTSet = #μ) : NewTSet × Support α → μ :=
  chooseWf posDeny (mk_posDeny' h)

theorem pos_injective (h : #NewTSet = #μ) : Injective (pos h) :=
  chooseWf_injective

theorem pos_not_mem_deny (h : #NewTSet = #μ) (t : NewTSet × Support α) :
    pos h t ∉ posDeny t :=
  chooseWf_not_mem_deny t

end ConNF.Construction
