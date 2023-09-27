import ConNF.Counting.OrdSupport

/-!
# Extending ordered supports
-/

open Set Sum
open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}

namespace OrdSupport

/-- An arbitrary global well-ordering on support conditions, such that `c ≺ d` implies `c < d`. -/
def ConditionRel (c d : SupportCondition β) : Prop :=
  c.value < d.value ∨ (c.value = d.value ∧ WellOrderingRel c.path d.path)

theorem conditionRel_of_constrains :
    Subrelation ((· ≺[α] ·) : SupportCondition β → _ → Prop) ConditionRel :=
  Or.inl ∘ constrains_subrelation α β

theorem conditionRel_of_transConstrains :
    Subrelation ((· <[α] ·) : SupportCondition β → _ → Prop) ConditionRel :=
  Or.inl ∘ transConstrains_subrelation β

instance conditionRel_isTrichotomous : IsTrichotomous (SupportCondition β) ConditionRel := by
  letI hlo : LinearOrder (Atom ⊕ NearLitter) := inferInstance
  constructor
  rintro ⟨A, x⟩ ⟨B, y⟩
  unfold ConditionRel
  simp only [SupportCondition.mk.injEq]
  rw [or_iff_not_imp_left, not_or, not_and]
  intro h₁
  rw [or_iff_not_imp_left, not_and]
  intro h₂
  rw [or_iff_not_imp_left]
  intro h₃
  simp only [not_lt] at h₁ h₃
  cases @le_antisymm _ hlo.toPartialOrder _ _ h₁.1 h₃
  obtain (h | h | h) := WellOrderingRel.isWellOrder.trichotomous A B
  · cases h₁.2 rfl h
  · cases h₂ h rfl
  · exact ⟨rfl, h⟩

instance conditionRel_isTrans : IsTrans (SupportCondition β) ConditionRel := by
  letI hlo : LinearOrder (Atom ⊕ NearLitter) := inferInstance
  letI hpo : Preorder (Atom ⊕ NearLitter) := hlo.toPreorder
  constructor
  unfold ConditionRel
  intro c₁ c₂ c₃ h₁ h₂
  have := WellOrderingRel.isWellOrder.trans c₁.path c₂.path c₃.path
  have := @lt_trans _ hlo.toPreorder c₁.value c₂.value c₃.value
  aesop

instance conditionRel_isWellFounded : IsWellFounded (SupportCondition β) ConditionRel := by
  letI hwo : IsWellFounded (Atom ⊕ NearLitter) (· < ·) := inferInstance
  refine ⟨⟨?_⟩⟩
  intro c
  refine hwo.wf.induction
    (C := fun x => ∀ A : ExtendedIndex β, Acc ConditionRel ⟨A, x⟩) c.value ?_ c.path
  clear c
  intro x ih₁ A
  refine WellOrderingRel.isWellOrder.wf.induction (C := fun A => Acc ConditionRel ⟨A, x⟩) A ?_
  clear A
  intro A ih₂
  constructor
  rintro c (hc | ⟨rfl, hc⟩)
  · exact ih₁ c.value hc c.path
  · exact ih₂ c.path hc

instance : IsWellOrder (SupportCondition β) ConditionRel := ⟨⟩

/-- Extends the well-order `S` to a well-order of `SupportCondition β`, in such a way that `S`
is an initial segment. -/
@[mk_iff]
inductive ExtendRel (S : OrdSupport β) : SupportCondition β → SupportCondition β → Prop
| lt (c d : S) : c < d → ExtendRel S c d
| conditionRel (c d : SupportCondition β) : c ∉ S → d ∉ S → ConditionRel c d → ExtendRel S c d
| sep (c : S) (d : SupportCondition β) : d ∉ S → ExtendRel S c d

instance (S : OrdSupport β) : IsTrichotomous (SupportCondition β) (ExtendRel S) := by
  constructor
  intro c d
  by_cases hc : c ∈ S <;> by_cases hd : d ∈ S
  · obtain (h | h | h) := lt_trichotomy (⟨c, hc⟩ : S) ⟨d, hd⟩
    · exact Or.inl (ExtendRel.lt ⟨c, hc⟩ ⟨d, hd⟩ h)
    · rw [Subtype.mk.injEq] at h
      exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (ExtendRel.lt ⟨d, hd⟩ ⟨c, hc⟩ h))
  · exact Or.inl (ExtendRel.sep ⟨c, hc⟩ d hd)
  · exact Or.inr (Or.inr (ExtendRel.sep ⟨d, hd⟩ c hc))
  · obtain (h | h | h) := conditionRel_isTrichotomous.trichotomous c d
    · exact Or.inl (ExtendRel.conditionRel c d hc hd h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (ExtendRel.conditionRel d c hd hc h))

instance (S : OrdSupport β) : IsTrans (SupportCondition β) (ExtendRel S) := by
  constructor
  intro c₁ c₂ c₃ h₁ h₂
  cases h₁ with
  | lt c₁ c₂ h₁ =>
    obtain ⟨c₂, hc₂⟩ := c₂
    cases h₂ with
    | lt c₂ c₃ h₂ =>
      exact ExtendRel.lt c₁ c₃ (h₁.trans h₂)
    | conditionRel c₂ c₃ hc₂' hc₃ h₂ =>
      cases hc₂' hc₂
    | sep c₂ c₃ hc₃ =>
      exact ExtendRel.sep c₁ c₃ hc₃
  | conditionRel c₁ c₂ hc₁ hc₂ h₁ =>
    cases h₂ with
    | lt c₂ c₃ h₂ =>
      cases hc₂ c₂.prop
    | conditionRel c₂ c₃ hc₂' hc₃ h₂ =>
      exact ExtendRel.conditionRel c₁ c₃ hc₁ hc₃ (conditionRel_isTrans.trans c₁ c₂ c₃ h₁ h₂)
    | sep c₂ c₃ hc₃ =>
      cases hc₂ c₂.prop
  | sep c₁ c₂ hc₂ =>
    cases h₂ with
    | lt c₂ c₃ h₂ =>
      cases hc₂ c₂.prop
    | conditionRel c₂ c₃ hc₂' hc₃ h₂ =>
      exact ExtendRel.sep c₁ c₃ hc₃
    | sep c₂ c₃ hc₃ =>
      cases hc₂ c₂.prop

theorem mem_of_extendRel {S : OrdSupport β} (c : SupportCondition β) (d : S)
    (h : ExtendRel S c d) : c ∈ S := by
  obtain ⟨d, hd⟩ := d
  cases h with
  | lt c d h =>
    exact c.prop
  | conditionRel c d hc hd' h =>
    cases hd' hd
  | sep c d h =>
    cases h hd

theorem lt_of_extendRel {S : OrdSupport β} (c : SupportCondition β) (d : S)
    (h : ExtendRel S c d) : ⟨c, mem_of_extendRel c d h⟩ < d := by
  obtain ⟨d, hd⟩ := d
  cases h with
  | lt c d h =>
    exact h
  | conditionRel c d hc hd' h =>
    cases hd' hd
  | sep c d h =>
    cases h hd

instance (S : OrdSupport β) : IsWellFounded (SupportCondition β) (ExtendRel S) := by
  constructor
  have : ∀ c : S, Acc (ExtendRel S) c
  · intro c
    refine S.induction (motive := fun c => Acc (ExtendRel S) c) c ?_
    intro c ih
    constructor
    intro d hd
    exact ih ⟨d, mem_of_extendRel d c hd⟩ (lt_of_extendRel d c hd)
  constructor
  intro c
  refine conditionRel_isWellFounded.induction (C := fun c => Acc (ExtendRel S) c) c ?_
  intro c ih
  constructor
  intro d hd
  cases hd with
  | lt c d h =>
    exact this c
  | conditionRel c d hc hd' h =>
    exact ih d h
  | sep c d h =>
    exact this c

instance (S : OrdSupport β) : IsWellOrder (SupportCondition β) (ExtendRel S) := ⟨⟩

/-- Add some extra support conditions to the end of an ordered support. -/
noncomputable def extend (S : OrdSupport β) (s : Set (SupportCondition β)) (hs : Small s) :
    OrdSupport β where
  carrier := S ∪ s
  carrier_small := Small.union S.small hs
  r c d := ExtendRel S c d
  r_isWellOrder := isWellOrder_invImage
    (inferInstanceAs (IsWellOrder (SupportCondition β) (ExtendRel S))) _ Subtype.val_injective

/-- An extended support specialises the original. -/
theorem le_extend (S : OrdSupport β) (s : Set (SupportCondition β)) (hs : Small s) :
    S ≤ S.extend s hs where
  mem_of_mem c := Or.inl c.prop
  lt_iff_lt c d := ⟨ExtendRel.lt c d, fun h => lt_of_extendRel c d (show ExtendRel S c d from h)⟩
  get_lt_get c d hd := ExtendRel.sep c d hd

theorem mem_extend_iff (S : OrdSupport β) (s : Set (SupportCondition β)) (hs : Small s)
    (c : SupportCondition β) :
    c ∈ S.extend s hs ↔ c ∈ S ∨ c ∈ s :=
  Iff.rfl

end OrdSupport

end ConNF
