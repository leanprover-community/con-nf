import ConNF.Aux.Rel
import ConNF.Aux.Set
import ConNF.Setup.Params

/-!
# Smallness

In this file, we define the notion of a small set, and prove many of the basic properties of small
sets.

## Main declarations

* `ConNF.Small`: A set is *small* if its cardinality is less than `#κ`.
* `ConNF.Near`: Two sets are *near* if their symmetric difference is small.
-/

universe u v

open Cardinal Set
open scoped symmDiff

namespace ConNF

variable [Params.{u}] {ι α β : Type _} {s t u : Set α}

/-- A set is *small* if its cardinality is less than `#κ`. -/
def Small (s : Set α) : Prop :=
  #s < #κ

theorem Small.lt : Small s → #s < #κ :=
  id

/-!
## Criteria for smallness
-/

theorem small_of_subsingleton (h : s.Subsingleton) : Small s :=
  h.cardinal_mk_le_one.trans_lt <| one_lt_aleph0.trans_le aleph0_lt_κ.le

@[simp]
theorem small_empty : Small (∅ : Set α) :=
  small_of_subsingleton subsingleton_empty

@[simp]
theorem small_singleton (x : α) : Small {x} :=
  small_of_subsingleton subsingleton_singleton

/-- Subsets of small sets are small. We say that the 'smallness' relation is monotone. -/
theorem Small.mono (h : s ⊆ t) : Small t → Small s :=
  (mk_le_mk_of_subset h).trans_lt

theorem Small.congr (h : s = t) : Small t → Small s :=
  Small.mono (subset_of_eq h)

/-- Unions of small subsets are small. -/
theorem small_union (hs : Small s) (ht : Small t) : Small (s ∪ t) :=
  (mk_union_le _ _).trans_lt <| add_lt_of_lt Params.κ_isRegular.aleph0_le hs ht

/-- Unions of small subsets are small. -/
theorem small_symmDiff (hs : Small s) (ht : Small t) : Small (s ∆ t) :=
  (small_union hs ht).mono symmDiff_subset_union

theorem small_iUnion (hι : #ι < #κ) {f : ι → Set α} (hf : ∀ i, Small (f i)) :
    Small (⋃ i, f i) :=
  (mk_iUnion_le _).trans_lt <|
    mul_lt_of_lt Params.κ_isRegular.aleph0_le hι <| iSup_lt_of_isRegular Params.κ_isRegular hι hf

theorem small_iUnion_Prop {p : Prop} {f : p → Set α} (hf : ∀ i, Small (f i)) : Small (⋃ i, f i) :=
  by by_cases p <;> simp_all

theorem small_biUnion {s : Set ι} (hs : Small s) {f : ∀ i ∈ s, Set α}
    (hf : ∀ (i : ι) (hi : i ∈ s), Small (f i hi)) : Small (⋃ (i : ι) (hi : i ∈ s), f i hi) :=
  (small_iUnion hs (λ i ↦ hf i i.prop)).congr (Set.biUnion_eq_iUnion _ _)

/-- The image of a small set under any function `f` is small. -/
theorem Small.image (f : α → β) : Small s → Small (f '' s) :=
  mk_image_le.trans_lt

/-- The preimage of a small set under an injective function `f` is small. -/
theorem Small.preimage (f : β → α) (h : f.Injective) : Small s → Small (f ⁻¹' s) :=
  (mk_preimage_of_injective f s h).trans_lt

theorem κ_le_of_not_small (h : ¬Small s) : #κ ≤ #s := by
  rwa [Small, not_lt] at h

theorem iio_small (i : κ) : Small {j | j < i} := by
  have := Ordinal.type_Iio_lt i
  rwa [κ_type, lt_ord, Ordinal.card_type] at this

theorem iic_small (i : κ) : Small {j | j ≤ i} := by
  have := Ordinal.type_Iic_lt i
  rwa [κ_type, lt_ord, Ordinal.card_type] at this

/-!
## Cardinality bounds on collections of small sets
-/

/-- The amount of small subsets of `α` is bounded below by the cardinality of `α`. -/
theorem card_le_card_small (α : Type _) : #α ≤ #{s : Set α | Small s} := by
  apply mk_le_of_injective (f := λ x ↦ ⟨{x}, small_singleton x⟩)
  intro x y h
  exact singleton_injective <| congr_arg Subtype.val h

/-- There are at most `μ` small sets of a type at most as large as `μ`. -/
theorem card_small_le (h : #α ≤ #μ) : #{s : Set α | Small s} ≤ #μ := by
  rw [le_def] at h
  obtain ⟨⟨f, hf⟩⟩ := h
  rw [← mk_subset_mk_lt_cof μ_isStrongLimit.2]
  refine mk_le_of_injective (f := λ s ↦ ⟨f '' s, ?_⟩) ?_
  · exact mk_image_le.trans_lt <| s.prop.trans_le κ_le_μ_ord_cof
  · intro s t h
    exact Subtype.val_injective <| hf.image_injective <| congr_arg Subtype.val h

/-- There are exactly `μ` small sets of a type of size `μ`. -/
theorem card_small_eq (h : #α = #μ) : #{s : Set α | Small s} = #μ := by
  apply le_antisymm
  · exact card_small_le h.le
  · exact h.symm.trans_le <| card_le_card_small α

/-!
## Small relations
-/

theorem small_codom_of_small_dom {r : Rel α β} (h : r.Coinjective) (h' : Small r.dom) :
    Small r.codom := by
  have := small_biUnion h' (f := λ x _ ↦ {y | r x y}) ?_
  · apply this.mono
    rintro y ⟨x, hxy⟩
    simp only [mem_iUnion]
    exact ⟨x, ⟨y, hxy⟩, hxy⟩
  · intro x hx
    apply small_of_subsingleton
    intro y hy z hz
    exact h.coinjective hy hz

theorem small_graph' {r : Rel α β} (h₁ : Small r.dom) (h₂ : Small r.codom) :
    Small r.graph' := by
  have := small_biUnion h₁ (f := λ x _ ↦ {z : α × β | z.1 = x ∧ r x z.2}) ?_
  · apply this.mono
    rintro z hz
    simp only [mem_iUnion]
    exact ⟨z.1, ⟨z.2, hz⟩, rfl, hz⟩
  · intro x hx
    apply (h₂.image (λ y ↦ (x, y))).mono
    rintro ⟨x', y⟩ hy
    rw [mem_setOf_eq] at hy
    cases hy.1
    rw [mem_image]
    exact ⟨y, ⟨x', hy.2⟩, rfl⟩

/-!
## Nearness
-/

/-- Two sets are called *near* if their symmetric difference is small. -/
def Near (s t : Set α) : Prop :=
  Small (s ∆ t)

@[refl]
theorem near_refl (s : Set α) : Near s s := by
  rw [Near, symmDiff_self]
  exact small_empty

theorem near_rfl : Near s s :=
  near_refl s

theorem near_of_eq (h : s = t) : Near s t :=
  h ▸ near_refl s

@[symm]
theorem near_symm (h : Near s t) : Near t s := by
  rwa [Near, symmDiff_comm] at h

@[symm]
theorem near_trans (h₁ : Near s t) (h₂ : Near t u) : Near s u :=
  (small_union h₁ h₂).mono (symmDiff_trans_subset s t u)

theorem near_symmDiff_self_of_small (h : Small s) : Near (s ∆ t) t := by
  rwa [Near, symmDiff_symmDiff_cancel_right]

theorem near_image (h : Near s t) (f : α → β) : Near (f '' s) (f '' t) :=
  (h.image f).mono subset_image_symmDiff

theorem card_le_of_near (h₁ : Near s t) (h₂ : ¬Small t) : #t ≤ #s := by
  rw [Near, Small, Set.symmDiff_def, mk_union_of_disjoint disjoint_sdiff_sdiff] at h₁
  rw [Small, not_lt] at h₂
  have h₃ := (le_add_self.trans_lt h₁).trans_le h₂
  by_contra! h₄
  have := add_lt_of_lt (aleph0_lt_κ.le.trans h₂) h₃ h₄
  exact (le_mk_diff_add_mk t s).not_lt this

/-- Two large sets that are near each other have the same cardinality (and we only need to suppose
that one of them is large to draw this conclusion). -/
theorem card_eq_of_near (h₁ : Near s t) (h₂ : ¬Small t) : #s = #t := by
  have := card_le_of_near h₁ h₂
  have h₃ : ¬Small s := h₂ ∘ this.trans_lt
  exact le_antisymm (card_le_of_near (near_symm h₁) h₃) this

theorem card_inter_of_near (h₁ : Near s t) (h₂ : ¬Small s) : #(s ∩ t : Set α) = #s := by
  apply le_antisymm
  · apply mk_le_of_injective (f := λ x ↦ ⟨x, x.prop.1⟩)
    intro x y h
    rwa [Subtype.mk.injEq, Subtype.coe_inj] at h
  · rw [← diff_symmDiff_self]
    apply le_of_le_add (le_mk_diff_add_mk s (s ∆ t))
    · exact aleph0_lt_κ.le.trans (κ_le_of_not_small h₂)
    · exact h₁.trans_le (κ_le_of_not_small h₂)

theorem inter_nonempty_of_near (h₁ : Near s t) (h₂ : ¬Small s) : (s ∩ t).Nonempty := by
  rw [← mk_ne_zero_iff_nonempty, card_inter_of_near h₁ h₂]
  exact ne_of_gt <| aleph0_pos.trans <| aleph0_lt_κ.trans_le <| κ_le_of_not_small h₂

theorem card_near_le (s : Set α) (h : #α ≤ #μ) : #{t | Near t s} ≤ #μ := by
  refine le_trans ?_ (card_small_le h)
  apply mk_le_of_injective (f := λ t ↦ ⟨t ∆ s, t.prop⟩)
  intro t₁ t₂ ht
  exact Subtype.val_injective <| symmDiff_left_injective s <| congr_arg Subtype.val ht

theorem card_near_eq (s : Set α) (h : #α = #μ) : #{t | Near t s} = #μ := by
  refine trans ?_ (card_small_eq h)
  rw [Cardinal.eq]
  refine ⟨⟨λ t ↦ ⟨t ∆ s, t.prop⟩, λ t ↦ ⟨t ∆ s, near_symmDiff_self_of_small t.prop⟩, ?_, ?_⟩⟩ <;>
  · intro t
    simp only [coe_setOf, mem_setOf_eq, symmDiff_symmDiff_cancel_right, Subtype.coe_eta]

end ConNF
