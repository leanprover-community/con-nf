import ConNF.Setup.Params

/-!
# Smallness

In this file, we define the notion of a small set, and prove many of the basic properties of small
sets.

## Main declarations

* `ConNF.Small`: A set is *small* if its cardinality is less than `#κ`.
-/

noncomputable section
universe u

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

end ConNF
