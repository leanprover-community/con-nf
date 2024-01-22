import Mathlib.Data.PFun
import ConNF.BaseType.Params

/-!
# Smallness

In this file, we define what it means for a set to be small.

## Main declarations

* `ConNF.Small`: A set is small if its cardinality (as a type) is strictly less than `κ`.
* `ConNF.IsNear`: Two sets are near if their symmetric difference is small.
-/

open Cardinal Set

open scoped Classical symmDiff

universe u

namespace ConNF

variable [Params.{u}] {ι α β : Type u} {f : α → β} {s t u : Set α}

/-- A set is small if its cardinality is strictly less than `κ`. -/
def Small (s : Set α) : Prop :=
  #s < #κ

theorem Small.lt : Small s → #s < #κ :=
  id

theorem Set.Subsingleton.small {α : Type _} {s : Set α} (hs : s.Subsingleton) : Small s :=
  hs.cardinal_mk_le_one.trans_lt <| one_lt_aleph0.trans_le Params.κ_isRegular.aleph0_le

@[simp]
theorem small_empty : Small (∅ : Set α) :=
  Set.Subsingleton.small subsingleton_empty

@[simp]
theorem small_singleton (x : α) : Small ({x} : Set α) :=
  Set.Subsingleton.small subsingleton_singleton

theorem small_setOf (p : α → Prop) : (Small fun a => p a) ↔ Small {a | p a} :=
  Iff.rfl

theorem small_of_forall_not_mem {s : Set α} (h : ∀ x, x ∉ s) : Small s := by
  simp only [eq_empty_of_forall_not_mem h, small_empty]

/-- Subsets of small sets are small. We say that the 'smallness' relation is monotone. -/
theorem Small.mono (h : s ⊆ t) : Small t → Small s :=
  (mk_le_mk_of_subset h).trans_lt

/-- Unions of small subsets are small. -/
theorem Small.union (hs : Small s) (ht : Small t) : Small (s ∪ t) :=
  (mk_union_le _ _).trans_lt <| add_lt_of_lt Params.κ_isRegular.aleph0_le hs ht

theorem Small.symmDiff (hs : Small s) (ht : Small t) : Small (s ∆ t) :=
  (hs.union ht).mono symmDiff_subset_union

theorem Small.symmDiff_iff (hs : Small s) : Small t ↔ Small (s ∆ t) :=
  ⟨hs.symmDiff, fun ht => by simpa only [symmDiff_symmDiff_self'] using ht.symmDiff hs⟩

theorem small_iUnion (hι : #ι < #κ) {f : ι → Set α} (hf : ∀ i, Small (f i)) :
    Small (⋃ i, f i) :=
  (mk_iUnion_le _).trans_lt <|
    mul_lt_of_lt Params.κ_isRegular.aleph0_le hι <| iSup_lt_of_isRegular Params.κ_isRegular hι hf

theorem small_iUnion_Prop {p : Prop} {f : p → Set α} (hf : ∀ i, Small (f i)) : Small (⋃ i, f i) :=
  by by_cases p <;> simp_all

protected theorem Small.bUnion {s : Set ι} (hs : Small s) {f : ∀ i ∈ s, Set α}
    (hf : ∀ i (hi : i ∈ s), Small (f i hi)) : Small (⋃ (i) (hi : i ∈ s), f i hi) :=
  (mk_bUnion_le' _ _).trans_lt <|
    mul_lt_of_lt Params.κ_isRegular.aleph0_le hs <|
    iSup_lt_of_isRegular Params.κ_isRegular hs (fun _ => hf _ _)

/-- The image of a small set under any function `f` is small. -/
theorem Small.image : Small s → Small (f '' s) :=
  mk_image_le.trans_lt

/-- The preimage of a small set under an injective function `f` is small. -/
theorem Small.preimage {s : Set β} (h : f.Injective) : Small s → Small (f ⁻¹' s) :=
  (mk_preimage_of_injective f s h).trans_lt

-- TODO: Convert random smallness manipulations into invocations of this lemma.
/-- A set is small if its image under an injective function is contained in a small set. -/
theorem Small.image_subset {t : Set β} (f : α → β) (h : f.Injective) :
    Small t → f '' s ⊆ t → Small s := by
  intro h₁ h₂
  have := (Small.mono h₂ h₁).preimage h
  rw [preimage_image_eq s h] at this
  exact this

theorem Small.pFun_image {α β : Type _} {s : Set α} (h : Small s) {f : α →. β} :
    Small (f.image s) := by
  have : Small (f '' s) := Small.image h
  refine' Small.image_subset Part.some Part.some_injective this _
  rintro x ⟨y, ⟨z, hz₁, hz₂⟩, rfl⟩
  exact ⟨z, hz₁, Part.eq_some_iff.mpr hz₂⟩

/-- Two sets are near if their symmetric difference is small. -/
def IsNear (s t : Set α) : Prop :=
  Small (s ∆ t)

/-- A set is near itself. -/
@[refl]
theorem isNear_refl (s : Set α) : IsNear s s := by rw [IsNear, symmDiff_self]; exact small_empty

/-- A version of the `is_near_refl` lemma that does not require the set `s` to be given explicitly.
The value of `s` will be inferred automatically by the elaborator. -/
theorem isNear_rfl : IsNear s s :=
  isNear_refl _

/-- If `s` is near `t`, then `t` is near `s`. -/
@[symm]
theorem IsNear.symm (h : IsNear s t) : IsNear t s := by rwa [IsNear, symmDiff_comm]

/-- `s` is near `t` if and only if `t` is near `s`.
In each direction, this is an application of the `is_near.symm` lemma.
Lemmas using `↔` can be used with `rw`, so this form of the result is particularly useful. -/
theorem isNear_comm : IsNear s t ↔ IsNear t s :=
  ⟨IsNear.symm, IsNear.symm⟩

/-- Nearness is transitive: if `s` is near `t` and `t` is near `u`, then `s` is near `u`. -/
@[trans]
theorem IsNear.trans (hst : IsNear s t) (htu : IsNear t u) : IsNear s u :=
  (hst.union htu).mono <| symmDiff_triangle s t u

/-- If two sets are near each other, then their images under an arbitrary function are also near. -/
theorem IsNear.image (f : α → β) (h : IsNear s t) : IsNear (f '' s) (f '' t) :=
  Small.mono subset_image_symmDiff (Small.image h)

theorem isNear_of_small (hs : Small s) (ht : Small t) : IsNear s t :=
  Small.symmDiff hs ht

theorem Small.isNear_iff (hs : Small s) : Small t ↔ IsNear s t :=
  hs.symmDiff_iff

theorem IsNear.κ_le (h : IsNear s t) (hs : #κ ≤ #s) : #κ ≤ #(t : Set α) := by
  by_contra ht
  rw [not_le] at ht
  have := h.symm
  rw [← Small.isNear_iff ht] at this
  exact (lt_iff_not_ge _ _).mp this hs

theorem IsNear.mk_inter (h : IsNear s t) (hs : #κ ≤ #s) : #κ ≤ #(s ∩ t : Set α) := by
  rw [IsNear, symmDiff_eq_sup_sdiff_inf] at h
  exact le_of_not_gt fun hst =>
    lt_irrefl _
      (((hs.trans (mk_le_mk_of_subset (subset_union_left _ _))).trans
            (le_mk_diff_add_mk (s ∪ t) (s ∩ t))).trans_lt
        (add_lt_of_lt Params.κ_isRegular.aleph0_le h hst))

end ConNF
