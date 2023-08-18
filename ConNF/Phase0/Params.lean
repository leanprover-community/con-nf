import ConNF.Mathlib.Cardinal
import ConNF.Mathlib.Order
import ConNF.Mathlib.Ordinal
import ConNF.Mathlib.WithBot
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Data.Prod.Lex

/-!
# Parameters of the construction
-/

-- TODO: Remove all `noncomputable section` annotations.
noncomputable section

open Cardinal Set

open scoped Cardinal Classical

universe u

namespace ConNF

/--
The parameters of the constructions. We collect them all in one class for simplicity.
Note that the ordinal `λ` in the paper is instead referred to here as `Λ`, since the symbol `λ` is
used for lambda abstractions.

Ordinals and cardinals are represented here as arbitrary types (not sets) with certain properties.
For instance, `Λ` is an arbitrary type that has an ordering `Λr`, which is assumed to be a
well-ordering (the `Λwf` term is a proof of this fact). If `Λr a b` holds, then we can say `a < b`.

The prefix `#` denotes the cardinality of a type.

Where possible, we use `<` and `≤` instead of `>` and `≥`. Human readers can easily convert between
the two, but it is not as immediately transparent for Lean. For simplicity, we keep with the
convention of using only `<` and `≤`.
-/
class Params where
  Λ : Type u
  Λr : Λ → Λ → Prop
  [Λwf : IsWellOrder Λ Λr]
  Λ_ord : Ordinal.type Λr = (#Λ).ord
  Λ_limit : (#Λ).IsLimit
  κ : Type u
  κ_regular : (#κ).IsRegular
  κr : κ → κ → Prop
  [κwf : IsWellOrder κ κr]
  κ_ord : Ordinal.type κr = (#κ).ord
  Λ_lt_κ : (#Λ) < (#κ)
  μ : Type u
  μr : μ → μ → Prop
  [μwf : IsWellOrder μ μr]
  μ_ord : Ordinal.type μr = (#μ).ord
  μ_strong_limit : (#μ).IsStrongLimit
  κ_lt_μ : (#κ) < (#μ)
  κ_le_μ_cof : (#κ) ≤ (#μ).ord.cof

export Params (Λ Λr Λwf Λ_ord Λ_limit κ κ_regular κr κwf κ_ord Λ_lt_κ μ μr μwf μ_ord μr μ_strong_limit
  κ_lt_μ κ_le_μ_cof)

/-!
### Explicit parameters

There exists valid parameters for the model. The smallest parameters are
* `Λ := ℵ_0`
* `κ := ℵ_1`
* `μ = ℶ_{ω_1}`.
-/

-- TODO: Remove the ordering on `κ`.
example : Params.{0} where
  Λ := ℕ
  Λr := (· < ·)
  Λwf := inferInstance
  Λ_ord := by simp only [mk_denumerable, ord_aleph0, Ordinal.type_nat_lt]
  Λ_limit := by rw [mk_denumerable]; exact isLimit_aleph0
  κ := (aleph 1).ord.out.α
  κr := (aleph 1).ord.out.r
  κwf := (aleph 1).ord.out.wo
  κ_ord := by simp
  κ_regular := by rw [mk_ordinal_out, card_ord]; exact isRegular_aleph_one
  Λ_lt_κ := by rw [mk_denumerable, mk_ordinal_out, card_ord]; exact aleph0_lt_aleph_one
  μ := (beth <| ord <| aleph 1).ord.out.α
  μr := (beth <| ord <| aleph 1).ord.out.r
  μwf := (beth <| ord <| aleph 1).ord.out.wo
  μ_ord := by simp
  μ_strong_limit := by
    simp only [Cardinal.card_ord, Cardinal.mk_ordinal_out]
    exact isStrongLimit_beth (Ordinal.IsLimit.isSuccLimit (ord_aleph_isLimit _))
  κ_lt_μ := by
    simp only [mk_out, mk_ordinal_out, card_ord]
    exact (aleph_le_beth _).trans_lt (beth_strictMono (ord_aleph_isLimit _).one_lt)
  κ_le_μ_cof := by
    simp only [mk_out, mk_ordinal_out, card_ord]
    rw [beth_normal.cof_eq (ord_isLimit <| aleph0_le_aleph 1)]
    exact isRegular_aleph_one.2

theorem noMaxOrder_of_ordinal_type_eq {α : Type u} [Preorder α] [Infinite α] [IsWellOrder α (· < ·)]
    (h : Ordinal.type ((· < ·) : α → α → Prop) = (#α).ord) : NoMaxOrder α := by
  refine ⟨fun a => ?_⟩
  have := (Ordinal.succ_lt_of_isLimit ?_).mpr (Ordinal.typein_lt_type (· < ·) a)
  · obtain ⟨b, hb⟩ := Ordinal.typein_surj (· < ·) this
    refine ⟨b, ?_⟩
    have := Order.lt_succ (Ordinal.typein (fun x y => x < y) a)
    rw [← hb, Ordinal.typein_lt_typein] at this
    exact this
  · rw [h]
    exact Cardinal.ord_isLimit (Cardinal.infinite_iff.mp inferInstance)

noncomputable def succOrderOfIsWellOrder (α : Type u) [Preorder α] [Infinite α]
    [inst : IsWellOrder α (· < ·)] (h : Ordinal.type ((· < ·) : α → α → Prop) = (#α).ord) :
    SuccOrder α where
  succ := inst.toIsWellFounded.wf.succ
  le_succ a := le_of_lt (WellFounded.lt_succ _ ((noMaxOrder_of_ordinal_type_eq h).exists_gt a))
  max_of_succ_le ha hb :=
    (ha.not_lt (WellFounded.lt_succ _ ((noMaxOrder_of_ordinal_type_eq h).exists_gt _))).elim
  succ_le_of_lt := by
    intro a b ha
    by_contra hb
    obtain hab | hab | hab :=
      inst.toIsTrichotomous.trichotomous (inst.toIsWellFounded.wf.succ a) b
    · exact hb hab.le
    · exact hb hab.le
    · rw [WellFounded.lt_succ_iff ((noMaxOrder_of_ordinal_type_eq h).exists_gt a)] at hab
      obtain (hab | hab) := hab
      exact ha.not_lt hab
      exact ha.ne hab.symm
  le_of_lt_succ := by
    intro a b ha
    rw [WellFounded.lt_succ_iff ((noMaxOrder_of_ordinal_type_eq h).exists_gt _)] at ha
    obtain (ha | ha) := ha
    exact ha.le
    exact ha.le

variable [Params.{u}] {ι α β : Type u}

/-- To allow Lean's type checker to see that the ordering `Λr` is a well-ordering without having to
explicitly write `Λwf` everywhere, we declare it as an instance. -/
instance : IsWellOrder Λ Λr :=
  Λwf

instance : IsWellOrder κ κr :=
  κwf

instance : IsWellOrder μ μr :=
  μwf

/-- We can deduce from the well-ordering `Λwf` that `Λ` is linearly ordered. -/
instance : LinearOrder Λ :=
  linearOrderOfSTO Λr

instance : LinearOrder κ :=
  linearOrderOfSTO κr

instance : LinearOrder μ :=
  linearOrderOfSTO μr

instance : IsWellOrder Λ (· < ·) :=
  Λwf

instance : IsWellOrder κ (· < ·) :=
  κwf

instance : IsWellOrder μ (· < ·) :=
  μwf

/-- We deduce that `Λ` has a well-founded relation. -/
instance : WellFoundedRelation Λ :=
  IsWellOrder.toHasWellFounded (hwo := Λwf)

instance : WellFoundedRelation κ :=
  IsWellOrder.toHasWellFounded (hwo := κwf)

instance : WellFoundedRelation μ :=
  IsWellOrder.toHasWellFounded (hwo := μwf)

theorem κ_le_μ : (#κ) ≤ (#μ) :=
  κ_lt_μ.le

noncomputable instance : Inhabited Λ :=
  @Classical.inhabited_of_nonempty _ <| mk_ne_zero_iff.1 Λ_limit.1

noncomputable instance : Inhabited κ :=
  @Classical.inhabited_of_nonempty _ <| mk_ne_zero_iff.1 κ_regular.pos.ne'

noncomputable instance : Inhabited μ :=
  @Classical.inhabited_of_nonempty _ <| mk_ne_zero_iff.1 μ_strong_limit.1

instance : Infinite Λ :=
  Cardinal.infinite_iff.mpr Λ_limit.aleph0_le

instance : Infinite κ :=
  Cardinal.infinite_iff.mpr κ_regular.aleph0_le

instance : Infinite μ :=
  Cardinal.infinite_iff.mpr μ_strong_limit.isLimit.aleph0_le

instance : NoMaxOrder Λ :=
  noMaxOrder_of_ordinal_type_eq Λ_ord

instance : NoMaxOrder μ :=
  noMaxOrder_of_ordinal_type_eq μ_ord

noncomputable instance : SuccOrder Λ :=
  succOrderOfIsWellOrder Λ Λ_ord

noncomputable instance : SuccOrder μ :=
  succOrderOfIsWellOrder μ μ_ord

/-- Either the base type or a proper type index (an element of `Λ`).
The base type is written `⊥`. -/
@[reducible]
def TypeIndex :=
  WithBot Λ

@[simp]
theorem mk_typeIndex : #TypeIndex = #Λ :=
  mk_option.trans <| add_eq_left Λ_limit.aleph0_le <| one_le_aleph0.trans Λ_limit.aleph0_le

/- Since `Λ` is well-ordered, so is `Λ` together with the base type `⊥`.
This allows well founded recursion on type indices. -/
noncomputable instance : LinearOrder TypeIndex :=
  linearOrderOfSTO (· < ·)

noncomputable instance : WellFoundedRelation TypeIndex :=
  IsWellOrder.toHasWellFounded

noncomputable instance : WellFoundedLT TypeIndex :=
  inferInstance

section Small

variable {f : α → β} {s t : Set α}

/-- A set is small if its cardinality is strictly less than `κ`. -/
def Small (s : Set α) : Prop :=
  (#s) < (#κ)

theorem Small.lt : Small s → (#s) < (#κ) :=
  id

theorem Set.Subsingleton.small {α : Type _} {s : Set α} (hs : s.Subsingleton) : Small s :=
  hs.cardinal_mk_le_one.trans_lt <| one_lt_aleph0.trans_le κ_regular.aleph0_le

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
  (mk_union_le _ _).trans_lt <| add_lt_of_lt κ_regular.aleph0_le hs ht

theorem Small.symmDiff (hs : Small s) (ht : Small t) : Small (s ∆ t) :=
  (hs.union ht).mono symmDiff_subset_union

theorem Small.symmDiff_iff (hs : Small s) : Small t ↔ Small (s ∆ t) :=
  ⟨hs.symmDiff, fun ht => by simpa only [symmDiff_symmDiff_self'] using ht.symmDiff hs⟩

theorem small_iUnion (hι : (#ι) < (#κ)) {f : ι → Set α} (hf : ∀ i, Small (f i)) :
    Small (⋃ i, f i) :=
  (mk_iUnion_le _).trans_lt <|
    mul_lt_of_lt κ_regular.aleph0_le hι <| iSup_lt_of_isRegular κ_regular hι hf

theorem small_iUnion_Prop {p : Prop} {f : p → Set α} (hf : ∀ i, Small (f i)) : Small (⋃ i, f i) :=
  by by_cases p <;> simp [h, hf _]

protected theorem Small.bUnion {s : Set ι} (hs : Small s) {f : ∀ i ∈ s, Set α}
    (hf : ∀ (i) (hi : i ∈ s), Small (f i hi)) : Small (⋃ (i) (hi : i ∈ s), f i hi) :=
  (mk_bUnion_le' _ _).trans_lt <|
    mul_lt_of_lt κ_regular.aleph0_le hs <| iSup_lt_of_isRegular κ_regular hs fun _ => hf _ _

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

end Small

section IsNear

variable {s t u : Set α}

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

theorem IsNear.κ_le (h : IsNear s t) (hs : (#κ) ≤ (#s)) : (#κ) ≤ (#(t : Set α)) := by
  by_contra ht
  rw [not_le] at ht
  have := h.symm
  rw [← Small.isNear_iff ht] at this
  exact (lt_iff_not_ge _ _).mp this hs

theorem IsNear.mk_inter (h : IsNear s t) (hs : (#κ) ≤ (#s)) : (#κ) ≤ (#(s ∩ t : Set α)) := by
  rw [IsNear, symmDiff_eq_sup_sdiff_inf] at h
  exact le_of_not_gt fun hst =>
    lt_irrefl _
      (((hs.trans (mk_le_mk_of_subset (subset_union_left _ _))).trans
            (le_mk_diff_add_mk (s ∪ t) (s ∩ t))).trans_lt
        (add_lt_of_lt κ_regular.aleph0_le h hst))

end IsNear

end ConNF
