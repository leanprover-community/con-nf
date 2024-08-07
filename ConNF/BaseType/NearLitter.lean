import ConNF.BaseType.Small
import ConNF.BaseType.Atom

/-!
# Near-litters

In this file, we define near-litters, which are sets with small symmetric difference to a litter.

## Main declarations

* `ConNF.IsNearLitter`: Proposition stating that a set is near a given litter.
* `ConNF.NearLitter`: The type of near-litters.
* `ConNF.Litter.toNearLitter`: Converts a litter to its corresponding near-litter.
* `ConNF.NearLitter.IsLitter`: Proposition stating that a near-litter comes directly from a litter:
    it is of the form `L.toNearLitter` for some litter `L`.
-/

universe u

open Cardinal Equiv Function Set

open scoped Cardinal symmDiff

namespace ConNF

variable [Params.{u}] {L L₁ L₂ : Litter} {s t : Set Atom}

/-- A `L`-near-litter is a set of small symmetric difference to litter `L`. In other words,
it is near litter `L`.

Note that here we keep track of which litter a set is near; a set cannot be merely a near-litter, it
must be an `L`-near-litter for some `L`. A priori, a set could be an `L₁`-near-litter and also a
`L₂`-near-litter, but this is not the case. -/
def IsNearLitter (L : Litter) (s : Set Atom) : Prop :=
  IsNear (litterSet L) s

/-- The litter set corresponding to `L` is a near-litter to litter `L`. -/
theorem isNearLitter_litterSet (L : Litter) : IsNearLitter L (litterSet L) :=
  isNear_rfl

@[simp]
theorem isNear_litterSet : IsNear (litterSet L) s ↔ IsNearLitter L s :=
  Iff.rfl

/-- If two sets are `L`-near-litters, they are near each other.
This is because they are both near litter `L`, and nearness is transitive. -/
theorem IsNearLitter.near (hs : IsNearLitter L s) (ht : IsNearLitter L t) : IsNear s t :=
  hs.symm.trans ht

theorem IsNearLitter.mk_eq_κ (hs : IsNearLitter L s) : #s = #κ :=
  ((le_mk_diff_add_mk _ _).trans <|
        add_le_of_le Params.κ_isRegular.aleph0_le (hs.mono subset_union_right).lt.le
          (mk_litterSet _).le).eq_of_not_lt
    fun h =>
    ((mk_litterSet _).symm.trans_le <| le_mk_diff_add_mk _ _).not_lt <|
      add_lt_of_lt Params.κ_isRegular.aleph0_le (hs.mono subset_union_left) h

protected theorem IsNearLitter.nonempty (hs : IsNearLitter L s) : s.Nonempty := by
  rw [← nonempty_coe_sort, ← mk_ne_zero_iff, hs.mk_eq_κ]
  exact Params.κ_isRegular.pos.ne'

/-- A litter set is only a near-litter to itself. -/
@[simp]
theorem isNearLitter_litterSet_iff : IsNearLitter L₁ (litterSet L₂) ↔ L₁ = L₂ := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra this
    refine ((mk_litterSet L₁).symm.trans_le <| mk_le_mk_of_subset ?_).not_lt h
    change litterSet L₁ ≤ _
    exact (le_symmDiff_iff_left _ _).2 (pairwise_disjoint_litterSet this)
  · rintro rfl
    exact isNearLitter_litterSet _

/-- A set is near at most one litter. -/
theorem IsNearLitter.unique {s : Set Atom} (h₁ : IsNearLitter L₁ s) (h₂ : IsNearLitter L₂ s) :
    L₁ = L₂ :=
  isNearLitter_litterSet_iff.1 <| h₁.trans h₂.symm

/-- There are `μ` near-litters to litter `L`. -/
@[simp]
theorem mk_nearLitter' (L : Litter) : #{ s // IsNearLitter L s } = #μ := by
  refine (le_antisymm ?_ ?_).trans mk_atom
  · have := mk_subset_mk_lt_cof (Params.μ_isStrongLimit.2)
    refine le_of_le_of_eq ?_ (mk_subset_mk_lt_cof ?_)
    · rw [mk_atom]
      exact (Cardinal.mk_congr <|
          subtypeEquiv
            ((symmDiff_right_involutive <| litterSet L).toPerm _)
            fun s => Iff.rfl).trans_le
        ⟨Subtype.impEmbedding _ _ fun s => Params.κ_le_μ_ord_cof.trans_lt'⟩
    · simp_rw [mk_atom]
      exact Params.μ_isStrongLimit.2
  . refine ⟨⟨fun a => ⟨litterSet L ∆ {a}, ?_⟩, fun a b h => ?_⟩⟩
    · rw [IsNearLitter, IsNear, Small, symmDiff_symmDiff_cancel_left, mk_singleton]
      exact one_lt_aleph0.trans_le Params.κ_isRegular.aleph0_le
    · exact singleton_injective (symmDiff_right_injective _ <| by convert congr_arg Subtype.val h)

/-- The type of near-litters. A near-litter is a litter together with a set near it. -/
def NearLitter : Type u :=
  Σ L, { s // IsNearLitter L s }

namespace NearLitter

variable {N₁ N₂ : NearLitter}

instance : SetLike NearLitter Atom where
  coe N := N.2
  coe_injective' := by
    rintro ⟨i, N₁, h₁⟩ ⟨j, N₂, h₂⟩ (rfl : N₁ = N₂); have := h₁.unique h₂
    subst this
    rfl

@[simp]
theorem coe_mk (L : Litter) (s : { s // IsNearLitter L s }) :
    SetLike.coe (A := NearLitter) ⟨L, s⟩ = s :=
  rfl

@[ext]
theorem ext (h₂ : (N₁ : Set Atom) = N₂) : N₁ = N₂ :=
  SetLike.coe_injective h₂

theorem nonempty (N : NearLitter) : Nonempty N := by
  obtain ⟨a, ha⟩ := IsNearLitter.nonempty N.2.2
  exact ⟨a, ha⟩

/-- Reinterpret a near-litter as a product of a litter and a set of atoms. -/
@[simps]
def toProd (N : NearLitter) : Litter × Set Atom :=
  (N.1, N.2)

theorem toProd_injective : Injective toProd := by
  rintro ⟨L₁, s⟩ ⟨L₂, t⟩ h
  rw [Prod.ext_iff] at h
  exact ext h.2

/-- A near-litter `N` is near a given litter `L` if and only if `N` has first projection `L`. -/
@[simp]
protected theorem isNearLitter (N : NearLitter) (L : Litter) : IsNearLitter L N ↔ N.fst = L :=
  ⟨IsNearLitter.unique N.snd.prop, by rintro rfl; exact N.2.2⟩

theorem isNear_iff_fst_eq_fst (N₁ N₂ : NearLitter) :
    IsNear (N₁ : Set Atom) N₂ ↔ N₁.fst = N₂.fst := by
  rw [← N₁.isNearLitter N₂.fst]
  constructor
  · intro h
    exact N₂.snd.prop.trans h.symm
  · intro h
    refine h.symm.trans N₂.snd.prop

end NearLitter

namespace Litter

/-- Convert a litter to its associated near-litter. -/
def toNearLitter (L : Litter) : NearLitter :=
  ⟨L, litterSet L, isNearLitter_litterSet L⟩

instance : Nonempty NearLitter :=
  ⟨(Classical.arbitrary Litter).toNearLitter⟩

@[simp]
theorem toNearLitter_fst (L : Litter) : L.toNearLitter.fst = L :=
  rfl

@[simp]
theorem coe_toNearLitter (L : Litter) : (L.toNearLitter : Set Atom) = litterSet L :=
  rfl

theorem toNearLitter_injective : Injective Litter.toNearLitter :=
  fun i j hij => by cases hij; rfl

end Litter

/-- There are `μ` near-litters in total. -/
@[simp]
theorem mk_nearLitter : #NearLitter = #μ := by
  simp_rw [NearLitter, mk_sigma, mk_nearLitter', sum_const]
  simp only [NearLitter, mk_sigma, mk_nearLitter', sum_const, mk_litter, lift_id]
  exact mul_eq_left
    (Params.κ_isRegular.aleph0_le.trans Params.κ_lt_μ.le)
    le_rfl
    Params.μ_isStrongLimit.ne_zero

/-- There aer `μ` near-litters to a given litter. -/
@[simp]
theorem mk_nearLitter_to (L : Litter) : #{N : NearLitter | N.1 = L} = #μ := by
  refine Eq.trans (Cardinal.eq.2 ⟨⟨?_, fun x => ⟨⟨L, x⟩, rfl⟩, ?_, ?_⟩⟩) (mk_nearLitter' L)
  · rintro ⟨x, rfl : x.1 = L⟩
    exact x.snd
  · rintro ⟨⟨j, S⟩, rfl : j = L⟩
    rfl
  · exact fun x => rfl

/-- This near-litter is of the form `L.toNearLitter`. -/
inductive NearLitter.IsLitter : NearLitter → Prop
  | mk (L : Litter) : IsLitter L.toNearLitter

theorem NearLitter.IsLitter.eq_fst_toNearLitter {N : NearLitter} (h : N.IsLitter) :
    N = N.fst.toNearLitter :=
  by cases h; rfl

theorem NearLitter.IsLitter.litterSet_eq {N : NearLitter} (h : N.IsLitter) :
    litterSet N.fst = N.snd :=
  by cases h; rfl

/-- The main induction rule for near-litters that are litters. -/
theorem NearLitter.IsLitter.exists_litter_eq {N : NearLitter} (h : N.IsLitter) :
    ∃ L : Litter, N = L.toNearLitter :=
  by obtain ⟨L⟩ := h; exact ⟨L, rfl⟩

theorem NearLitter.not_isLitter {N : NearLitter} (h : ¬N.IsLitter) : litterSet N.fst ≠ N.snd := by
  contrapose! h
  obtain ⟨L, S, hS⟩ := N
  simp only [Subtype.coe_mk] at h
  cases h
  exact NearLitter.IsLitter.mk _

theorem NearLitter.not_isLitter' {N : NearLitter} (h : ¬N.IsLitter) : N.fst.toNearLitter ≠ N := by
  contrapose! h
  obtain ⟨L, S, hS⟩ := N
  simp only [Subtype.coe_mk] at h
  cases h
  exact NearLitter.IsLitter.mk _

/-- The size of each near-litter is `κ`. -/
@[simp]
theorem mk_nearLitter'' (N : NearLitter) : #N = #κ := by
  change #(N : Set Atom) = _
  rw [← symmDiff_symmDiff_cancel_right (litterSet N.fst) N]
  refine le_antisymm ?_ ?_
  · refine (mk_le_mk_of_subset symmDiff_subset_union).trans ?_
    refine (mk_union_le _ _).trans ?_
    simp only [mk_litterSet, add_mk_eq_max', max_le_iff, le_refl, and_true_iff]
    rw [symmDiff_comm]
    exact le_of_lt N.2.2
  · refine le_of_not_lt fun h : Small _ => ?_
    rw [← Small.symmDiff_iff _] at h
    · simp only [Small, mk_litterSet, lt_self_iff_false] at h
    · rw [symmDiff_comm]
      exact N.2.2

theorem symmDiff_union_inter {α : Type _} {a b : Set α} : (a ∆ b) ∪ (a ∩ b) = a ∪ b := by
  ext x
  simp only [mem_union, mem_symmDiff, mem_inter_iff]
  tauto

/-- Near-litters to the same litter have `κ`-sized intersection. -/
theorem NearLitter.mk_inter_of_fst_eq_fst {N₁ N₂ : NearLitter} (h : N₁.fst = N₂.fst) :
    #(N₁ ∩ N₂ : Set Atom) = #κ := by
  rw [← isNear_iff_fst_eq_fst] at h
  refine le_antisymm ?_ ?_
  · exact (mk_le_mk_of_subset inter_subset_left).trans (mk_nearLitter'' _).le
  · by_contra! h'
    have := Small.union h h'
    rw [symmDiff_union_inter] at this
    exact (this.mono subset_union_left).not_le (le_of_eq (mk_nearLitter'' N₁).symm)

theorem NearLitter.inter_nonempty_of_fst_eq_fst {N₁ N₂ : NearLitter} (h : N₁.fst = N₂.fst) :
    (N₁ ∩ N₂ : Set Atom).Nonempty := by
  rw [← nonempty_coe_sort, ← mk_ne_zero_iff, mk_inter_of_fst_eq_fst h]
  exact mk_ne_zero κ

/-- Near-litters to different litters have small intersection. -/
theorem NearLitter.inter_small_of_fst_ne_fst {N₁ N₂ : NearLitter} (h : N₁.fst ≠ N₂.fst) :
    Small (N₁ ∩ N₂ : Set Atom) := by
  have := N₁.2.2
  have : (N₁ ∩ N₂ : Set Atom) ⊆ (litterSet N₁.1 ∆ N₁) ∪ (litterSet N₂.1 ∆ N₂)
  · intro a ha
    by_cases ha' : a.1 = N₁.1
    · refine Or.inr (Or.inr ⟨ha.2, ?_⟩)
      intro h'
      exact h (ha'.symm.trans h')
    · exact Or.inl (Or.inr ⟨ha.1, ha'⟩)
  exact Small.mono this (Small.union N₁.2.2 N₂.2.2)

end ConNF
