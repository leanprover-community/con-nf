import ConNF.Atom.Small
import ConNF.Atom.Atom

universe u

open Cardinal Equiv Function Set

open scoped Cardinal

namespace ConNF

variable [Params.{u}] {α β : Type u} {i j : Litter} {s t : Set Atom}

/-- A `i`-near-litter is a set of small symmetric difference to the `i`-th litter. In other words,
it is near the `i`-th litter.

Note that here we keep track of which litter a set is near; a set cannot be merely a near-litter, it
must be an `i`-near-litter for some `i`. A priori, a set could be an `i`-near-litter and also a
`j`-near-litter, but this is not the case. -/
def IsNearLitter (i : Litter) (s : Set Atom) : Prop :=
  IsNear (litterSet i) s

/-- Litter `i` is a near-litter to litter `i`.
Note that the type of litters is `set atom`, and the type of objects that can be near-litters
is also `set atom`. There is therefore no type-level distinction between elements of a litter
and elements of a near-litter. -/
theorem isNearLitter_litterSet (i : Litter) : IsNearLitter i (litterSet i) :=
  isNear_rfl

@[simp]
theorem isNear_litterSet : IsNear (litterSet i) s ↔ IsNearLitter i s :=
  Iff.rfl

/-- If two sets are `i`-near-litters, they are near each other.
This is because they are both near litter `i`, and nearness is transitive. -/
theorem IsNearLitter.near (hs : IsNearLitter i s) (ht : IsNearLitter i t) : IsNear s t :=
  hs.symm.trans ht

theorem IsNearLitter.mk_eq_κ (hs : IsNearLitter i s) : #s = #κ :=
  ((le_mk_diff_add_mk _ _).trans <|
        add_le_of_le κ_isRegular.aleph0_le (hs.mono <| subset_union_right _ _).lt.le
          (mk_litterSet _).le).eq_of_not_lt
    fun h =>
    ((mk_litterSet _).symm.trans_le <| le_mk_diff_add_mk _ _).not_lt <|
      add_lt_of_lt κ_isRegular.aleph0_le (hs.mono <| subset_union_left _ _) h

protected theorem IsNearLitter.nonempty (hs : IsNearLitter i s) : s.Nonempty := by
  rw [← nonempty_coe_sort, ← mk_ne_zero_iff, hs.mk_eq_κ]; exact κ_isRegular.pos.ne'

/-- A litter is only a near-litter to itself. -/
@[simp]
theorem isNearLitter_litterSet_iff : IsNearLitter i (litterSet j) ↔ i = j := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra'
    refine ((mk_litterSet i).symm.trans_le <| mk_le_mk_of_subset ?_).not_lt h
    change litterSet i ≤ _
    exact (le_symmDiff_iff_left _ _).2 (pairwise_disjoint_litterSet this)
  · rintro rfl
    exact isNearLitter_litterSet _

/-- A set is near at most one litter. -/
theorem IsNearLitter.unique {s : Set Atom} (hi : IsNearLitter i s) (hj : IsNearLitter j s) :
    i = j :=
  isNearLitter_litterSet_iff.1 <| hi.trans hj.symm

/-- There are `μ` near-litters near the `i`-th litter. -/
@[simp]
theorem mk_nearLitter' (i : Litter) : #{ s // IsNearLitter i s } = #μ := by
  refine (le_antisymm ?_ ?_).trans mk_atom
  · have := mk_subset_mk_lt_cof (μ_isStrongLimit.2)
    refine le_of_le_of_eq ?_ (mk_subset_mk_lt_cof <| by simp_rw [mk_atom]; exact μ_isStrongLimit.2)
    rw [mk_atom]
    exact (Cardinal.mk_congr <|
        subtypeEquiv
          ((symmDiff_right_involutive <| litterSet i).toPerm _)
          fun s => Iff.rfl).trans_le
      ⟨Subtype.impEmbedding _ _ fun s => κ_le_μ_ord_cof.trans_lt'⟩
  . refine ⟨⟨fun a => ⟨litterSet i ∆ {a}, ?_⟩, fun a b h => ?_⟩⟩
    · rw [IsNearLitter, IsNear, Small, symmDiff_symmDiff_cancel_left, mk_singleton]
      exact one_lt_aleph0.trans_le κ_isRegular.aleph0_le
    · exact singleton_injective (symmDiff_right_injective _ <| by convert congr_arg Subtype.val h)

/-- The type of near-litters. -/
def NearLitter : Type _ :=
  Σ i, { s // IsNearLitter i s }

namespace NearLitter

variable {N₁ N₂ : NearLitter}

instance : SetLike NearLitter Atom where
  coe N := N.2
  coe_injective' := by
    rintro ⟨i, N₁, h₁⟩ ⟨j, N₂, h₂⟩ (rfl : N₁ = N₂); have := h₁.unique h₂
    subst this
    rfl

@[simp]
theorem coe_mk (i : Litter) (s : { s // IsNearLitter i s }) :
    SetLike.coe (A := NearLitter) ⟨i, s⟩ = s :=
  rfl

@[ext]
theorem ext (h₂ : (N₁ : Set Atom) = N₂) : N₁ = N₂ :=
  SetLike.coe_injective h₂

/-- Reinterpret a near-litter as a product of a litter and a set of atoms. -/
@[simps]
def toProd (N : NearLitter) : Litter × Set Atom :=
  (N.1, N.2)

theorem toProd_injective : Injective toProd := by
  rintro ⟨i, s⟩ ⟨j, t⟩ h
  rw [Prod.ext_iff] at h
  exact ext h.2

@[simp]
protected theorem isNearLitter (N : NearLitter) (i : Litter) : IsNearLitter i N ↔ N.fst = i :=
  ⟨IsNearLitter.unique N.snd.prop, by rintro rfl; exact N.2.2⟩

end NearLitter

namespace Litter

/-- Consider a litter as a near-litter. -/
def toNearLitter (i : Litter) : NearLitter :=
  ⟨i, litterSet i, isNearLitter_litterSet i⟩

noncomputable instance : Inhabited NearLitter :=
  ⟨(default : Litter).toNearLitter⟩

@[simp]
theorem toNearLitter_fst (i : Litter) : i.toNearLitter.fst = i :=
  rfl

@[simp]
theorem coe_toNearLitter (i : Litter) : (i.toNearLitter : Set Atom) = litterSet i :=
  rfl

theorem toNearLitter_injective : Injective Litter.toNearLitter := fun i j hij => by cases hij; rfl

end Litter

/-- There are `μ` near-litters in total. -/
@[simp]
theorem mk_nearLitter : #NearLitter = #μ := by
  simp_rw [NearLitter, mk_sigma, mk_nearLitter', sum_const]
  simp only [NearLitter, mk_sigma, mk_nearLitter', sum_const, mk_litter, lift_id]
  exact mul_eq_left (κ_isRegular.aleph0_le.trans κ_le_μ) le_rfl μ_isStrongLimit.ne_zero

/-- The *local cardinal* of a litter is the set of all near-litters to that litter. -/
def localCardinal (i : Litter) : Set NearLitter :=
  {N : NearLitter | N.1 = i}

@[simp]
theorem mem_localCardinal {i : Litter} {N : NearLitter} : N ∈ localCardinal i ↔ N.1 = i :=
  Iff.rfl

theorem localCardinal_nonempty (i : Litter) : (localCardinal i).Nonempty :=
  ⟨⟨i, litterSet _, isNearLitter_litterSet _⟩, rfl⟩

theorem localCardinal_disjoint : Pairwise (Disjoint on localCardinal) :=
  fun _ _ h => disjoint_left.2 fun _ hi hj => h <| hi.symm.trans hj

theorem localCardinal_injective : Injective localCardinal := by
  intro i j hij
  by_contra h
  have := (localCardinal_disjoint h).inter_eq
  rw [hij, inter_self] at this
  exact (localCardinal_nonempty _).ne_empty this

theorem Litter.toNearLitter_mem_localCardinal (i : Litter) : i.toNearLitter ∈ localCardinal i :=
  rfl

@[simp]
theorem mk_localCardinal (i : Litter) : #(localCardinal i) = #μ := by
  refine Eq.trans (Cardinal.eq.2 ⟨⟨?_, fun x => ⟨⟨i, x⟩, rfl⟩, ?_, ?_⟩⟩) (mk_nearLitter' i)
  · rintro ⟨x, rfl : x.1 = i⟩
    exact x.snd
  · rintro ⟨⟨j, S⟩, rfl : j = i⟩
    rfl
  · exact fun x => rfl

inductive NearLitter.IsLitter : NearLitter → Prop
  | mk (L : Litter) : IsLitter L.toNearLitter

theorem NearLitter.IsLitter.eq_fst_toNearLitter {N : NearLitter} (h : N.IsLitter) :
    N = N.fst.toNearLitter :=
  by cases h; rfl

theorem NearLitter.IsLitter.litterSet_eq {N : NearLitter} (h : N.IsLitter) :
    litterSet N.fst = N.snd :=
  by cases h; rfl

theorem NearLitter.IsLitter.exists_litter_eq {N : NearLitter} (h : N.IsLitter) :
    ∃ L : Litter, N = L.toNearLitter :=
  by obtain ⟨L⟩ := h; exact ⟨L, rfl⟩

theorem NearLitter.not_isLitter {N : NearLitter} (h : ¬N.IsLitter) : litterSet N.fst ≠ N.snd := by
  contrapose! h
  obtain ⟨L, S, hS⟩ := N
  simp only [Subtype.coe_mk] at h
  cases h
  exact NearLitter.IsLitter.mk _

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

theorem NearLitter.inter_nonempty_of_fst_eq_fst {N₁ N₂ : NearLitter} (h : N₁.fst = N₂.fst) :
    (N₁ ∩ N₂ : Set Atom).Nonempty := by
  by_contra h'
  rw [Set.not_nonempty_iff_eq_empty] at h'
  have := N₁.2.prop
  simp_rw [h] at this
  have := Small.mono (subset_union_left _ _) (N₂.2.prop.symm.trans this)
  have h : (N₂.snd : Set Atom) \ N₁.snd = N₂.snd := by
    rwa [sdiff_eq_left, disjoint_iff_inter_eq_empty, inter_comm]
  rw [h] at this
  have : #N₂ < #κ := this
  rw [mk_nearLitter''] at this
  exact lt_irrefl #κ this

end ConNF
