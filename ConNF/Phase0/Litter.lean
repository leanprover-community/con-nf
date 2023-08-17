import Mathlib.Data.Set.Pointwise.SMul
import ConNF.Mathlib.Equiv
import ConNF.Mathlib.Logic
import ConNF.Phase0.Params

#align_import phase0.litter

/-!
# Litters, near-litters

In this file, we define litters and near-litters.

Litters are the parts of an indexed partition of `con_nf.atom`. Their precise definition can be
considered opaque, as we only care about the fact that their cardinality is `κ`.

## Main declarations

* `con_nf.litter`: The `i`-th litter.
* `con_nf.is_near_litter`: A set is a `i`-near-litter if it is near the `i`-th litter.
-/


open Cardinal Cardinal.IsRegular Equiv Equiv.Perm Function Set

open scoped Cardinal Pointwise

universe u

namespace ConNF

variable [Params.{u}] {α β : Type u}

variable {i j : Litter} {s t : Set Atom}

/-- The set corresponding to the `i`-th litter.

We define a litter as the set of elements of the base type `τ₋₁` where the first element of the pair
is `i`. However, as noted above, the definition can be viewed as opaque, since its cardinality is
the only interesting feature. -/
def litterSet (i : Litter) : Set Atom :=
  {p | p.1 = i}

@[simp]
theorem mem_litterSet {a : Atom} {i : Litter} : a ∈ litterSet i ↔ a.1 = i :=
  Iff.rfl

def litterSetEquiv (L : Litter) : litterSet L ≃ κ :=
  ⟨fun x => x.1.2, fun k => ⟨(L, k), rfl⟩, fun x => Subtype.ext <| Prod.ext x.2.symm rfl, fun k =>
    rfl⟩

/-- Each litter has cardinality `κ`. -/
@[simp]
theorem mk_litterSet (i : Litter) : (#litterSet i) = (#κ) :=
  Cardinal.eq.2 ⟨litterSetEquiv i⟩

/-- Two litters with different indices are disjoint. -/
theorem pairwise_disjoint_litterSet : Pairwise (Disjoint on litterSet) := fun i j h =>
  disjoint_left.2 fun x hi hj => h <| hi.symm.trans hj

theorem eq_of_mem_litterSet_of_mem_litterSet {a : Atom} (hi : a ∈ litterSet i)
    (hj : a ∈ litterSet j) : i = j :=
  pairwise_disjoint_litterSet.Eq <| not_disjoint_iff.2 ⟨_, hi, hj⟩

theorem litterSet_symmDiff_litterSet (h : i ≠ j) :
    litterSet i ∆ litterSet j = litterSet i ∪ litterSet j :=
  (pairwise_disjoint_litterSet h).symmDiff_eq_sup

def litterSetRelIso (L : Litter) : ((· < ·) : litterSet L → litterSet L → Prop) ≃r κr :=
  by
  refine' ⟨litter_set_equiv L, _⟩
  rintro ⟨⟨La, a⟩, ha⟩ ⟨⟨Lb, b⟩, hb⟩
  cases ha
  cases hb
  constructor
  · intro h
    exact Prod.Lex.right L h
  · rintro (⟨_, _, hL⟩ | ⟨_, hab⟩)
    cases lt_irrefl _ hL
    exact hab

noncomputable def litterSetOrderIso (L : Litter) : litterSet L ≃o κ :=
  OrderIso.ofRelIsoLT (litterSetRelIso L)

/-- The order type of a litter is `κ`. -/
theorem Litter.ordinal_type (L : Litter) :
    Ordinal.type ((· < ·) : litterSet L → litterSet L → Prop) = (#κ).ord := by
  rw [← κ_ord, Ordinal.type_eq] <;> exact ⟨litter_set_rel_iso L⟩

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
theorem isNearLitter_set : IsNear (litterSet i) s ↔ IsNearLitter i s :=
  Iff.rfl

/-- If two sets are `i`-near-litters, they are near each other.
This is because they are both near litter `i`, and nearness is transitive. -/
theorem IsNearLitter.near (hs : IsNearLitter i s) (ht : IsNearLitter i t) : IsNear s t :=
  hs.symm.trans ht

theorem IsNearLitter.mk_eq_κ (hs : IsNearLitter i s) : (#s) = (#κ) :=
  ((le_mk_diff_add_mk _ _).trans <|
        add_le_of_le κ_regular.aleph0_le (hs.mono <| subset_union_right _ _).lt.le
          (mk_litterSet _).le).eq_of_not_lt
    fun h =>
    ((mk_litterSet _).symm.trans_le <| le_mk_diff_add_mk _ _).not_lt <|
      add_lt_of_lt κ_regular.aleph0_le (hs.mono <| subset_union_left _ _) h

protected theorem IsNearLitter.nonempty (hs : IsNearLitter i s) : s.Nonempty := by
  rw [← nonempty_coe_sort, ← mk_ne_zero_iff, hs.mk_eq_κ]; exact κ_regular.pos.ne'

/-- A litter is only a near-litter to itself. -/
@[simp]
theorem isNearLitter_litterSet_iff : IsNearLitter i (litterSet j) ↔ i = j :=
  by
  refine' ⟨fun h => _, _⟩
  · by_contra'
    refine' ((mk_litter_set i).symm.trans_le <| mk_le_mk_of_subset _).not_lt h
    change litter_set i ≤ _
    exact (le_symmDiff_iff_left _ _).2 (pairwise_disjoint_litter_set this)
  · rintro rfl
    exact is_near_litter_litter_set _

/-- A set is near at most one litter. -/
theorem IsNearLitter.unique {s : Set Atom} (hi : IsNearLitter i s) (hj : IsNearLitter j s) :
    i = j :=
  isNearLitter_litterSet_iff.1 <| hi.trans hj.symm

/-- There are `μ` near-litters near the `i`-th litter. -/
@[simp]
theorem mk_near_litter' (i : Litter) : (#{ s // IsNearLitter i s }) = (#μ) :=
  by
  refine' (le_antisymm _ _).trans mk_atom
  · refine' le_of_le_of_eq _ (mk_subset_mk_lt_cof <| by simp_rw [mk_atom]; exact μ_strong_limit.2)
    rw [mk_atom]
    exact
      (Cardinal.mk_congr <|
            subtype_equiv ((symmDiff_right_involutive <| litter_set i).toPerm _) fun s =>
              Iff.rfl).trans_le
        ⟨Subtype.impEmbedding _ _ fun s => κ_le_μ_cof.trans_lt'⟩
  refine' ⟨⟨fun a => ⟨litter_set i ∆ {a}, _⟩, fun a b h => _⟩⟩
  · rw [is_near_litter, is_near, Small, symmDiff_symmDiff_cancel_left, mk_singleton]
    exact one_lt_aleph_0.trans_le κ_regular.aleph_0_le
  · exact singleton_injective (symmDiff_right_injective _ <| by convert congr_arg Subtype.val h)

/-- The type of near-litters. -/
def NearLitter : Type _ :=
  Σ i, { s // IsNearLitter i s }

namespace NearLitter

variable {N₁ N₂ : NearLitter}

instance : SetLike NearLitter Atom where
  coe N := N.2
  coe_injective' := by rintro ⟨i, N₁, h₁⟩ ⟨j, N₂, h₂⟩ (rfl : N₁ = N₂); have := h₁.unique h₂;
    subst this

@[simp]
theorem coe_mk (i : Litter) (s : { s // IsNearLitter i s }) :
    @coe NearLitter (Set Atom) _ ⟨i, s⟩ = s :=
  rfl

@[ext]
theorem ext (h₁ : N₁.1 = N₂.1) (h₂ : (N₁ : Set Atom) = N₂) : N₁ = N₂ := by cases N₁; cases N₂;
  dsimp at h₁ ; subst h₁; rw [SetLike.coe_injective h₂]

/-- Reinterpret a near-litter as a product of a litter and a set of atoms. -/
@[simps]
def toProd (N : NearLitter) : Litter × Set Atom :=
  (N.1, N.2)

theorem toProd_injective : Injective toProd := by rintro ⟨i, s⟩ ⟨j, t⟩ h; rw [Prod.ext_iff] at h ;
  exact ext h.1 h.2

@[simp]
protected theorem isNearLitter (N : NearLitter) (i : Litter) : IsNearLitter i N ↔ N.fst = i :=
  ⟨IsNearLitter.unique N.snd.Prop, by rintro rfl; exact N.2.2⟩

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
theorem mk_nearLitter : (#NearLitter) = (#μ) :=
  by
  simp only [near_litter, mk_sigma, mk_near_litter', sum_const, mk_litter, lift_id]
  exact mul_eq_left (κ_regular.aleph_0_le.trans κ_le_μ) le_rfl μ_strong_limit.ne_zero

/-- The *local cardinal* of a litter is the set of all near-litters to that litter. -/
def localCardinal (i : Litter) : Set NearLitter :=
  {N : NearLitter | N.1 = i}

@[simp]
theorem mem_localCardinal {i : Litter} {N : NearLitter} : N ∈ localCardinal i ↔ N.1 = i :=
  Iff.rfl

theorem localCardinal_nonempty (i : Litter) : (localCardinal i).Nonempty :=
  ⟨⟨i, litterSet _, isNearLitter_litterSet _⟩, rfl⟩

theorem localCardinal_disjoint : Pairwise (Disjoint on localCardinal) := fun i j h =>
  disjoint_left.2 fun N hi hj => h <| hi.symm.trans hj

theorem localCardinal_injective : Injective localCardinal :=
  by
  intro i j hij
  by_contra
  have := (local_cardinal_disjoint h).inter_eq
  rw [hij, inter_self] at this
  exact (local_cardinal_nonempty _).ne_empty this

theorem Litter.toNearLitter_mem_localCardinal (i : Litter) : i.toNearLitter ∈ localCardinal i :=
  rfl

@[simp]
theorem mk_localCardinal (i : Litter) : (#localCardinal i) = (#μ) :=
  by
  refine' Eq.trans (Cardinal.eq.2 ⟨⟨_, fun x => ⟨⟨i, x⟩, rfl⟩, _, _⟩⟩) (mk_near_litter' i)
  · rintro ⟨x, rfl : x.1 = i⟩
    exact x.snd
  · rintro ⟨⟨j, S⟩, rfl : j = i⟩
    rfl
  · exact fun x => rfl

inductive NearLitter.IsLitter : NearLitter → Prop
  | mk (L : Litter) : near_litter.is_litter L.toNearLitter

theorem NearLitter.IsLitter.eq_fst_toNearLitter {N : NearLitter} (h : N.IsLitter) :
    N = N.fst.toNearLitter := by cases h <;> rfl

theorem NearLitter.IsLitter.litterSet_eq {N : NearLitter} (h : N.IsLitter) :
    litterSet N.fst = N.snd := by cases h <;> rfl

theorem NearLitter.IsLitter.exists_litter_eq {N : NearLitter} (h : N.IsLitter) :
    ∃ L : Litter, N = L.toNearLitter := by obtain ⟨L⟩ := h <;> exact ⟨L, rfl⟩

theorem NearLitter.not_isLitter {N : NearLitter} (h : ¬N.IsLitter) : litterSet N.fst ≠ N.snd :=
  by
  contrapose! h
  obtain ⟨L, S, hS⟩ := N
  simp only [Subtype.coe_mk] at h
  cases h
  exact near_litter.is_litter.mk _

@[simp]
theorem mk_near_litter'' (N : NearLitter) : (#N) = (#κ) :=
  by
  change (#(N : Set atom)) = _
  rw [← symmDiff_symmDiff_cancel_right (litter_set N.fst) N]
  refine' le_antisymm _ _
  · refine' (mk_le_mk_of_subset symm_diff_subset_union).trans _
    refine' (mk_union_le _ _).trans _
    simp only [mk_litter_set, add_mk_eq_max', max_le_iff, le_refl, and_true_iff]
    rw [symmDiff_comm]
    exact le_of_lt N.2.2
  · refine' le_of_not_lt fun h : Small _ => _
    rw [← small.symm_diff_iff _] at h
    · simpa only [Small, mk_litter_set, lt_self_iff_false] using h
    · rw [symmDiff_comm]
      exact N.2.2

theorem NearLitter.inter_nonempty_of_fst_eq_fst {N₁ N₂ : NearLitter} (h : N₁.fst = N₂.fst) :
    (N₁ ∩ N₂ : Set Atom).Nonempty := by
  by_contra h'
  rw [Set.not_nonempty_iff_eq_empty] at h'
  have := N₁.2.Prop
  simp_rw [h] at this
  have := small.mono (subset_union_left _ _) (N₂.2.Prop.symm.trans this)
  have h : (N₂.snd : Set atom) \ N₁.snd = N₂.snd := by
    rwa [sdiff_eq_left, disjoint_iff_inter_eq_empty, inter_comm]
  rw [h] at this
  have : (#N₂) < (#κ) := this
  rw [mk_near_litter''] at this
  exact lt_irrefl (#κ) this

/-- A near-litter permutation is a permutation of the base type which sends near-litters to
near-litters. It turns out that the images of near-litters near the same litter are themselves near
the same litter. Hence a near-litter permutation induces a permutation of litters, and we keep that
as data for simplicity.

In the paper, this is called a -1-allowable permutation.
The proposition `near` can be interpreted as saying that if `s` is an `i`-near-litter, then its
image under the permutation (`atom_perm`) is near the litter that `i` is mapped to under the litter
permutation (`litter_perm`).

The definition `⇑atom_perm⁻¹ ⁻¹' s` is used instead of `⇑atom_perm '' s` because it has better
definitional properties. For instance, `x ∈ atom_perm⁻¹ ⁻¹' s` is definitionally equal to
`atom_perm x ∈ s`.
-/
structure NearLitterPerm : Type u where
  atomPerm : Perm Atom
  litterPerm : Perm Litter
  near ⦃i : Litter⦄ ⦃s : Set Atom⦄ :
    IsNearLitter i s → IsNearLitter (litter_perm i) (⇑atom_perm⁻¹ ⁻¹' s)

/-- This is the condition that relates the `atom_perm` and the `litter_perm`. This is essentially
the field `near` in the structure `near_litter_perm`, but presented here as a lemma. -/
theorem IsNearLitter.map {f : NearLitterPerm} {s : Set Atom} (h : IsNearLitter i s) :
    IsNearLitter (f.litterPerm i) (⇑f.atomPerm⁻¹ ⁻¹' s) :=
  f.near h

namespace NearLitterPerm

variable {f g : NearLitterPerm}

/-- The map from the type of near-litter permutations to the type of permutations of `τ₋₁` is
injective. That is, if two near-litter permutations have the same action on the base type, they are
equal. -/
theorem atomPerm_injective : Injective NearLitterPerm.atomPerm :=
  by
  rintro ⟨f, f', hf⟩ ⟨g, g', hg⟩ (h : f = g)
  suffices f' = g' by
    subst h
    subst this
  ext i : 1
  exact
    is_near_litter_litter_set_iff.1
      (((hf <| is_near_litter_litter_set _).trans <| by rw [h]).trans
        (hg <| is_near_litter_litter_set _).symm)

/-- An extensionality result for near-litter permutations.
If two near-litter permutations have the same action on the base type, they are equal. -/
@[ext]
theorem ext (h : f.atomPerm = g.atomPerm) : f = g :=
  atomPerm_injective h

/-!
We are going to show that the set of near-litter permutations forms a group.
To do this, we construct several instances, such as the existence of an identity
element or inverse elements.
-/


/-- The identity near-litter permutation. -/
instance : One NearLitterPerm :=
  ⟨⟨1, 1, fun i s => id⟩⟩

/-- Any near-litter permutation admits an inverse, which is also a near-litter permutation. -/
instance : Inv NearLitterPerm :=
  ⟨fun f =>
    ⟨f.atomPerm⁻¹, f.litterPerm⁻¹, fun i s h =>
      by
      have : is_near (⇑f.atom_perm⁻¹ ⁻¹' litter_set (f.litter_perm⁻¹ i)) s :=
        (f.near <| is_near_litter_litter_set _).near (by rwa [apply_inv_self])
      simpa only [preimage_inv, perm.image_inv, preimage_image] using this.image ⇑f.atom_perm⁻¹⟩⟩

/-- Near-litter permutations can be composed. -/
instance : Mul NearLitterPerm :=
  ⟨fun f g => ⟨f.atomPerm * g.atomPerm, f.litterPerm * g.litterPerm, fun i s h => h.map.map⟩⟩

/-- Dividing two permutations `f / g` can be interpreted as `f * g⁻¹`. -/
instance : Div NearLitterPerm :=
  ⟨fun f g =>
    ⟨f.atomPerm / g.atomPerm, f.litterPerm / g.litterPerm, by simp_rw [div_eq_mul_inv];
      exact (f * g⁻¹).near⟩⟩

/-- We can raise near-litter permutations to a natural power since we can do this to
permutations of the base type and the type of litters. -/
instance hasPow : Pow NearLitterPerm ℕ :=
  ⟨fun f n =>
    ⟨f.atomPerm ^ n, f.litterPerm ^ n, by
      induction' n with d hd
      · exact (1 : near_litter_perm).near
      · exact (f * ⟨f.atom_perm ^ d, f.litter_perm ^ d, hd⟩).near⟩⟩

/-- We can raise near-litter permutations to an integer power since we can do this to
permutations of the base type and the type of litters. -/
instance hasZpow : Pow NearLitterPerm ℤ :=
  ⟨fun f n =>
    ⟨f.atomPerm ^ n, f.litterPerm ^ n, by
      cases n
      · exact (f ^ n).near
      · exact (f ^ (n + 1))⁻¹.near⟩⟩

instance : Inhabited NearLitterPerm :=
  ⟨1⟩

/-!
The following lemmas describe how the group of near-litter permutations interacts with the group of
base type permutations and the group of litter permutations. In particular, many group operations,
such as taking the inverse, can be moved out of the near-litter context and into the (simpler) base
permutation or litter permutation context.

The `@[simp]` attribute teaches these results to the `simp` tactic. This means that `simp` will (for
example) prefer group operations to be applied after extracting the base permutation, not before.
-/


@[simp]
theorem atomPerm_one : (1 : NearLitterPerm).atomPerm = 1 :=
  rfl

@[simp]
theorem atomPerm_inv (f : NearLitterPerm) : f⁻¹.atomPerm = f.atomPerm⁻¹ :=
  rfl

@[simp]
theorem atomPerm_hMul (f g : NearLitterPerm) : (f * g).atomPerm = f.atomPerm * g.atomPerm :=
  rfl

@[simp]
theorem atomPerm_div (f g : NearLitterPerm) : (f / g).atomPerm = f.atomPerm / g.atomPerm :=
  rfl

@[simp]
theorem atomPerm_pow (f : NearLitterPerm) (n : ℕ) : (f ^ n).atomPerm = f.atomPerm ^ n :=
  rfl

@[simp]
theorem atomPerm_zpow (f : NearLitterPerm) (n : ℤ) : (f ^ n).atomPerm = f.atomPerm ^ n :=
  rfl

@[simp]
theorem litterPerm_one : (1 : NearLitterPerm).litterPerm = 1 :=
  rfl

@[simp]
theorem litterPerm_inv (f : NearLitterPerm) : f⁻¹.litterPerm = f.litterPerm⁻¹ :=
  rfl

@[simp]
theorem litterPerm_hMul (f g : NearLitterPerm) : (f * g).litterPerm = f.litterPerm * g.litterPerm :=
  rfl

@[simp]
theorem litterPerm_div (f g : NearLitterPerm) : (f / g).litterPerm = f.litterPerm / g.litterPerm :=
  rfl

@[simp]
theorem litterPerm_pow (f : NearLitterPerm) (n : ℕ) : (f ^ n).litterPerm = f.litterPerm ^ n :=
  rfl

@[simp]
theorem litterPerm_zpow (f : NearLitterPerm) (n : ℤ) : (f ^ n).litterPerm = f.litterPerm ^ n :=
  rfl

/-- Near-litter permutations form a group. -/
instance : Group NearLitterPerm :=
  atomPerm_injective.Group _ atomPerm_one atomPerm_hMul atomPerm_inv atomPerm_div atomPerm_pow
    atomPerm_zpow

/-- Near-litter permutations act on the base type via the base permutation. -/
instance : MulAction NearLitterPerm Atom
    where
  smul f := f.atomPerm
  one_smul _ := rfl
  hMul_smul _ _ _ := rfl

/-- Near-litter permutations act on litters via the litter permutation. -/
instance : MulAction NearLitterPerm Litter
    where
  smul f := f.litterPerm
  one_smul _ := rfl
  hMul_smul _ _ _ := rfl

theorem near_smul (f : NearLitterPerm) (h : IsNearLitter i s) : IsNearLitter (f • i) (f • s) := by
  convert f.near h; exact (preimage_inv _ _).symm

instance : SMul NearLitterPerm NearLitter :=
  ⟨fun f N => ⟨f • N.1, f • N, f.near_smul N.2.2⟩⟩

@[simp]
theorem toProd_smul (f : NearLitterPerm) (N : NearLitter) : (f • N).toProd = f • N.toProd :=
  rfl

/-- Near-litter permutations act on near-litters. -/
instance : MulAction NearLitterPerm NearLitter :=
  NearLitter.toProd_injective.MulAction _ toProd_smul

@[simp]
theorem smul_fst (π : NearLitterPerm) (N : NearLitter) : (π • N).fst = π • N.fst :=
  rfl

@[simp]
theorem coe_smul (π : NearLitterPerm) (N : NearLitter) : (↑(π • N) : Set Atom) = π • N :=
  rfl

@[simp]
theorem smul_localCardinal (π : NearLitterPerm) (i : Litter) :
    π • localCardinal i = localCardinal (π • i) := by ext N; simp [mem_smul_set, ← eq_inv_smul_iff]

@[simp]
theorem NearLitter.mem_snd_iff (N : NearLitter) (a : Atom) : a ∈ (N.snd : Set Atom) ↔ a ∈ N :=
  Iff.rfl

@[simp]
theorem NearLitter.not_mem_snd_iff (N : NearLitter) (a : Atom) : a ∉ (N.snd : Set Atom) ↔ a ∉ N :=
  Iff.rfl

theorem smul_nearLitter_eq_smul_symmDiff_smul (π : NearLitterPerm) (N : NearLitter) :
    (π • N : Set Atom) = (π • N.fst.toNearLitter) ∆ (π • litterSet N.fst ∆ N.snd) :=
  by
  ext a : 1
  simp only [litter.coe_to_near_litter, mem_symm_diff, mem_smul_set_iff_inv_smul_mem,
    SetLike.mem_coe, mem_litter_set, near_litter.mem_snd_iff, near_litter.not_mem_snd_iff]
  by_cases (π⁻¹ • a).fst = N.fst <;>
    simp only [h, eq_self_iff_true, true_and_iff, and_true_iff, not_true, and_false_iff,
      false_and_iff, or_false_iff, false_or_iff, Classical.not_not, not_false_iff]

end NearLitterPerm

end ConNF
