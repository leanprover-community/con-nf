import Mathlib.Data.Set.Pointwise.SMul
import ConNF.Mathlib.Equiv
import ConNF.Mathlib.Logic
import ConNF.Phase0.Params

/-!
# Litters, near-litters

In this file, we define litters and near-litters.

Litters are the parts of an indexed partition of `con_nf.atom`. Their precise definition can be
considered opaque, as we only care about the fact that their cardinality is `κ`.

## Main declarations

* `con_nf.litter`: The `i`-th litter.
* `con_nf.is_near_litter`: A set is a `i`-near-litter if it is near the `i`-th litter.
-/

noncomputable section

open Cardinal Cardinal.IsRegular Equiv Equiv.Perm Function Set

open scoped Cardinal Classical Pointwise

universe u

namespace ConNF

variable [Params.{u}] {α β : Type u}

/-- The litters. This is the type indexing the partition of `atom`. -/
structure Litter where
  ν : μ
  β : TypeIndex
  γ : Λ
  β_ne_γ : β ≠ γ

instance : Inhabited Litter :=
  ⟨⟨default, ⊥, default, WithBot.bot_ne_coe⟩⟩

/-- Litters are equivalent to a subtype of a product type. -/
def litterEquiv : Litter ≃ { a : μ ×ₗ TypeIndex ×ₗ Λ // a.2.1 ≠ a.2.2 }
    where
  toFun L := ⟨⟨L.ν, L.β, L.γ⟩, L.β_ne_γ⟩
  invFun L := ⟨L.val.1, L.val.2.1, L.val.2.2, L.prop⟩
  left_inv := by rintro ⟨ν, β, γ, h⟩; rfl
  right_inv := by rintro ⟨⟨ν, β, γ⟩, h⟩; rfl

instance Subtype.isWellOrder {α : Type _} (p : α → Prop) [LT α] [IsWellOrder α (· < ·)] :
    IsWellOrder (Subtype p) (· < ·) :=
  RelEmbedding.isWellOrder (Subtype.relEmbedding (· < ·) p)

-- TODO: Remove after port.
instance Lex.isWellOrder {α β : Type _} [LT α] [LT β] [IsWellOrder α (· < ·)]
    [IsWellOrder β (· < ·)] : IsWellOrder (α ×ₗ β) (· < ·) :=
  instIsWellOrderProdLex

@[simp]
theorem mk_litter : #Litter = #μ := by
  refine
    litterEquiv.cardinal_eq.trans
      (le_antisymm ((Cardinal.mk_subtype_le _).trans_eq ?_)
        ⟨⟨fun ν => ⟨⟨ν, ⊥, default⟩, WithBot.bot_ne_coe⟩, fun ν₁ ν₂ =>
            congr_arg <| Prod.fst ∘ Subtype.val⟩⟩)
  have :=
    mul_eq_left (κ_regular.aleph0_le.trans κ_le_μ) (Λ_lt_κ.le.trans κ_lt_μ.le) Λ_limit.ne_zero
  simp only [Lex, mk_prod, lift_id, mk_typeIndex, mul_eq_self Λ_limit.aleph0_le, this]

/-- Principal segments (sets of the form `{y | y < x}`) have cardinality `< μ`. -/
theorem card_Iio_lt (x : μ) : #(Iio x) < #μ :=
  card_typein_lt (· < ·) x μ_ord.symm

/-- Initial segments (sets of the form `{y | y ≤ x}`) have cardinality `< μ`. -/
theorem card_Iic_lt (x : μ) : #(Iic x) < #μ := by
  rw [← Iio_union_right, mk_union_of_disjoint, mk_singleton]
  · exact (add_one_le_succ _).trans_lt (μ_strong_limit.isLimit.succ_lt (card_Iio_lt x))
  · simp

instance : LT Litter :=
  ⟨litterEquiv ⁻¹'o (· < ·)⟩

/-- Litters are well-ordered. -/
instance Litter.isWellOrder : IsWellOrder Litter (· < ·) :=
  RelIso.IsWellOrder.preimage _ litterEquiv

instance : LinearOrder Litter :=
  linearOrderOfSTO (· < ·)

instance : WellFoundedRelation Litter :=
  IsWellOrder.toHasWellFounded

/-- The base type of the construction, `τ₋₁` in the document. Instead of declaring it as an
arbitrary type of cardinality `μ` and partitioning it into suitable sets of litters afterwards, we
define it as `litter × κ`, which has the correct cardinality and comes with a natural
partition.

These are not 'atoms' in the ZFU, TTTU or NFU sense; they are simply the elements of the model which
are in type `τ₋₁`. -/
def Atom : Type _ :=
  Litter × κ

instance : Inhabited Atom :=
  ⟨⟨default, default⟩⟩

instance : LT Atom :=
  ⟨Prod.Lex (· < ·) (· < ·)⟩

/-- Atoms are well-ordered. -/
instance Atom.isWellOrder : IsWellOrder Atom (· < ·) :=
  instIsWellOrderProdLex

instance : LinearOrder Atom :=
  linearOrderOfSTO (· < ·)

instance : WellFoundedRelation Atom :=
  IsWellOrder.toHasWellFounded

/-- The cardinality of `τ₋₁` is the cardinality of `μ`.
We will prove that all types constructed in our model have cardinality equal to `μ`. -/
@[simp]
theorem mk_atom : #Atom = #μ := by
  simp_rw [Atom, mk_prod, lift_id, mk_litter,
    mul_eq_left (κ_regular.aleph0_le.trans κ_le_μ) κ_le_μ κ_regular.pos.ne']

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

def litterSetEquiv (L : Litter) : litterSet L ≃ κ := ⟨
    fun x => x.1.2,
    fun k => ⟨(L, k), rfl⟩,
    fun x => Subtype.ext <| Prod.ext x.2.symm rfl,
    fun _ => rfl
  ⟩

/-- Each litter has cardinality `κ`. -/
@[simp]
theorem mk_litterSet (i : Litter) : #(litterSet i) = #κ :=
  Cardinal.eq.2 ⟨litterSetEquiv i⟩

/-- Two litters with different indices are disjoint. -/
theorem pairwise_disjoint_litterSet : Pairwise (Disjoint on litterSet) :=
  fun _ _ h => disjoint_left.2 fun _ hi hj => h <| hi.symm.trans hj

theorem eq_of_mem_litterSet_of_mem_litterSet {a : Atom}
    (hi : a ∈ litterSet i) (hj : a ∈ litterSet j) : i = j :=
  pairwise_disjoint_litterSet.eq <| not_disjoint_iff.2 ⟨_, hi, hj⟩

theorem litterSet_symmDiff_litterSet (h : i ≠ j) :
    litterSet i ∆ litterSet j = litterSet i ∪ litterSet j :=
  (pairwise_disjoint_litterSet h).symmDiff_eq_sup

def litterSetRelIso (L : Litter) : ((· < ·) : litterSet L → litterSet L → Prop) ≃r κr := by
  refine ⟨litterSetEquiv L, ?_⟩
  rintro ⟨⟨La, a⟩, ha⟩ ⟨⟨Lb, b⟩, hb⟩
  cases ha
  cases hb
  constructor
  · intro h
    exact Prod.Lex.right La h
  · rintro (⟨_, _, hL⟩ | ⟨_, hab⟩)
    cases lt_irrefl _ hL
    exact hab

noncomputable def litterSetOrderIso (L : Litter) : litterSet L ≃o κ :=
  OrderIso.ofRelIsoLT (litterSetRelIso L)

/-- The order type of a litter is `κ`. -/
theorem Litter.ordinal_type (L : Litter) :
    Ordinal.type ((· < ·) : litterSet L → litterSet L → Prop) = (#κ).ord := by
  rw [← κ_ord, Ordinal.type_eq]; exact ⟨litterSetRelIso L⟩

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
        add_le_of_le κ_regular.aleph0_le (hs.mono <| subset_union_right _ _).lt.le
          (mk_litterSet _).le).eq_of_not_lt
    fun h =>
    ((mk_litterSet _).symm.trans_le <| le_mk_diff_add_mk _ _).not_lt <|
      add_lt_of_lt κ_regular.aleph0_le (hs.mono <| subset_union_left _ _) h

protected theorem IsNearLitter.nonempty (hs : IsNearLitter i s) : s.Nonempty := by
  rw [← nonempty_coe_sort, ← mk_ne_zero_iff, hs.mk_eq_κ]; exact κ_regular.pos.ne'

/-- A litter is only a near-litter to itself. -/
@[simp]
theorem isNearLitter_litterSet_iff : IsNearLitter i (litterSet j) ↔ i = j := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra'
    refine' ((mk_litterSet i).symm.trans_le <| mk_le_mk_of_subset _).not_lt h
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
theorem mk_nearLitter' (i : Litter) : #{s // IsNearLitter i s} = #μ :=
  by
  refine' (le_antisymm _ _).trans mk_atom
  · refine' le_of_le_of_eq _ (mk_subset_mk_lt_cof <| by simp_rw [mk_atom]; exact μ_strong_limit.2)
    rw [mk_atom]
    exact
      (Cardinal.mk_congr <|
            subtypeEquiv ((symmDiff_right_involutive <| litterSet i).toPerm _) fun s =>
              Iff.rfl).trans_le
        ⟨Subtype.impEmbedding _ _ fun s => κ_le_μ_cof.trans_lt'⟩
  refine' ⟨⟨fun a => ⟨litterSet i ∆ {a}, _⟩, fun a b h => _⟩⟩
  · rw [IsNearLitter, IsNear, Small, symmDiff_symmDiff_cancel_left, mk_singleton]
    exact one_lt_aleph0.trans_le κ_regular.aleph0_le
  · exact singleton_injective (symmDiff_right_injective _ <| by convert congr_arg Subtype.val h)

/-- The type of near-litters. -/
def NearLitter : Type _ :=
  Σ i, {s // IsNearLitter i s}

namespace NearLitter

variable {N₁ N₂ : NearLitter}

instance : SetLike NearLitter Atom where
  coe N := N.2
  coe_injective' := by
    rintro ⟨i, N₁, h₁⟩ ⟨j, N₂, h₂⟩ (rfl : N₁ = N₂); have := h₁.unique h₂
    subst this
    rfl

@[simp]
theorem coe_mk (i : Litter) (s : {s // IsNearLitter i s}) :
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
theorem mk_nearLitter : (#NearLitter) = (#μ) :=
  by
  simp only [NearLitter, mk_sigma, mk_nearLitter', sum_const, mk_litter, lift_id]
  exact mul_eq_left (κ_regular.aleph0_le.trans κ_le_μ) le_rfl μ_strong_limit.ne_zero

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
theorem mk_nearLitter'' (N : NearLitter) : (#N) = (#κ) :=
  by
  change (#(N : Set Atom)) = _
  rw [← symmDiff_symmDiff_cancel_right (litterSet N.fst) N]
  refine' le_antisymm _ _
  · refine' (mk_le_mk_of_subset symmDiff_subset_union).trans _
    refine' (mk_union_le _ _).trans _
    simp only [mk_litterSet, add_mk_eq_max', max_le_iff, le_refl, and_true_iff]
    rw [symmDiff_comm]
    exact le_of_lt N.2.2
  · refine' le_of_not_lt fun h : Small _ => _
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
  have : (#N₂) < (#κ) := this
  rw [mk_nearLitter''] at this
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
    IsNearLitter i s → IsNearLitter (litterPerm i) (atomPerm⁻¹.toFun ⁻¹' s)

/-- This is the condition that relates the `atom_perm` and the `litter_perm`. This is essentially
the field `near` in the structure `near_litter_perm`, but presented here as a lemma. -/
theorem IsNearLitter.map {f : NearLitterPerm} {s : Set Atom} (h : IsNearLitter i s) :
    IsNearLitter (f.litterPerm i) (f.atomPerm⁻¹.toFun ⁻¹' s) :=
  f.near h

namespace NearLitterPerm

variable {f g : NearLitterPerm}

/-- The map from the type of near-litter permutations to the type of permutations of `τ₋₁` is
injective. That is, if two near-litter permutations have the same action on the base type, they are
equal. -/
theorem atomPerm_injective : Injective NearLitterPerm.atomPerm := by
  rintro ⟨f, f', hf⟩ ⟨g, g', hg⟩ (h : f = g)
  suffices f' = g' by
    subst h
    subst this
    rfl
  ext i : 1
  exact isNearLitter_litterSet_iff.1
    (((hf <| isNearLitter_litterSet _).trans <| by rw [h]).trans
      (hg <| isNearLitter_litterSet _).symm)

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
  ⟨⟨1, 1, fun _ _ => id⟩⟩

/-- Any near-litter permutation admits an inverse, which is also a near-litter permutation. -/
instance : Inv NearLitterPerm :=
  ⟨fun f =>
    ⟨f.atomPerm⁻¹, f.litterPerm⁻¹, fun i s h => by
      have : IsNear (f.atomPerm⁻¹.toFun ⁻¹' litterSet (f.litterPerm⁻¹ i)) s :=
        (f.near <| isNearLitter_litterSet _).near (by rwa [apply_inv_self])
      simpa only [toFun_as_coe_apply, Perm.image_inv, toFun_as_coe, preimage_inv, preimage_image,
        isNear_litterSet] using this.image f.atomPerm⁻¹.toFun⟩⟩

/-- Near-litter permutations can be composed. -/
instance : Mul NearLitterPerm :=
  ⟨fun f g => ⟨f.atomPerm * g.atomPerm, f.litterPerm * g.litterPerm, fun _ _ h => h.map.map⟩⟩

/-- Dividing two permutations `f / g` can be interpreted as `f * g⁻¹`. -/
instance : Div NearLitterPerm :=
  ⟨fun f g => ⟨f.atomPerm / g.atomPerm, f.litterPerm / g.litterPerm, (f * g⁻¹).near⟩⟩

/-- We can raise near-litter permutations to a natural power since we can do this to
permutations of the base type and the type of litters. -/
instance hasPow : Pow NearLitterPerm ℕ :=
  ⟨fun f n =>
    ⟨f.atomPerm ^ n, f.litterPerm ^ n, by
      induction n with
      | zero =>
          exact (1 : NearLitterPerm).near
      | succ d hd =>
          have := (f * ⟨f.atomPerm ^ d, f.litterPerm ^ d, hd⟩).near
          exact this⟩⟩

/-- We can raise near-litter permutations to an integer power since we can do this to
permutations of the base type and the type of litters. -/
instance hasZpow : Pow NearLitterPerm ℤ :=
  ⟨fun f n =>
    ⟨f.atomPerm ^ n, f.litterPerm ^ n, by
      obtain (n | n) := n
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
  atomPerm_injective.group _ atomPerm_one atomPerm_hMul atomPerm_inv atomPerm_div atomPerm_pow
    atomPerm_zpow

/-- Near-litter permutations act on the base type via the base permutation. -/
instance : MulAction NearLitterPerm Atom
    where
  smul f := f.atomPerm
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Near-litter permutations act on litters via the litter permutation. -/
instance : MulAction NearLitterPerm Litter
    where
  smul f := f.litterPerm
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem near_smul (f : NearLitterPerm) (h : IsNearLitter i s) : IsNearLitter (f • i) (f • s) := by
  convert f.near h using 1
  exact (preimage_inv _ _).symm

instance : SMul NearLitterPerm NearLitter :=
  ⟨fun f N => ⟨f • N.1, f • (N : Set Atom), f.near_smul N.2.2⟩⟩

@[simp]
theorem toProd_smul (f : NearLitterPerm) (N : NearLitter) : (f • N).toProd = f • N.toProd :=
  rfl

/-- Near-litter permutations act on near-litters. -/
instance : MulAction NearLitterPerm NearLitter :=
  NearLitter.toProd_injective.mulAction _ toProd_smul

@[simp]
theorem smul_fst (π : NearLitterPerm) (N : NearLitter) : (π • N).fst = π • N.fst :=
  rfl

@[simp]
theorem coe_smul (π : NearLitterPerm) (N : NearLitter) : ((π • N) : Set Atom) = π • (N : Set Atom) :=
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
    (π • N : Set Atom) = (π • N.fst.toNearLitter : Set Atom) ∆ (π • litterSet N.fst ∆ N.snd) := by
  ext a : 1
  simp only [mem_symmDiff, mem_smul_set_iff_inv_smul_mem, coe_smul]
  tauto

end NearLitterPerm

end ConNF
