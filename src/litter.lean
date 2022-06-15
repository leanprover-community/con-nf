import mathlib.equiv
import mathlib.order
import params
import algebra.hom.iterate

/-!
# Litters, near-litters

In this file, we define smallness, nearness, litters and near-litters.

Litters are the parts of an indexed partition of `con_nf.base_type`. Their precise definition can be
considered opaque, as we only care about the fact that their cardinality is `κ`.

## Main declarations

* `con_nf.small`: A set is small if its cardinality is strictly less than `κ`.
* `con_nf.is_near`: Two sets are near if their symmetric difference is small.
* `con_nf.litter`: The `i`-th litter.
* `con_nf.is_near_litter`: A set is a `i`-near-litter if it is near the `i`-th litter.
-/

open cardinal cardinal.is_regular equiv equiv.perm function set
open_locale cardinal

universe u

namespace con_nf
variables [params.{u}] {α β : Type u}

open params

section small
variables {f : α → β} {s t : set α}

/-- A set is small if its cardinality is strictly less than `κ`. -/
def small (s : set α) := #s < #κ

/-- The empty set is small. -/
lemma small_empty : small (∅ : set α) := by { rw [small, mk_emptyc], exact κ_regular.pos }

/-- Subsets of small sets are small.
We say that the 'smallness' relation is monotonic. -/
lemma small.mono (h : s ⊆ t) : small t → small s := (cardinal.mk_le_mk_of_subset h).trans_lt

/-- Unions of small subsets are small. -/
lemma small.union (hs : small s) (ht : small t) : small (s ∪ t) :=
(mk_union_le _ _).trans_lt $ add_lt_of_lt κ_regular.aleph_0_le hs ht

/-- The image of a small set under any function `f` is small. -/
lemma small.image : small s → small (f '' s) := mk_image_le.trans_lt

end small

section is_near
variables {s t u : set α}

/-- Two sets are near if their symmetric difference is small. -/
def is_near (s t : set α) : Prop := small (s ∆ t)

/-- A set is near itself. -/
@[refl] lemma is_near_refl (s : set α) : is_near s s :=
by { rw [is_near, symm_diff_self], exact small_empty }

/-- A version of the `is_near_refl` lemma that does not require the set `s` to be given explicitly.
The value of `s` will be inferred automatically by the elaborator. -/
lemma is_near_rfl : is_near s s := is_near_refl _

/-- If `s` is near `t`, then `t` is near `s`. -/
@[symm] lemma is_near.symm (h : is_near s t) : is_near t s := by rwa [is_near, symm_diff_comm]
/-- `s` is near `t` if and only if `t` is near `s`.
In each direction, this is an application of the `is_near.symm` lemma.
Lemmas using `↔` can be used with `rw`, so this form of the result is particularly useful. -/
lemma is_near_comm : is_near s t ↔ is_near t s := ⟨is_near.symm, is_near.symm⟩

/-- Nearness is transitive: if `s` is near `t` and `t` is near `u`, then `s` is near `u`. -/
@[trans] lemma is_near.trans (hst : is_near s t) (htu : is_near t u) : is_near s u :=
(hst.union htu).mono $ symm_diff_triangle s t u

/-- If two sets are near each other, then their images under an arbitrary function are also near. -/
lemma is_near.image (f : α → β) (h : is_near s t) : is_near (f '' s) (f '' t) :=
h.image.mono $ subset_image_symm_diff _ _ _

end is_near

variables {i j : μ}

/-- The `i`-th litter.

We define a litter as the set of elements of the base type `τ₋₁` where the first element of the pair
is `i`. However, as noted above, the definition can be viewed as opaque, since its cardinality is
the only interesting feature. -/
def litter (i : μ) : set base_type := {p | p.1 = i}

/-- Each litter has cardinality `κ`. -/
@[simp] lemma mk_litter (i : μ) : #(litter i) = #κ :=
cardinal.eq.2 ⟨⟨λ x, x.1.2, λ k, ⟨(i, k), rfl⟩, λ x, by { ext, exacts [x.2.symm, rfl] }, λ k, rfl⟩⟩

/-- Two litters with different indices are disjoint. -/
lemma pairwise_disjoint_litter : pairwise (disjoint on litter) :=
λ i j h x hx, h $ hx.1.symm.trans hx.2

/-- A `i`-near-litter is a set of small symmetric difference to the `i`-th litter. In other words,
it is near the `i`-th litter.

Note that here we keep track of which litter a set is near; a set cannot be merely a near-litter, it
must be an `i`-near-litter for some `i`. A priori, a set could be an `i`-near-litter and also a
`j`-near-litter, but this is not the case. -/
def is_near_litter (i : μ) (s : set base_type) : Prop := is_near (litter i) s

/-- Litter `i` is a near-litter to litter `i`.
Note that the type of litters is `set base_type`, and the type of objects that can be near-litters
is also `set base_type`. There is therefore no type-level distinction between elements of a litter
and elements of a near-litter. -/
lemma is_near_litter_litter (i : μ) : is_near_litter i (litter i) := is_near_rfl

/-- If two sets are `i`-near-litters, they are near each other.
This is because they are both near litter `i`, and nearness is transitive. -/
lemma is_near_litter.near {s t : set base_type} (hs : is_near_litter i s)
  (ht : is_near_litter i t) : is_near s t := hs.symm.trans ht

/-- A litter is only a near-litter to itself. -/
@[simp] lemma is_near_litter_litter_iff : is_near_litter i (litter j) ↔ i = j :=
begin
  refine ⟨λ h, _, _⟩,
  { by_contra',
    refine ((mk_litter i).symm.trans_le $ mk_le_mk_of_subset _).not_lt h,
    change litter i ≤ _,
    exact le_symm_diff_iff_left.2 (pairwise_disjoint_litter _ _ this) },
  { rintro rfl,
    exact is_near_litter_litter _ }
end

/-- If two litters are near, they must be the same. -/
@[simp] lemma litter_is_near_litter_iff : is_near (litter i) (litter j) ↔ i = j :=
is_near_litter_litter_iff

/-- A set is near at most one litter. -/
lemma is_near_litter.unique {s : set base_type}
  (hi : is_near_litter i s) (hj : is_near_litter j s) : i = j :=
is_near_litter_litter_iff.1 $ hi.trans hj.symm

/-- There are `μ` near-litters near the `i`-th litter. -/
lemma mk_near_litter (i : μ) : #{s : set base_type // is_near_litter i s} = #μ :=
begin
  refine (le_antisymm _ _).trans mk_base_type,
  { refine le_of_le_of_eq _
     (mk_subset_mk_lt_cof $ by { simp_rw mk_base_type, exact μ_strong_limit.2 }),
    rw mk_base_type,
    exact (cardinal.mk_congr $ subtype_equiv (equiv.symm_diff $ litter i) $ λ s, iff.rfl).trans_le
      ⟨subtype.imp_embedding _ _ $ λ s, κ_le_μ_cof.trans_lt'⟩ },
  refine ⟨⟨λ a, ⟨litter i ∆ {a}, _⟩, λ a b h, _⟩⟩,
  { rw [is_near_litter, is_near, small, symm_diff_symm_diff_self, mk_singleton],
    exact one_lt_aleph_0.trans_le κ_regular.aleph_0_le },
  { exact singleton_injective (symm_diff_left_injective _ $ by convert congr_arg subtype.val h) }
end

/--
A near-litter permutation is a permutation of the base type which sends near-litters to
near-litters. It turns out that the images of near-litters near the same litter are themselves near
the same litter. Hence a near-litter permutation induces a permutation of litters, and we keep that
as data for simplicity.

In the paper, this is called a -1-allowable permutation.
The proposition `near` can be interpreted as saying that if `s` is an `i`-near-litter, then its
image under the permutation (`base_perm`) is near the litter that `i` is mapped to under the litter
permutation (`litter_perm`).

The definition `⇑base_perm⁻¹ ⁻¹' s` is used instead of `⇑base_perm '' s` because it has better
definitional properties. For instance, `x in base_perm⁻¹ ⁻¹' s` is definitionally equal to
`base_perm x ∈ s`.
-/
structure near_litter_perm : Type u :=
(base_perm : perm base_type)
(litter_perm : perm μ)
(near ⦃i : μ⦄ ⦃s : set base_type⦄ :
  is_near_litter i s → is_near_litter (litter_perm i) (⇑base_perm⁻¹ ⁻¹' s))

/-- This is the condition that relates the `base_perm` and the `litter_perm`. This is essentially
the field `near` in the structure `near_litter_perm`, but presented here as a lemma. -/
lemma is_near_litter.map {f : near_litter_perm} {s : set base_type} (h : is_near_litter i s) :
  is_near_litter (f.litter_perm i) (⇑f.base_perm⁻¹ ⁻¹' s) :=
f.near h

namespace near_litter_perm
variables {f g : near_litter_perm}

/-- The map from the type of near-litter permutations to the type of permutations of `τ₋₁` is
injective. That is, if two near-litter permutations have the same action on the base type, they are
equal. -/
lemma base_perm_injective : injective near_litter_perm.base_perm :=
begin
  rintro ⟨f, f', hf⟩ ⟨g, g', hg⟩ (h : f = g),
  suffices : f' = g',
  { subst h,
    subst this },
  ext i,
  exact is_near_litter_litter_iff.1
    (((hf $ is_near_litter_litter _).trans $ by rw h).trans (hg $ is_near_litter_litter _).symm),
end

/-- An extensionality result for near-litter permutations.
If two near-litter permutations have the same action on the base type, they are equal. -/
@[ext] lemma ext (h : f.base_perm = g.base_perm) : f = g := base_perm_injective h

/-!
We are going to show that the set of near-litter permutations forms a group.
To do this, we construct several instances, such as the existence of an identity
element or inverse elements.
-/

/-- The identity near-litter permutation. -/
instance : has_one near_litter_perm := ⟨⟨1, 1, λ i s, id⟩⟩

/-- Any near-litter permutation admits an inverse, which is also a near-litter permutation. -/
instance : has_inv near_litter_perm :=
⟨λ f, ⟨f.base_perm⁻¹, f.litter_perm⁻¹, λ i s h, begin
  have : is_near (⇑f.base_perm⁻¹ ⁻¹' litter (f.litter_perm⁻¹ i)) s,
  { exact (f.near $ is_near_litter_litter _).near (by rwa apply_inv_self) },
  simpa only [preimage_inv, perm.image_inv, preimage_image] using this.image ⇑f.base_perm⁻¹,
end⟩⟩

/-- Near-litter permutations can be composed. -/
instance : has_mul near_litter_perm :=
⟨λ f g, ⟨f.base_perm * g.base_perm, f.litter_perm * g.litter_perm, λ i s h, h.map.map⟩⟩

/-- Dividing two permutations `f / g` can be interpreted as `f⁻¹ * g`. -/
instance : has_div near_litter_perm :=
⟨λ f g, ⟨f.base_perm / g.base_perm, f.litter_perm / g.litter_perm,
  by { simp_rw [div_eq_mul_inv], exact (f * g⁻¹).near }⟩⟩

/-- We can raise near-litter permutations to a natural power since we can do this to
permutations of the base type and the type of litters. -/
instance has_pow : has_pow near_litter_perm ℕ :=
begin
  refine ⟨λ f n, ⟨f.base_perm ^ n, f.litter_perm ^ n, _⟩⟩,
  induction n with d hd,
  { exact (1 : near_litter_perm).near },
  { exact (f * ⟨f.base_perm ^ d, f.litter_perm ^ d, hd⟩).near }
end

/-- We can raise near-litter permutations to an integer power since we can do this to
permutations of the base type and the type of litters. -/
instance has_zpow : has_pow near_litter_perm ℤ :=
begin
  refine ⟨λ f n, ⟨f.base_perm ^ n, f.litter_perm ^ n, _⟩⟩,
  cases n,
  { exact (f ^ n).near },
  { exact (f ^ (n + 1))⁻¹.near }
end

instance : inhabited near_litter_perm := ⟨1⟩

/-!
The following lemmas describe how the group of near-litter permutations interacts with the group of
base type permutations and the group of litter permutations. In particular, many group operations,
such as taking the inverse, can be moved out of the near-litter context and into the (simpler) base
permutation or litter permutation context.

The `@[simp]` attribute teaches these results to the `simp` tactic. This means that `simp` will (for
example) prefer group operations to be applied after extracting the base permutation, not before.
-/

@[simp] lemma base_perm_one : (1 : near_litter_perm).base_perm = 1 := rfl
@[simp] lemma base_perm_inv (f : near_litter_perm) : f⁻¹.base_perm = f.base_perm⁻¹ := rfl
@[simp] lemma base_perm_mul (f g : near_litter_perm) :
  (f * g).base_perm = f.base_perm * g.base_perm := rfl
@[simp] lemma base_perm_div (f g : near_litter_perm) :
  (f / g).base_perm = f.base_perm / g.base_perm := rfl
@[simp] lemma base_perm_pow (f : near_litter_perm) (n : ℕ) : (f ^ n).base_perm = f.base_perm ^ n :=
rfl
@[simp] lemma base_perm_zpow (f : near_litter_perm) (n : ℤ) : (f ^ n).base_perm = f.base_perm ^ n :=
rfl

@[simp] lemma litter_perm_one : (1 : near_litter_perm).litter_perm = 1 := rfl
@[simp] lemma litter_perm_inv (f : near_litter_perm) : f⁻¹.litter_perm = f.litter_perm⁻¹ := rfl
@[simp] lemma litter_perm_mul (f g : near_litter_perm) :
  (f * g).litter_perm = f.litter_perm * g.litter_perm := rfl
@[simp] lemma litter_perm_div (f g : near_litter_perm) :
  (f / g).litter_perm = f.litter_perm / g.litter_perm := rfl
@[simp] lemma litter_perm_pow (f : near_litter_perm) (n : ℕ) :
  (f ^ n).litter_perm = f.litter_perm ^ n := rfl
@[simp] lemma litter_perm_zpow (f : near_litter_perm) (n : ℤ) :
  (f ^ n).litter_perm = f.litter_perm ^ n := rfl

/-- The type of near-litter permutations forms a group. -/
instance : group near_litter_perm :=
base_perm_injective.group _ base_perm_one base_perm_mul base_perm_inv base_perm_div base_perm_pow
  base_perm_zpow

/-- The group of near-litter permutations acts on the base type via the base permutation. -/
instance : mul_action near_litter_perm base_type :=
{ smul := λ f, f.base_perm, one_smul := λ _, rfl, mul_smul := λ _ _ _, rfl }

/-- The group of near-litter permutations acts on litters via the litter permutation. -/
instance : mul_action near_litter_perm μ :=
{ smul := λ f, f.litter_perm, one_smul := λ _, rfl, mul_smul := λ _ _ _, rfl }

end near_litter_perm

/-- A near litter is an index `i : μ` of a litter and a set `s : set base_type`, such that `s` is
an `i`-near-litter.

This allows us to forget which set and which litter we are talking about at the type level, and
hence deal with an arbitrary near-litter. -/
def near_litter : Type* := Σ' i s, is_near_litter i s

/-- If this is satisfied for a near-litter `N`, then `N` is actually a litter. -/
def near_litter.is_litter (N : near_litter) : Prop := N.2.1 = litter N.1

end con_nf
