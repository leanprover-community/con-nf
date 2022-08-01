import mathlib.cardinal
import mathlib.equiv
import phase0.params

/-!
# Litters, near-litters

In this file, we define litters and near-litters.

Litters are the parts of an indexed partition of `con_nf.atom`. Their precise definition can be
considered opaque, as we only care about the fact that their cardinality is `κ`.

## Main declarations

* `con_nf.litter`: The `i`-th litter.
* `con_nf.is_near_litter`: A set is a `i`-near-litter if it is near the `i`-th litter.
-/

open cardinal cardinal.is_regular equiv equiv.perm function set
open_locale cardinal

universe u

namespace con_nf
variables [params.{u}] {α β : Type u}

variables {i j : litter} {s t : set atom}

/-- The set corresponding to the `i`-th litter.

We define a litter as the set of elements of the base type `τ₋₁` where the first element of the pair
is `i`. However, as noted above, the definition can be viewed as opaque, since its cardinality is
the only interesting feature. -/
def litter_set (i : litter) : set atom := {p | p.1 = i}

/-- Each litter has cardinality `κ`. -/
@[simp] lemma mk_litter_set (i : litter) : #(litter_set i) = #κ :=
cardinal.eq.2 ⟨⟨λ x, x.1.2, λ k, ⟨(i, k), rfl⟩, λ x, subtype.ext $ prod.ext x.2.symm rfl, λ k, rfl⟩⟩

/-- Two litters with different indices are disjoint. -/
lemma pairwise_disjoint_litter_set : pairwise (disjoint on litter_set) :=
λ i j h x hx, h $ hx.1.symm.trans hx.2

/-- A `i`-near-litter is a set of small symmetric difference to the `i`-th litter. In other words,
it is near the `i`-th litter.

Note that here we keep track of which litter a set is near; a set cannot be merely a near-litter, it
must be an `i`-near-litter for some `i`. A priori, a set could be an `i`-near-litter and also a
`j`-near-litter, but this is not the case. -/
def is_near_litter (i : litter) (s : set atom) : Prop := is_near (litter_set i) s

/-- Litter `i` is a near-litter to litter `i`.
Note that the type of litters is `set atom`, and the type of objects that can be near-litters
is also `set atom`. There is therefore no type-level distinction between elements of a litter
and elements of a near-litter. -/
lemma is_near_litter_litter_set (i : litter) : is_near_litter i (litter_set i) := is_near_rfl

/-- If two sets are `i`-near-litters, they are near each other.
This is because they are both near litter `i`, and nearness is transitive. -/
lemma is_near_litter.near (hs : is_near_litter i s) (ht : is_near_litter i t) : is_near s t :=
hs.symm.trans ht

lemma is_near_litter.mk_eq_κ (hs : is_near_litter i s) : #s = #κ :=
((le_mk_diff_add_mk _ _).trans $ add_le_of_le κ_regular.aleph_0_le
  (hs.mono $ subset_union_right _ _).lt.le (mk_litter_set _).le).eq_of_not_lt $ λ h,
    ((mk_litter_set _).symm.trans_le $ le_mk_diff_add_mk _ _).not_lt $
      add_lt_of_lt κ_regular.aleph_0_le (hs.mono $ subset_union_left _ _) h

protected lemma is_near_litter.nonempty (hs : is_near_litter i s) : s.nonempty :=
by { rw [←nonempty_coe_sort, ←mk_ne_zero_iff, hs.mk_eq_κ], exact κ_regular.pos.ne' }

/-- A litter is only a near-litter to itself. -/
@[simp] lemma is_near_litter_litter_set_iff : is_near_litter i (litter_set j) ↔ i = j :=
begin
  refine ⟨λ h, _, _⟩,
  { by_contra',
    refine ((mk_litter_set i).symm.trans_le $ mk_le_mk_of_subset _).not_lt h,
    change litter_set i ≤ _,
    exact (le_symm_diff_iff_left _ _).2 (pairwise_disjoint_litter_set _ _ this) },
  { rintro rfl,
    exact is_near_litter_litter_set _ }
end

/-- A set is near at most one litter. -/
lemma is_near_litter.unique {s : set atom} (hi : is_near_litter i s) (hj : is_near_litter j s) :
  i = j :=
is_near_litter_litter_set_iff.1 $ hi.trans hj.symm

/-- There are `μ` near-litters near the `i`-th litter. -/
@[simp] lemma mk_near_litter' (i : litter) : #{s // is_near_litter i s} = #μ :=
begin
  refine (le_antisymm _ _).trans mk_atom,
  { refine le_of_le_of_eq _
     (mk_subset_mk_lt_cof $ by { simp_rw mk_atom, exact μ_strong_limit.2 }),
    rw mk_atom,
    exact (cardinal.mk_congr $ subtype_equiv
      ((symm_diff_right_involutive $ litter_set i).to_perm _) $ λ s, iff.rfl).trans_le
        ⟨subtype.imp_embedding _ _ $ λ s, κ_le_μ_cof.trans_lt'⟩ },
  refine ⟨⟨λ a, ⟨litter_set i ∆ {a}, _⟩, λ a b h, _⟩⟩,
  { rw [is_near_litter, is_near, small, symm_diff_symm_diff_cancel_left, mk_singleton],
    exact one_lt_aleph_0.trans_le κ_regular.aleph_0_le },
  { exact singleton_injective (symm_diff_right_injective _ $ by convert congr_arg subtype.val h) }
end

/-- The type of near-litters. -/
def near_litter : Type* := Σ i, {s // is_near_litter i s}

/-- Consider a litter as a near-litter. -/
def litter.to_near_litter (i : litter) : near_litter :=
⟨i, litter_set i, is_near_litter_litter_set i⟩

lemma litter.to_near_litter_injective : injective litter.to_near_litter :=
λ i j hij, by { cases hij, refl }

/-- There are `μ` near-litters in total. -/
@[simp] lemma mk_near_litter : #near_litter = #μ :=
by { simp only [near_litter, mk_sigma, mk_near_litter', sum_const, mk_litter, lift_id],
  exact mul_eq_left (κ_regular.aleph_0_le.trans κ_le_μ) le_rfl μ_strong_limit.ne_zero }

/-- The *local cardinal* of a litter is the set of all near-litters to that litter. -/
def local_cardinal (i : litter) : set near_litter := {N : near_litter | N.1 = i}

@[simp] lemma mem_local_cardinal {i : litter} {N : near_litter} : N ∈ local_cardinal i ↔ N.1 = i :=
iff.rfl

lemma local_cardinal_nonempty (i : litter) : (local_cardinal i).nonempty :=
⟨⟨i, litter_set _, is_near_litter_litter_set _⟩, rfl⟩

lemma local_cardinal_disjoint : pairwise (disjoint on local_cardinal) :=
λ i j h N hN, h $ hN.1.symm.trans hN.2

lemma local_cardinal_injective : injective local_cardinal :=
begin
  intros i j hij,
  by_contradiction,
  have := local_cardinal_disjoint i j h,
  rw [(on), disjoint, hij, inf_idem, le_bot_iff, bot_eq_empty, ← not_nonempty_iff_eq_empty] at this,
  exact this (local_cardinal_nonempty _)
end

lemma litter.to_near_litter_mem_local_cardinal (i : litter) : i.to_near_litter ∈ local_cardinal i :=
by exact rfl

@[simp] lemma mk_local_cardinal (i : litter) : #(local_cardinal i) = #μ :=
begin
  refine eq.trans (cardinal.eq.2 ⟨⟨_, λ x, ⟨⟨i, x⟩, rfl⟩, _, _⟩⟩) (mk_near_litter' i),
  { rintro ⟨x, (rfl : x.1 = i)⟩,
    exact x.snd },
  { rintro ⟨⟨j, S⟩, (rfl : j = i)⟩,
    refl },
  { exact λ x, rfl }
end

/--
A near-litter permutation is a permutation of the base type which sends near-litters to
near-litters. It turns out that the images of near-litters near the same litter are themselves near
the same litter. Hence a near-litter permutation induces a permutation of litters, and we keep that
as data for simplicity.

In the paper, this is called a -1-allowable permutation.
The proposition `near` can be interpreted as saying that if `s` is an `i`-near-litter, then its
image under the permutation (`atom_perm`) is near the litter that `i` is mapped to under the litter
permutation (`litter_perm`).

The definition `⇑atom_perm⁻¹ ⁻¹' s` is used instead of `⇑atom_perm '' s` because it has better
definitional properties. For instance, `x in atom_perm⁻¹ ⁻¹' s` is definitionally equal to
`atom_perm x ∈ s`.
-/
structure near_litter_perm : Type u :=
(atom_perm : perm atom)
(litter_perm : perm litter)
(near ⦃i : litter⦄ ⦃s : set atom⦄ :
  is_near_litter i s → is_near_litter (litter_perm i) (⇑atom_perm⁻¹ ⁻¹' s))

/-- This is the condition that relates the `atom_perm` and the `litter_perm`. This is essentially
the field `near` in the structure `near_litter_perm`, but presented here as a lemma. -/
lemma is_near_litter.map {f : near_litter_perm} {s : set atom} (h : is_near_litter i s) :
  is_near_litter (f.litter_perm i) (⇑f.atom_perm⁻¹ ⁻¹' s) :=
f.near h

namespace near_litter_perm
variables {f g : near_litter_perm}

/-- The map from the type of near-litter permutations to the type of permutations of `τ₋₁` is
injective. That is, if two near-litter permutations have the same action on the base type, they are
equal. -/
lemma atom_perm_injective : injective near_litter_perm.atom_perm :=
begin
  rintro ⟨f, f', hf⟩ ⟨g, g', hg⟩ (h : f = g),
  suffices : f' = g',
  { subst h,
    subst this },
  ext i,
  exact is_near_litter_litter_set_iff.1 (((hf $ is_near_litter_litter_set _).trans $ by rw h).trans
    (hg $ is_near_litter_litter_set _).symm),
end

/-- An extensionality result for near-litter permutations.
If two near-litter permutations have the same action on the base type, they are equal. -/
@[ext] lemma ext (h : f.atom_perm = g.atom_perm) : f = g := atom_perm_injective h

/-!
We are going to show that the set of near-litter permutations forms a group.
To do this, we construct several instances, such as the existence of an identity
element or inverse elements.
-/

/-- The identity near-litter permutation. -/
instance : has_one near_litter_perm := ⟨⟨1, 1, λ i s, id⟩⟩

/-- Any near-litter permutation admits an inverse, which is also a near-litter permutation. -/
instance : has_inv near_litter_perm :=
⟨λ f, ⟨f.atom_perm⁻¹, f.litter_perm⁻¹, λ i s h, begin
  have : is_near (⇑f.atom_perm⁻¹ ⁻¹' litter_set (f.litter_perm⁻¹ i)) s,
  { exact (f.near $ is_near_litter_litter_set _).near (by rwa apply_inv_self) },
  simpa only [preimage_inv, perm.image_inv, preimage_image] using this.image ⇑f.atom_perm⁻¹,
end⟩⟩

/-- Near-litter permutations can be composed. -/
instance : has_mul near_litter_perm :=
⟨λ f g, ⟨f.atom_perm * g.atom_perm, f.litter_perm * g.litter_perm, λ i s h, h.map.map⟩⟩

/-- Dividing two permutations `f / g` can be interpreted as `f⁻¹ * g`. -/
instance : has_div near_litter_perm :=
⟨λ f g, ⟨f.atom_perm / g.atom_perm, f.litter_perm / g.litter_perm,
  by { simp_rw [div_eq_mul_inv], exact (f * g⁻¹).near }⟩⟩

/-- We can raise near-litter permutations to a natural power since we can do this to
permutations of the base type and the type of litters. -/
instance has_pow : has_pow near_litter_perm ℕ :=
⟨λ f n, ⟨f.atom_perm ^ n, f.litter_perm ^ n, begin
  induction n with d hd,
  { exact (1 : near_litter_perm).near },
  { exact (f * ⟨f.atom_perm ^ d, f.litter_perm ^ d, hd⟩).near }
end⟩⟩

/-- We can raise near-litter permutations to an integer power since we can do this to
permutations of the base type and the type of litters. -/
instance has_zpow : has_pow near_litter_perm ℤ :=
⟨λ f n, ⟨f.atom_perm ^ n, f.litter_perm ^ n, begin
  cases n,
  { exact (f ^ n).near },
  { exact (f ^ (n + 1))⁻¹.near }
end⟩⟩

instance : inhabited near_litter_perm := ⟨1⟩

/-!
The following lemmas describe how the group of near-litter permutations interacts with the group of
base type permutations and the group of litter permutations. In particular, many group operations,
such as taking the inverse, can be moved out of the near-litter context and into the (simpler) base
permutation or litter permutation context.

The `@[simp]` attribute teaches these results to the `simp` tactic. This means that `simp` will (for
example) prefer group operations to be applied after extracting the base permutation, not before.
-/

@[simp] lemma atom_perm_one : (1 : near_litter_perm).atom_perm = 1 := rfl
@[simp] lemma atom_perm_inv (f : near_litter_perm) : f⁻¹.atom_perm = f.atom_perm⁻¹ := rfl
@[simp] lemma atom_perm_mul (f g : near_litter_perm) :
  (f * g).atom_perm = f.atom_perm * g.atom_perm := rfl
@[simp] lemma atom_perm_div (f g : near_litter_perm) :
  (f / g).atom_perm = f.atom_perm / g.atom_perm := rfl
@[simp] lemma atom_perm_pow (f : near_litter_perm) (n : ℕ) : (f ^ n).atom_perm = f.atom_perm ^ n :=
rfl
@[simp] lemma atom_perm_zpow (f : near_litter_perm) (n : ℤ) : (f ^ n).atom_perm = f.atom_perm ^ n :=
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

/-- Near-litter permutations form a group. -/
instance : group near_litter_perm :=
atom_perm_injective.group _ atom_perm_one atom_perm_mul atom_perm_inv atom_perm_div atom_perm_pow
  atom_perm_zpow

/-- Near-litter permutations act on the base type via the base permutation. -/
instance : mul_action near_litter_perm atom :=
{ smul := λ f, f.atom_perm, one_smul := λ _, rfl, mul_smul := λ _ _ _, rfl }

/-- Near-litter permutations act on litters via the litter permutation. -/
instance : mul_action near_litter_perm litter :=
{ smul := λ f, f.litter_perm, one_smul := λ _, rfl, mul_smul := λ _ _ _, rfl }

/-- Near-litter permutations act on near-litters. -/
instance : mul_action near_litter_perm near_litter :=
{ smul := λ f N, ⟨f.litter_perm N.1, ⇑(f.atom_perm)⁻¹ ⁻¹' N.2, f.near N.2.2⟩,
  one_smul := λ _, sigma.ext rfl $ by simp,
  mul_smul := λ _ _ _, rfl }

open_locale pointwise

@[simp] lemma smul_fst (π : near_litter_perm) (N : near_litter) : (π • N).fst = π • N.fst := rfl
@[simp] lemma smul_snd (π : near_litter_perm) (N : near_litter) : (π • N).snd.val = π • N.snd.val :=
by { dsimp only [(•)], simp }

@[simp] lemma smul_local_cardinal (π : near_litter_perm) (i : litter) :
  π • local_cardinal i = local_cardinal (π • i) :=
begin
  ext M,
  unfold local_cardinal,
  unfold has_smul.smul,
  dsimp, split,
  { rintro ⟨N, hN₁, hN₂⟩, rw [← hN₂, ← hN₁] },
  { intro h, refine ⟨π⁻¹ • M, _, _⟩,
    { rw [smul_fst, h], unfold has_smul.smul, simp },
    { ext; simp_rw smul_fst; dsimp only [(•)]; simp } }
end

end near_litter_perm
end con_nf
