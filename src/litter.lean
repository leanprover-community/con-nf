import mathlib.equiv
import mathlib.order
import params

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

open cardinal equiv equiv.perm function set
open_locale cardinal

universe u

namespace con_nf
variables [params.{u}] {α β : Type u}

open params

section small
variables {f : α → β} {s t : set α}

/-- A set is small if its cardinality is strictly less than `κ`. -/
def small (s : set α) := #s < #κ

lemma small_empty : small (∅ : set α) := by { rw [small, mk_emptyc], exact κ_regular.pos }

lemma small.mono (h : s ⊆ t) : small t → small s := (cardinal.mk_le_mk_of_subset h).trans_lt

lemma small.union (hs : small s) (ht : small t) : small (s ∪ t) :=
(mk_union_le _ _).trans_lt $ add_lt_of_lt κ_regular.aleph_0_le hs ht

lemma small.image : small s → small (f '' s) := mk_image_le.trans_lt

end small

section is_near
variables {s t u : set α}

/-- Two sets are near if their symmetric difference is small. -/
def is_near (s t : set α) : Prop := small (s ∆ t)

@[refl] lemma is_near_refl (s : set α) : is_near s s :=
by { rw [is_near, symm_diff_self], exact small_empty }

lemma is_near_rfl : is_near s s := is_near_refl _

@[symm] lemma is_near.symm (h : is_near s t) : is_near t s := by rwa [is_near, symm_diff_comm]
lemma is_near_comm : is_near s t ↔ is_near t s := ⟨is_near.symm, is_near.symm⟩

@[trans] lemma is_near.trans (hst : is_near s t) (htu : is_near t u) : is_near s u :=
(hst.union htu).mono $ symm_diff_triangle s t u

lemma is_near.image (f : α → β) (h : is_near s t) : is_near (f '' s) (f '' t) :=
h.image.mono $ subset_image_symm_diff _ _ _

end is_near

variables {i j : μ}

/-- The `i`-th litter. -/
def litter (i : μ) : set base_type := {p | p.1 = i}

@[simp] lemma mk_litter (i : μ) : #(litter i) = #κ :=
cardinal.eq.2 ⟨⟨λ x, x.1.2, λ k, ⟨(i, k), rfl⟩, λ x, by { ext, exacts [x.2.symm, rfl] }, λ k, rfl⟩⟩

lemma pairwise_disjoint_litter : pairwise (disjoint on litter) :=
λ i j h x hx, h $ hx.1.symm.trans hx.2

/-- A `i`-near-litter is a set of small symmetric to the `i`-th litter. -/
def is_near_litter (i : μ) (s : set base_type) : Prop := is_near (litter i) s

lemma is_near_litter_litter (i : μ) : is_near_litter i (litter i) := is_near_rfl

lemma is_near_litter.near {s t : set base_type} (hs : is_near_litter i s)
  (ht : is_near_litter i t) : is_near s t := hs.symm.trans ht

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

/-- A near-litter permutation is a permutation of the base type which sends near-litters to
near-litters. It turns out that the images of near-litters near the same litter are themselves near
the same litter. Hence a near-litter permutation induces a permutation of litters, and we keep that
as data for simplicity. -/
structure near_litter_perm : Type u :=
(base_perm : perm base_type)
(litter_perm : perm μ)
(near ⦃i : μ⦄ ⦃s : set base_type⦄ :
  is_near_litter i s → is_near_litter (litter_perm i) (⇑base_perm⁻¹ ⁻¹' s))

lemma is_near_litter.map {f : near_litter_perm} {s : set base_type} (h : is_near_litter i s) :
  is_near_litter (f.litter_perm i) (⇑f.base_perm⁻¹ ⁻¹' s) :=
f.near h

namespace near_litter_perm
variables {f g : near_litter_perm}

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

@[ext] lemma near_litter_perm.ext (h : f.base_perm = g.base_perm) : f = g := base_perm_injective h

instance : has_one near_litter_perm := ⟨⟨1, 1, λ i s, id⟩⟩

instance : has_inv near_litter_perm :=
⟨λ f, ⟨f.base_perm⁻¹, f.litter_perm⁻¹, λ i s h, begin
  have : is_near (⇑f.base_perm⁻¹ ⁻¹' litter (f.litter_perm⁻¹ i)) s,
  { exact (f.near $ is_near_litter_litter _).near (by rwa apply_inv_self) },
  simpa only [preimage_inv, perm.image_inv, preimage_image] using this.image ⇑f.base_perm⁻¹,
end⟩⟩

instance : has_mul near_litter_perm :=
⟨λ f g, ⟨f.base_perm * g.base_perm, f.litter_perm * g.litter_perm, λ i s h, h.map.map⟩⟩

instance : has_div near_litter_perm :=
⟨λ f g, ⟨f.base_perm / g.base_perm, f.litter_perm / g.litter_perm,
  by { simp_rw [div_eq_mul_inv], exact (f * g⁻¹).near }⟩⟩

instance has_pow : has_pow near_litter_perm ℕ :=
⟨λ f n, ⟨f.base_perm ^ n, f.litter_perm ^ n, sorry⟩⟩

instance has_zpow : has_pow near_litter_perm ℤ :=
⟨λ f n, ⟨f.base_perm ^ n, f.litter_perm ^ n, sorry⟩⟩

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

instance : group near_litter_perm :=
base_perm_injective.group _ base_perm_one base_perm_mul base_perm_inv base_perm_div base_perm_pow
  base_perm_zpow

instance : mul_action near_litter_perm base_type :=
{ smul := λ f, f.base_perm, one_smul := λ _, rfl, mul_smul := λ _ _ _, rfl }

instance : mul_action near_litter_perm μ :=
{ smul := λ f, f.litter_perm, one_smul := λ _, rfl, mul_smul := λ _ _ _, rfl }

end near_litter_perm

def near_litter : Type* := Σ' i s, is_near_litter i s

def near_litter.is_litter (N : near_litter) : Prop := N.2.1 = litter N.1

end con_nf
