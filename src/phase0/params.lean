import mathlib.cardinal
import mathlib.order
import mathlib.with_bot
import set_theory.cardinal.cofinality

/-!
# Parameters of the construction

This file is based on sections 3.1 and 3.2 of the paper.
-/

/-!
We do not assume that our definitions, instances, lemmas and theorems are 'computable';
that is, can be provably evaluated in finite time by a computer.
For our purposes, restricting to only computable functions is unnecessary.
-/
noncomputable theory

open cardinal set
open_locale cardinal classical

universe u

namespace con_nf

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
class params :=
(Λ : Type u) (Λr : Λ → Λ → Prop) [Λwf : is_well_order Λ Λr]
(Λ_ord : ordinal.type Λr = (#Λ).ord)
(Λ_limit : (#Λ).is_limit)
(κ : Type u) (κ_regular : (#κ).is_regular) (κr : κ → κ → Prop) [κwf : is_well_order κ κr]
(κ_ord : ordinal.type κr = (#κ).ord)
(Λ_lt_κ : #Λ < #κ)
(μ : Type u) (μr : μ → μ → Prop) [μwf : is_well_order μ μr]
(μ_ord : ordinal.type μr = (#μ).ord)
(μ_strong_limit : (#μ).is_strong_limit)
(κ_lt_μ : #κ < #μ)
(κ_le_μ_cof : #κ ≤ (#μ).ord.cof)

export params (Λ Λr Λwf Λ_ord Λ_limit κ κ_regular κr κwf κ_ord Λ_lt_κ μ μr μwf μ_ord μr
  μ_strong_limit κ_lt_μ κ_le_μ_cof)

/-!
### Explicit parameters

There exists valid parameters for the model. The smallest parameters are
* `Λ := ℵ_0`
* `κ := ℵ_1`
* `μ = ℶ_{ω_1}`.
-/

example : params.{0} :=
{ Λ := ℕ,
  Λr := (<),
  Λwf := infer_instance,
  Λ_ord := by simp only [mk_denumerable, ord_aleph_0, ordinal.type_nat_lt],
  Λ_limit := by { rw mk_denumerable, exact is_limit_aleph_0 },
  κ := (aleph 1).ord.out.α,
  κr := (aleph 1).ord.out.r,
  κwf := (aleph 1).ord.out.wo,
  κ_ord := by simp,
  κ_regular := by { rw [mk_ordinal_out, card_ord], exact is_regular_aleph_one },
  Λ_lt_κ := by { rw [mk_denumerable, mk_ordinal_out, card_ord], exact aleph_0_lt_aleph_one },
  μ := (beth $ ord $ aleph 1).ord.out.α,
  μr := (beth $ ord $ aleph 1).ord.out.r,
  μwf := (beth $ ord $ aleph 1).ord.out.wo,
  μ_ord := by simp,
  μ_strong_limit := by simp [is_strong_limit_beth (ord_is_limit $ aleph_0_le_aleph 1).2],
  κ_lt_μ := by { simp only [mk_out, mk_ordinal_out, card_ord],
    exact (aleph_le_beth _).trans_lt (beth_strict_mono (ord_aleph_is_limit _).one_lt) },
  κ_le_μ_cof := begin
    simp only [mk_out, mk_ordinal_out, card_ord],
    rw beth_normal.cof_eq (ord_is_limit $ aleph_0_le_aleph 1),
    exact is_regular_aleph_one.2,
  end }

variables [params.{u}] {ι α β : Type u}

/-- To allow Lean's type checker to see that the ordering `Λr` is a well-ordering without having to
explicitly write `Λwf` everywhere, we declare it as an instance. -/
instance : is_well_order Λ Λr := Λwf
instance : is_well_order κ κr := κwf
instance : is_well_order μ μr := μwf
/-- We can deduce from the well-ordering `Λwf` that `Λ` is linearly ordered. -/
instance : linear_order Λ := linear_order_of_STO Λr
instance : linear_order κ := linear_order_of_STO κr
instance : linear_order μ := linear_order_of_STO μr
/-- We deduce that `Λ` has a well-founded relation. -/
instance : has_well_founded Λ := is_well_order.to_has_well_founded
instance : has_well_founded κ := is_well_order.to_has_well_founded
instance : has_well_founded μ := is_well_order.to_has_well_founded

lemma κ_le_μ : #κ ≤ #μ := κ_lt_μ.le

noncomputable instance : inhabited Λ :=
@classical.inhabited_of_nonempty _ $ mk_ne_zero_iff.1 Λ_limit.ne_zero

noncomputable instance : inhabited κ :=
@classical.inhabited_of_nonempty _ $ mk_ne_zero_iff.1 κ_regular.pos.ne'

noncomputable instance : inhabited μ :=
@classical.inhabited_of_nonempty _ $ mk_ne_zero_iff.1 μ_strong_limit.ne_zero

/-- Either the base type or a proper type index (an element of `Λ`).
The base type is written `⊥`. -/
@[reducible]
def type_index := with_bot Λ

@[simp] lemma mk_type_index : #type_index = #Λ :=
mk_option.trans $ add_eq_left Λ_limit.aleph_0_le $ one_le_aleph_0.trans Λ_limit.aleph_0_le

/- Since `Λ` is well-ordered, so is `Λ` together with the base type `⊥`.
This allows well founded recursion on type indices. -/

noncomputable instance : linear_order type_index := linear_order_of_STO (<)
noncomputable instance : has_well_founded type_index := is_well_order.to_has_well_founded

/-- The litters. This is the type indexing the partition of `atom`. -/
structure litter :=
(ν : μ)
(β : type_index)
(γ : Λ)
(β_ne_γ : β ≠ γ)

instance : inhabited litter :=
⟨⟨arbitrary μ, ⊥, arbitrary Λ, with_bot.bot_ne_coe⟩⟩

/-- Litters are equivalent to a subtype of a product type. -/
def litter_equiv : litter ≃ {a : μ ×ₗ type_index ×ₗ Λ // a.2.1 ≠ a.2.2} :=
{ to_fun := λ L, ⟨⟨L.ν, L.β, L.γ⟩, L.β_ne_γ⟩,
  inv_fun := λ L, ⟨L.val.1, L.val.2.1, L.val.2.2, L.prop⟩,
  left_inv := by rintro ⟨ν, β, γ, h⟩; refl,
  right_inv := by rintro ⟨⟨ν, β, γ⟩, h⟩; refl }

instance subtype.is_well_order {α : Type*} (p : α → Prop) [has_lt α] [is_well_order α (<)] :
  is_well_order (subtype p) (<) :=
rel_embedding.is_well_order (subtype.rel_embedding (<) p)

instance lex.is_well_order {α β : Type*} [has_lt α] [has_lt β]
  [is_well_order α (<)] [is_well_order β (<)] : is_well_order (α ×ₗ β) (<) := prod.lex.is_well_order

@[simp] lemma mk_litter : #litter = #μ :=
begin
  refine litter_equiv.cardinal_eq.trans (le_antisymm ((cardinal.mk_subtype_le _).trans_eq _)
    ⟨⟨λ ν, ⟨⟨ν, ⊥, arbitrary Λ⟩, with_bot.bot_ne_coe⟩, λ ν₁ ν₂, congr_arg $ prod.fst ∘ subtype.val⟩⟩),
  have := mul_eq_left (κ_regular.aleph_0_le.trans κ_le_μ) (Λ_lt_κ.le.trans κ_lt_μ.le)
    Λ_limit.ne_zero,
  simp only [lex, mk_prod, lift_id, mk_type_index, mul_eq_self Λ_limit.aleph_0_le, this],
end

/-- Principal segments (sets of the form `{y | y < x}`) have cardinality `< μ`. -/
lemma card_Iio_lt (x : μ) : #(Iio x) < #μ := card_typein_lt (<) x μ_ord.symm

/-- Initial segments (sets of the form `{y | y ≤ x}`) have cardinality `< μ`. -/
lemma card_Iic_lt (x : μ) : #(Iic x) < #μ :=
begin
  rw [←Iio_union_right, mk_union_of_disjoint, mk_singleton],
  { exact (add_one_le_succ _).trans_lt (μ_strong_limit.is_limit.2 _ $ card_Iio_lt x) },
  { simp }
end

instance : has_lt litter := ⟨litter_equiv ⁻¹'o (<)⟩

/-- Litters are well-ordered. -/
instance litter.is_well_order : is_well_order litter (<) :=
rel_iso.is_well_order.preimage _ litter_equiv

instance : linear_order litter := linear_order_of_STO (<)
instance : has_well_founded litter := is_well_order.to_has_well_founded

/-- The base type of the construction, `τ₋₁` in the document. Instead of declaring it as an
arbitrary type of cardinality `μ` and partitioning it into suitable sets of litters afterwards, we
define it as `litter × κ`, which has the correct cardinality and comes with a natural
partition.

These are not 'atoms' in the ZFU, TTTU or NFU sense; they are simply the elements of the model which
are in type `τ₋₁`. -/
@[derive inhabited] def atom : Type* := litter × κ

instance : has_lt atom := ⟨prod.lex (<) (<)⟩

/-- Atoms are well-ordered. -/
instance atom.is_well_order : is_well_order atom (<) := prod.lex.is_well_order

instance : linear_order atom := linear_order_of_STO (<)
instance : has_well_founded atom := is_well_order.to_has_well_founded

/-- The cardinality of `τ₋₁` is the cardinality of `μ`.
We will prove that all types constructed in our model have cardinality equal to `μ`. -/
@[simp] lemma mk_atom : #atom = #μ :=
by simp_rw [atom, mk_prod, lift_id, mk_litter,
  mul_eq_left (κ_regular.aleph_0_le.trans κ_le_μ) κ_le_μ κ_regular.pos.ne']

section small
variables {f : α → β} {s t : set α}

/-- A set is small if its cardinality is strictly less than `κ`. -/
def small (s : set α) := #s < #κ

lemma small.lt : small s → #s < #κ := id

lemma _root_.set.subsingleton.small {α : Type*} {s : set α} (hs : s.subsingleton) : small s :=
hs.cardinal_mk_le_one.trans_lt $ one_lt_aleph_0.trans_le κ_regular.aleph_0_le

@[simp] lemma small_empty : small (∅ : set α) := subsingleton_empty.small
@[simp] lemma small_singleton (x : α) : small ({x} : set α) := subsingleton_singleton.small

lemma small_set_of (p : α → Prop) : small (λ a, p a) ↔ small {a | p a} := iff.rfl

lemma small_of_forall_not_mem {s : set α} (h : ∀ x, x ∉ s) : small s :=
by simp only [eq_empty_of_forall_not_mem h, small_empty]

/-- Subsets of small sets are small. We say that the 'smallness' relation is monotone. -/
lemma small.mono (h : s ⊆ t) : small t → small s := (mk_le_mk_of_subset h).trans_lt

/-- Unions of small subsets are small. -/
lemma small.union (hs : small s) (ht : small t) : small (s ∪ t) :=
(mk_union_le _ _).trans_lt $ add_lt_of_lt κ_regular.aleph_0_le hs ht

lemma small.symm_diff (hs : small s) (ht : small t) : small (s ∆ t) :=
(hs.union ht).mono symm_diff_subset_union

lemma small.symm_diff_iff (hs : small s) : small t ↔ small (s ∆ t) :=
⟨hs.symm_diff, λ ht, by simpa only [symm_diff_symm_diff_self'] using ht.symm_diff hs⟩

lemma small_Union (hι : #ι < #κ) {f : ι → set α} (hf : ∀ i, small (f i)) : small (⋃ i, f i) :=
(mk_Union_le _).trans_lt $ mul_lt_of_lt κ_regular.aleph_0_le hι $
  supr_lt_of_is_regular κ_regular hι hf

lemma small_Union_Prop {p : Prop} {f : p → set α} (hf : ∀ i, small (f i)) : small (⋃ i, f i) :=
by by_cases p; simp [h, hf _]

protected lemma small.bUnion {s : set ι} (hs : small s) {f : Π i ∈ s, set α}
  (hf : ∀ i (hi : i ∈ s), small (f i hi)) : small (⋃ i (hi : i ∈ s), f i hi) :=
(mk_bUnion_le' _ _).trans_lt $ mul_lt_of_lt κ_regular.aleph_0_le hs $
  supr_lt_of_is_regular κ_regular hs $ λ i, hf _ _

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
h.image.mono subset_image_symm_diff

lemma is_near_of_small (hs : small s) (ht : small t) : is_near s t :=
small.symm_diff hs ht

lemma small.is_near_iff (hs : small s) : small t ↔ is_near s t :=
hs.symm_diff_iff

lemma is_near.κ_le (h : is_near s t) (hs : #κ ≤ #s) : #κ ≤ #(t : set α) :=
begin
  by_contradiction ht,
  rw not_le at ht,
  have := h.symm,
  rw ← small.is_near_iff ht at this,
  exact (lt_iff_not_ge _ _).mp this hs,
end

lemma is_near.mk_inter (h : is_near s t) (hs : #κ ≤ #s) : #κ ≤ #(s ∩ t : set α) :=
begin
  rw [is_near, symm_diff_eq_sup_sdiff_inf] at h,
  exact le_of_not_gt (λ hst, lt_irrefl _
    (((hs.trans (mk_le_mk_of_subset (subset_union_left _ _))).trans
    (le_mk_diff_add_mk (s ∪ t) (s ∩ t))).trans_lt (add_lt_of_lt κ_regular.aleph_0_le h hst))),
end

end is_near
end con_nf
