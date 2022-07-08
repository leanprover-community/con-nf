import mathlib.logic
import mathlib.with_bot
import phase1.code
import phase1.f_map

/-!
# Alternative extensions

The alternative extension map, aka A-map, from `γ` to `β` sends a code of extension `γ` to its
lternative extension `β`. This will used to identify codes and construct the TTT objects.

An important property for intuition is that A-maps have disjoint ranges (except on empty codes) and
are each injective, so if we connect each code to its images under A-maps, we get a tree (except for
empty codes that form a complete graph).

## Main declarations

* `con_nf.A_map`: Alternative extension map as a map from sets of `γ`-tangles to of `β`-tangles.
  Note that `γ` can be any type index while `β` has to be a proper type index.
* `con_nf.A_map_code`: Alternative extension map as a map from codes to codes of extension `β`.
* `con_nf.A_map_rel`: The relation on codes generated by `A_map_code`. It relates `c` to `d` iff `d`
  is the image of `c` under some A-map. This relation is well-founded on **nonempty** codes. See
  `con_nf.A_map_rel'_well_founded`.

## Notation

* `c ↝ d`: `d` is the image of `c` under some A-map.
-/

open function set with_bot
open_locale cardinal

universe u

namespace con_nf
variables [params.{u}]

section A_map
variables {α α₁ α₂ : type_index} (β : Λ) [weak_tangle_data α] [weak_tangle_data α₁]
  [weak_tangle_data α₂] [tangle_data β] {s : set (tangle α)} {t : tangle α}

/-- The *alternative extension* map. For a set of tangles `G`, consider the code
`(α, γ, G)`. We then construct the non-empty set `D` such that `(α, β, D)` is an alternative
extension of the same object in TTT. -/
def A_map (s : set (tangle α)) : set (tangle β) := to_tangle '' ⋃ t ∈ s, local_cardinal (f_map β t)

variables {β}

@[simp] lemma mem_A_map {t : tangle β} :
  t ∈ A_map β s ↔ ∃ (t' ∈ s) N (hN : is_near_litter (f_map β t') N), to_tangle ⟨_, N, hN⟩ = t :=
begin
  simp only [A_map, and_comm, mem_image, mem_Union, exists_prop],
  split,
  { rintro ⟨⟨i, N, hN⟩, ⟨t', ht', (rfl : i = _)⟩, rfl⟩,
    exact ⟨t', ht', N, hN, rfl⟩ },
  { rintro ⟨t', ht', N, hN, rfl⟩,
    exact ⟨⟨_, N, hN⟩, ⟨t', ht', rfl⟩, rfl⟩ }
end

variables (β)

@[simp] lemma A_map_empty : A_map β (∅ : set (tangle α)) = ∅ :=
by simp only [A_map, Union_false, Union_empty, image_empty]

@[simp] lemma A_map_singleton (t) :
  A_map β ({t} : set (tangle α)) = to_tangle '' local_cardinal (f_map β t) :=
by simp only [A_map, mem_singleton_iff, Union_Union_eq_left]

variables {β}

lemma _root_.set.nonempty.A_map (h : s.nonempty) : (A_map β s).nonempty :=
begin
  refine (nonempty_bUnion.2 _).image _,
  exact h.imp (λ t ht, ⟨ht, ⟨f_map β _, litter_set _, is_near_litter_litter_set _⟩, rfl⟩),
end

@[simp] lemma A_map_eq_empty : A_map β s = ∅ ↔ s = ∅ :=
begin
  refine ⟨λ h, not_nonempty_iff_eq_empty.1 $ λ hs, hs.A_map.ne_empty h, _⟩,
  rintro rfl,
  exact A_map_empty _,
end

@[simp] lemma A_map_nonempty : (A_map β s).nonempty ↔ s.nonempty :=
by simp_rw [←ne_empty_iff_nonempty, ne.def, A_map_eq_empty]

lemma subset_A_map (ht : t ∈ s) : to_tangle '' local_cardinal (f_map β t) ⊆ A_map β s :=
image_subset _ $ subset_Union₂ t ht

lemma μ_le_mk_A_map : s.nonempty → #μ ≤ #(A_map β s) :=
begin
  rintro ⟨t, ht⟩,
  refine (cardinal.mk_le_mk_of_subset $ subset_A_map ht).trans_eq' _,
  rw [cardinal.mk_image_eq, mk_local_cardinal],
  exact to_tangle.inj',
end

lemma A_map_injective : injective (A_map β : set (tangle α) → set (tangle β)) :=
to_tangle.injective.image_injective.comp $ pairwise.bUnion_injective
  (λ x y h, local_cardinal_disjoint _ _ $ (f_map_injective _).ne h) $
  λ _, local_cardinal_nonempty _

lemma A_map_disjoint_range (c : set (tangle α₁)) (d : set (tangle α₂)) (hc : c.nonempty)
  (h : A_map β c = A_map β d) : α₁ = α₂ :=
begin
  obtain ⟨b, hb⟩ := hc,
  have := (subset_Union₂ b hb).trans (to_tangle.injective.image_injective h).subset,
  obtain ⟨i, -, hi⟩ := mem_Union₂.1 (this (f_map _ b).to_near_litter_mem_local_cardinal),
  exact f_map_range_eq _ hi,
end

/-!
We don't need to prove that the ranges of the `A_δ` are disjoint for different `β`, since this holds
at the type level.

We now show that there are only finitely many iterated images under any inverse A-map.
-/

lemma well_founded_position : well_founded (λ a b : tangle α, position a < position b) :=
inv_image.wf _ is_well_order.wf

/-- The minimum tangle of a nonempty set of tangles. -/
noncomputable def min_tangle (c : tangles α) : tangle α := well_founded_position.min c.1 c.2

lemma min_tangle_mem (c : tangles α) : min_tangle c ∈ c.val :=
well_founded.min_mem _ c.val c.property

lemma min_tangle_le (c : tangles α) {x} (hx : x ∈ c.1) : position (min_tangle c) ≤ position x :=
not_lt.1 $ well_founded_position.not_lt_min c.val c.property hx

lemma A_map_order (c : tangles α) :
  position (min_tangle c) < position (min_tangle ⟨A_map β c.1, c.2.A_map⟩) :=
begin
  obtain ⟨t, ht, s, hs, h⟩ := mem_A_map.1 (min_tangle_mem ⟨A_map β c.1, c.2.A_map⟩),
  rw ←h,
  exact (min_tangle_le c ht).trans_lt (f_map_position_raising β t s hs),
end

end A_map

section A_map_code
variables {α α₁ α₂ β : Λ} {hβ : β < α} [weak_tangle_data α] [weak_tangle_data α₁] [tangle_cumul α]
  [tangle_cumul α₁] [weak_tangle_data α₂] {c d : code α}

/-- Tool that lets us use well-founded recursion on codes via `μ`. -/
noncomputable def code_min_map (c : nonempty_code α) : μ := position $ min_tangle ⟨_, c.prop⟩

/-- The pullback `<` relation on codes is well-founded. -/
lemma code_wf : well_founded (inv_image μr (code_min_map : nonempty_code α → μ)) :=
inv_image.wf (code_min_map) μwf.wf

/-- The A-map, phrased as a function on `α`-codes. -/
def A_map_code (hβ : β < α) (c : code α) : code α :=
⟨⟨β, coe_lt_coe.2 hβ⟩, A_map (⟨β, hβ⟩ : Iio α) c.elts⟩

@[simp] lemma extension_A_map_code (c) : (A_map_code hβ c).extension = ⟨β, coe_lt_coe.2 hβ⟩ := rfl
@[simp] lemma elts_A_map_code (c) : (A_map_code hβ c).elts = A_map β c.elts := rfl

@[simp] lemma A_map_code_mk (s) :
  A_map_code hβ ⟨⟨β, coe_lt_coe.2 $ hβ⟩, s⟩ = ⟨⟨β, coe_lt_coe.2 hβ⟩, A_map β s⟩ := rfl

@[simp] lemma A_map_code_is_empty (c) : (A_map_code hβ c).is_empty ↔ c.is_empty :=
by { cases c, exact A_map_eq_empty }

alias A_map_code_is_empty ↔ _ code.is_empty.A_map_code

attribute [protected] code.is_empty.A_map_code

lemma A_map_code_inj_on :
  {c : code α | c.elts.nonempty}.inj_on (A_map_code hβ : code α → code α) :=
begin
  rintro ⟨⟨γ, hγ⟩, s⟩ hs ⟨⟨δ, hδ⟩, t⟩ ht h,
  have := (congr_arg_heq code.elts h).eq,
  dsimp at this,
  have := A_map_disjoint_range _ _ hs this,
  subst this,
  rw A_map_injective this,
  refl,
end

lemma A_map_code_order (c : nonempty_code α) :
  code_min_map c < code_min_map ⟨A_map_code hβ c.1, c.2.A_map⟩ :=
A_map_order _

/-- This relation on `α`-codes allows us to state that there are only finitely many iterated images
under the inverse A-map. -/
@[mk_iff] inductive A_map_rel (c : code α) : code α → Prop
| intro (β : Λ) (hβ : β < α) : c.extension.1 ≠ β → A_map_rel (A_map_code hβ c)

infix ` ↝ `:62 := A_map_rel

lemma A_map_rel_subsingleton (hc : c.elts.nonempty) : {d : code α | d ↝ c}.subsingleton :=
begin
  intros d hd e he,
  simp only [A_map_rel_iff, mem_set_of_eq] at hd he,
  obtain ⟨β, hβ, -, rfl⟩ := hd,
  obtain ⟨γ, hγ, -, h⟩ := he,
  have := congr_arg subtype.val ((code.ext_iff _ _).1 h).1,
  dsimp at this,
  rw coe_eq_coe at this,
  subst this,
  refine A_map_code_inj_on (A_map_nonempty.1 hc) _ h,
  rw h at hc,
  exact A_map_nonempty.1 hc,
end

lemma A_map_rel_A_map_code {hδ : β < α} (hd : d.elts.nonempty) (hdδ : d.extension.1 ≠ β) :
  c ↝ A_map_code hβ d ↔ c = d :=
begin
  refine ⟨λ h, A_map_rel_subsingleton (by exact hd.A_map) h $ A_map_rel.intro _ _ hdδ, _⟩,
  rintro rfl,
  exact ⟨_, _, hdδ⟩,
end

lemma A_map_rel.nonempty_iff :  c ↝ d → (c.elts.nonempty ↔ d.elts.nonempty) :=
by { rintro ⟨β, hδ, hcδ⟩, exact A_map_nonempty.symm }

@[simp] lemma A_map_rel_coe_coe {c d : nonempty_code α} : (c : code α) ↝ d ↔ A_map_rel' c d :=
begin
  rw [A_map_rel_iff, A_map_rel'_iff, iff.comm],
  exact exists₂_congr (λ β hδ, and_congr_right' subtype.ext_iff),
end

lemma A_map_rel_empty_empty {hγ : γ < α} {hδ : β < α} (hγδ : γ ≠ β) :
  (⟨γ, hγ, ∅⟩ : code α) ↝ ⟨β, coe_lt_coe.2 hδ, ∅⟩ :=
(A_map_rel_iff _ _).2 ⟨_, hδ, hγδ, by simp⟩

lemma eq_of_A_map_code {hδ : β < α} {hε : ε < α} (hc : c.elts.nonempty) (hcδ : c.extension ≠ β)
  (hdε : d.extension ≠ ε) (h : A_map_code hβ c = A_map_code hε d) : c = d :=
begin
  refine A_map_rel_subsingleton (by exact hc.A_map) (A_map_rel.intro _ hδ hcδ) _,
  simp_rw h,
  exact A_map_rel.intro _ _ hdε,
end

/-- This relation on `α`-codes allows us to state that there are only finitely many iterated images
under the inverse A-map. -/
@[mk_iff] inductive A_map_rel' (c : nonempty_code α) : nonempty_code α → Prop
| intro (β : Λ) (hβ : β < α) : (c : code α).extension.1 ≠ β →
  A_map_rel' ⟨A_map_code hβ c, c.2.A_map⟩

lemma A_map_subrelation : subrelation A_map_rel' (inv_image μr (code_min_map : nonempty_code α → μ))
| c _ (A_map_rel'.intro β hβ hc) := A_map_code_order _

/-- There are only finitely many iterated images under any inverse A-map. -/
lemma A_map_rel'_well_founded :
  well_founded (A_map_rel' : nonempty_code α → nonempty_code α → Prop) :=
A_map_subrelation.wf code_wf

instance : has_well_founded (nonempty_code α) := ⟨_, A_map_rel'_well_founded⟩

/-- There is at most one inverse under an A-map. This corresponds to the fact that there is only one
code which is related (on the left) to any given code under the A-map relation. -/
lemma A_map_rel'_subsingleton (c : nonempty_code α) :
  {d : nonempty_code α | A_map_rel' d c}.subsingleton :=
begin
  intros x hx y hy,
  simp only [subtype.val_eq_coe, ne.def, A_map_rel'_iff, mem_set_of_eq] at hx hy,
  obtain ⟨β, hβ, -, rfl⟩ := hx,
  obtain ⟨γ, hγ, -, h⟩ := hy,
  rw subtype.ext_iff at h,
  have := congr_arg subtype.val ((code.ext_iff _ _).1 h).1,
  dsimp at this,
  rw coe_eq_coe at this,
  subst this,
  exact subtype.coe_injective (A_map_code_inj_on x.2 y.2 h),
end

end con_nf
