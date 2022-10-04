import mathlib.logic
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

noncomputable theory

open function set with_bot
open_locale cardinal

universe u

namespace con_nf
variables [params.{u}]

open code

section A_map
variables {α : Λ} {γ : Iio_index α} [core_tangle_data γ] [positioned_tangle_data γ]
  (β : Iio α) [core_tangle_data (Iio_coe β)]
  [positioned_tangle_data (Iio_coe β)] [almost_tangle_data β]

/-- The *alternative extension* map. For a set of tangles `G`, consider the code
`(α, γ, G)`. We then construct the non-empty set `D` such that `(α, β, D)` is an alternative
extension of the same object in TTT. -/
def A_map (s : set (tangle γ)) : set (tangle $ Iio_coe β) := typed_near_litter '' ⋃ t ∈ s, local_cardinal (f_map β t)

variables {β}

@[simp] lemma mem_A_map {t : tangle $ Iio_coe β} {s : set (tangle γ)} :
  t ∈ A_map β s ↔ ∃ (t' ∈ s) N (hN : is_near_litter (f_map β t') N), typed_near_litter ⟨_, N, hN⟩ = t :=
begin
  simp only [A_map, and_comm, mem_image, mem_Union, exists_prop],
  split,
  { rintro ⟨⟨i, N, hN⟩, rfl, t, ht₁, ⟨rfl, ht₂⟩⟩,
    exact ⟨t, ht₁, N, _, rfl⟩ },
  { rintro ⟨t, ht, N, hN, rfl⟩, cases hN,
    exact ⟨⟨f_map β t, N, _⟩, rfl, t, ht, rfl⟩ }
end


@[simp] lemma A_map_empty : A_map β (∅ : set (tangle γ)) = ∅ :=
by simp only [A_map, Union_false, Union_empty, image_empty]

@[simp] lemma A_map_singleton (t) :
  A_map β ({t} : set (tangle γ)) = typed_near_litter '' local_cardinal (f_map β t) :=
by simp only [A_map, mem_singleton_iff, Union_Union_eq_left]

variables {β γ} {s : set (tangle γ)} {t : tangle γ}

lemma _root_.set.nonempty.A_map (h : s.nonempty) : (A_map β s).nonempty :=
begin
  refine (nonempty_bUnion.2 _).image _,
  exact h.imp (λ t ht, ⟨ht, ⟨f_map β _, litter_set _, is_near_litter_litter_set _⟩, rfl⟩),
end

@[simp] lemma A_map_eq_empty : A_map β s = ∅ ↔ s = ∅ :=
begin
  refine ⟨λ h, not_nonempty_iff_eq_empty.1 $ λ hs, hs.A_map.ne_empty h, _⟩,
  rintro rfl,
  exact A_map_empty,
end

@[simp] lemma A_map_nonempty : (A_map β s).nonempty ↔ s.nonempty :=
by simp_rw [←ne_empty_iff_nonempty, ne.def, A_map_eq_empty]

lemma subset_A_map (ht : t ∈ s) : typed_near_litter '' local_cardinal (f_map β t) ⊆ A_map β s :=
image_subset _ $ subset_Union₂ t ht

lemma μ_le_mk_A_map : s.nonempty → #μ ≤ #(A_map β s) :=
begin
  rintro ⟨t, ht⟩,
  refine (cardinal.mk_le_mk_of_subset $ subset_A_map ht).trans_eq' _,
  rw [cardinal.mk_image_eq, mk_local_cardinal],
  exact typed_near_litter.inj',
end

lemma A_map_injective :
  injective (A_map β : set (tangle γ) → set (tangle $ Iio_coe β)) :=
typed_near_litter.injective.image_injective.comp $ pairwise.bUnion_injective
  (λ x y h, local_cardinal_disjoint _ _ $ (f_map_injective _).ne h) $
  λ _, local_cardinal_nonempty _

variables {δ : Iio_index α} [core_tangle_data δ] [positioned_tangle_data δ]

lemma A_map_disjoint_range (c : set (tangle γ)) (d : set (tangle δ)) (hc : c.nonempty)
  (h : A_map β c = A_map β d) : γ = δ :=
begin
  obtain ⟨b, hb⟩ := hc,
  have := (subset_Union₂ b hb).trans (typed_near_litter.injective.image_injective h).subset,
  obtain ⟨i, -, hi⟩ := mem_Union₂.1 (this (f_map _ b).to_near_litter_mem_local_cardinal),
  exact subtype.coe_injective (f_map_range_eq _ hi),
end

/-!
We don't need to prove that the ranges of the `A_δ` are disjoint for different `β`, since this holds
at the type level.

We now show that there are only finitely many iterated images under any inverse A-map, in the case
of nonempty sets.
-/

variable {γ}

lemma well_founded_position : well_founded (λ a b : tangle γ, position a < position b) :=
inv_image.wf _ is_well_founded.wf

/-- The minimum tangle of a nonempty set of tangles. -/
noncomputable def min_tangle (c : tangles γ) : tangle γ :=
well_founded_position.min c.1 c.2

lemma min_tangle_mem (c : tangles γ) : min_tangle c ∈ c.val :=
well_founded.min_mem _ c.val c.property

lemma min_tangle_le (c : tangles γ) {x} (hx : x ∈ c.1) :
  position (min_tangle c) ≤ position x :=
not_lt.1 $ well_founded_position.not_lt_min c.val c.property hx

lemma A_map_order (c : tangles γ) :
  position (min_tangle c) < position (min_tangle ⟨A_map β c.1, c.2.A_map⟩) :=
begin
  obtain ⟨t, ht, s, hs, h⟩ := (mem_A_map).1 (min_tangle_mem ⟨A_map β c.1, c.2.A_map⟩),
  rw ←h,
  exact (min_tangle_le c ht).trans_lt (f_map_position_raising β t s hs),
end

end A_map

section A_map_code
variables {α : Λ} [core_tangle_cumul α] [positioned_tangle_cumul α]

/-- Tool that lets us use well-founded recursion on codes via `μ`. -/
noncomputable def code_min_map (c : nonempty_code α) : μ := position $ min_tangle ⟨_, c.prop⟩

/-- The pullback `<` relation on codes is well-founded. -/
lemma code_wf : well_founded (inv_image μr (code_min_map : nonempty_code α → μ)) :=
inv_image.wf (code_min_map) μwf.wf

variables [almost_tangle_cumul α] (γ : Iio_index α) (β : Iio α) (c d : code α)

/-- The A-map, phrased as a function on `α`-codes. -/
noncomputable! def A_map_code (c : code α) : code α := mk β (A_map β c.2)

@[simp] lemma fst_A_map_code : (A_map_code β c).1 = β := rfl
@[simp] lemma snd_A_map_code : (A_map_code β c).2 = A_map β c.2 := rfl

@[simp] lemma A_map_code_mk (s) : A_map_code β (mk γ s) = mk β (A_map β s) := rfl

variables {β c d}

@[simp] lemma A_map_code_is_empty : (A_map_code β c).is_empty ↔ c.is_empty :=
by { cases c, exact A_map_eq_empty }

alias A_map_code_is_empty ↔ _ code.is_empty.A_map_code

attribute [protected] code.is_empty.A_map_code

lemma A_map_code_inj_on : {c : code α | c.2.nonempty}.inj_on (A_map_code β) :=
begin
  rintro ⟨⟨γ, hγ⟩, s⟩ hs ⟨⟨δ, hδ⟩, t⟩ ht h,
  have := (congr_arg_heq sigma.snd h).eq,
  dsimp at this,
  have γ_eq_δ := congr_arg subtype.val (A_map_disjoint_range _ _ hs this),
  dsimp only at γ_eq_δ,
  subst γ_eq_δ,
  rw A_map_injective this,
end

variables (β)

lemma A_map_code_order (c : nonempty_code α) :
  code_min_map c < code_min_map ⟨A_map_code β c.1, c.2.A_map⟩ :=
A_map_order _

/-- This relation on `α`-codes allows us to state that there are only finitely many iterated images
under the inverse A-map. -/
@[mk_iff] inductive A_map_rel (c : code α) : code α → Prop
| intro (β : Iio α) : c.1 ≠ β → A_map_rel (A_map_code β c)

infix ` ↝ `:62 := A_map_rel

lemma A_map_rel_subsingleton (hc : c.2.nonempty) : {d : code α | d ↝ c}.subsingleton :=
begin
  intros d hd e he,
  simp only [A_map_rel_iff] at hd he,
  obtain ⟨⟨β, hβ⟩, -, rfl⟩ := hd,
  obtain ⟨⟨γ, hγ⟩, -, h⟩ := he,
  have := congr_arg subtype.val (sigma.ext_iff.1 h).1,
  dsimp at this,
  rw coe_eq_coe at this,
  subst this,
  refine A_map_code_inj_on (A_map_nonempty.1 hc) _ h,
  rw h at hc,
  exact A_map_nonempty.1 hc,
end

lemma A_map_rel_A_map_code (hd : d.2.nonempty) (hdβ : d.1 ≠ β) :
  c ↝ A_map_code β d ↔ c = d :=
begin
  refine ⟨λ h, A_map_rel_subsingleton (by exact hd.A_map) h $ A_map_rel.intro _ hdβ, _⟩,
  rintro rfl,
  exact ⟨_, hdβ⟩,
end

lemma A_map_rel.nonempty_iff : c ↝ d → (c.2.nonempty ↔ d.2.nonempty) :=
by { rintro ⟨β, hcδ⟩, exact A_map_nonempty.symm }

lemma A_map_rel_empty_empty (hγβ : γ ≠ β) : mk γ ∅ ↝ mk β ∅ :=
(A_map_rel_iff _ _).2 ⟨β, hγβ, by simp⟩

lemma eq_of_A_map_code {β γ : Iio α} (hc : c.2.nonempty) (hcβ : c.1 ≠ β)
  (hdγ : d.1 ≠ γ) (h : A_map_code β c = A_map_code γ d) : c = d :=
begin
  refine A_map_rel_subsingleton (by exact hc.A_map) (A_map_rel.intro _ hcβ) _,
  simp_rw h,
  exact A_map_rel.intro _ hdγ,
end

/-- This relation on `α`-codes allows us to state that there are only finitely many iterated images
under the inverse A-map. -/
@[mk_iff] inductive A_map_rel' (c : nonempty_code α) : nonempty_code α → Prop
| intro (β : Iio α) : (c : code α).1 ≠ β →
  A_map_rel' ⟨A_map_code β c, c.2.A_map⟩

@[simp] lemma A_map_rel_coe_coe {c d : nonempty_code α} : (c : code α) ↝ d ↔ A_map_rel' c d :=
begin
  rw [A_map_rel_iff, A_map_rel'_iff, iff.comm],
  exact exists_congr (λ β, and_congr_right' subtype.ext_iff),
end

lemma A_map_subrelation : subrelation A_map_rel' (inv_image μr (code_min_map : nonempty_code α → μ))
| c _ (A_map_rel'.intro β hc) := A_map_code_order _ _

/-- There are only finitely many iterated images under any inverse A-map. -/
lemma A_map_rel'_well_founded : well_founded (A_map_rel' : _ → nonempty_code α → Prop) :=
A_map_subrelation.wf code_wf

instance : has_well_founded (nonempty_code α) := ⟨_, A_map_rel'_well_founded⟩

/-- There is at most one inverse under an A-map. This corresponds to the fact that there is only one
code which is related (on the left) to any given code under the A-map relation. -/
lemma A_map_rel'_subsingleton (c : nonempty_code α) :
  {d : nonempty_code α | A_map_rel' d c}.subsingleton :=
begin
  intros d hd e he,
  simp only [subtype.val_eq_coe, ne.def, A_map_rel'_iff, mem_set_of_eq] at hd he,
  obtain ⟨⟨β, hβ⟩, -, rfl⟩ := hd,
  obtain ⟨⟨γ, hγ⟩, -, h⟩ := he,
  rw subtype.ext_iff at h,
  have := congr_arg subtype.val (sigma.ext_iff.1 h).1,
  dsimp at this,
  rw coe_eq_coe at this,
  subst this,
  exact subtype.coe_injective (A_map_code_inj_on d.2 e.2 h),
end

end A_map_code
end con_nf
