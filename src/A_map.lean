import f_map
import mathlib.logic
import mathlib.with_bot

/-!
# Alternative extensions

The alternative extension map, aka A-map, from `γ` to `δ` sends a code of extension `γ` to its
lternative extension `δ`. This will used to identify codes and construct the TTT objects.

An important property for intuition is that A-maps have disjoint ranges (except on empty codes) and
are each injective, so if we connect each code to its images under A-maps, we get a tree (except for
empty codes that form a complete graph).

## Main declarations

* `con_nf.A_map`: Alternative extension map as a map from sets of `γ`-tangles to of `δ`-tangles.
  Note that `γ` can be any type index while `δ` has to be a proper type index.
* `con_nf.A_map_code`: Alternative extension map as a map from codes to codes of extension `δ`.
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
open params
variables [params.{u}] {α β δ ε : Λ} [phase_1a.{u} α] {hβ : β ≤ α} {γ : type_index} {hγ : γ < α}
  {hδ : δ < α} {s : set (tangle α γ hγ)} {t : tangle α γ hγ} {c d : code α β hβ}

/-- The *alternative extension* map. For a set of tangles `G`, consider the code
`(α, γ, G)`. We then construct the non-empty set `D` such that `(α, δ, D)` is an alternative
extension of the same object in TTT. -/
def A_map (hδ : δ < α) (s : set (tangle α γ hγ)) : set (tangle α δ $ coe_lt_coe.2 hδ) :=
to_tangle δ hδ '' ⋃ t ∈ s, local_cardinal (f_map γ δ hγ hδ t)

@[simp] lemma mem_A_map {t : tangle α δ $ coe_lt_coe.2 hδ} :
  t ∈ A_map hδ s ↔ ∃ (t' ∈ s) N (hN : is_near_litter (f_map γ δ hγ hδ t') N),
    to_tangle δ hδ ⟨_, N, hN⟩ = t :=
begin
  simp only [A_map, and_comm, mem_image, mem_Union, exists_prop],
  split,
  { rintro ⟨⟨i, N, hN⟩, ⟨t', (rfl : i = _), ht'⟩, rfl⟩,
    exact ⟨t', ht', N, hN, rfl⟩ },
  { rintro ⟨t', ht', N, hN, rfl⟩,
    exact ⟨⟨_, N, hN⟩, ⟨t', rfl, ht'⟩, rfl⟩ }
end

@[simp] lemma A_map_empty (hδ : δ < α) : A_map hδ (∅ : set (tangle α γ hγ)) = ∅ :=
by simp only [A_map, Union_false, Union_empty, image_empty]

@[simp] lemma A_map_singleton (hδ : δ < α) (t) :
  A_map hδ ({t} : set (tangle α γ hγ)) = to_tangle δ hδ '' local_cardinal (f_map γ δ hγ hδ t) :=
by simp only [A_map, mem_singleton_iff, Union_Union_eq_left]

lemma _root_.set.nonempty.A_map (h : s.nonempty) : (A_map hδ s).nonempty :=
begin
  refine (nonempty_bUnion.2 _).image _,
  exact h.imp (λ t ht, ⟨ht, ⟨f_map γ δ hγ hδ _, litter_set _, is_near_litter_litter_set _⟩, rfl⟩),
end

@[simp] lemma A_map_eq_empty : A_map hδ s = ∅ ↔ s = ∅ :=
begin
  refine ⟨λ h, not_nonempty_iff_eq_empty.1 $ λ hs, hs.A_map.ne_empty h, _⟩,
  rintro rfl,
  exact A_map_empty _,
end

@[simp] lemma A_map_nonempty : (A_map hδ s).nonempty ↔ s.nonempty :=
by simp_rw [←ne_empty_iff_nonempty, ne.def, A_map_eq_empty]

lemma subset_A_map (hδ : δ < α) (ht : t ∈ s) :
  to_tangle δ hδ '' local_cardinal (f_map γ δ hγ hδ t) ⊆ A_map hδ s :=
image_subset _ $ subset_Union₂ t ht

lemma μ_le_mk_A_map (hδ : δ < α) : s.nonempty → #μ ≤ #(A_map hδ s) :=
begin
  rintro ⟨t, ht⟩,
  refine (cardinal.mk_le_mk_of_subset $ subset_A_map _ ht).trans_eq' _,
  rw [cardinal.mk_image_eq, mk_local_cardinal],
  exact (to_tangle δ hδ).inj',
end

lemma A_map_injective (hδ : δ < α) :
  injective (A_map hδ : set (tangle α γ hγ) → set (tangle α δ $ coe_lt_coe.2 hδ)) :=
(to_tangle _ _).injective.image_injective.comp $ pairwise.bUnion_injective
  (λ x y h, local_cardinal_disjoint _ _ $ (f_map_injective _ _ _ _).ne h) $
  λ _, local_cardinal_nonempty _

lemma A_map_disjoint_range {hβ : β < α} {δ : type_index} {hγ : γ < α} {hδ : δ < α}
  (c : set (tangle α γ hγ)) (d : set (tangle α δ hδ)) (hc : c.nonempty)
  (h : A_map hβ c = A_map hβ d) : γ = δ :=
begin
  obtain ⟨b, hb⟩ := hc,
  have := (subset_Union₂ b hb).trans ((to_tangle _ _).injective.image_injective h).subset,
  obtain ⟨i, -, hi⟩ := mem_Union₂.1 (this (f_map γ β hγ hβ b).to_near_litter_mem_local_cardinal),
  exact f_map_range_eq hi,
end

/-!
We don't need to prove that the ranges of the `A_δ` are disjoint for different `δ`, since this holds
at the type level.

We now show that there are only finitely many iterated images under any inverse A-map.
-/

lemma well_founded_of_tangle {β : type_index} (h : β < α) :
  well_founded (λ a b, of_tangle α h a < of_tangle α h b) :=
inv_image.wf _ is_well_order.wf

/-- The minimum tangle of a nonempty set of tangles. -/
noncomputable def min_tangle (c : {s : set (tangle α γ hγ) // s.nonempty}) : tangle α γ hγ :=
(well_founded_of_tangle hγ).min c.val c.property

lemma min_tangle_mem (c : {s : set (tangle α γ hγ) // s.nonempty}) : min_tangle c ∈ c.val :=
well_founded.min_mem _ c.val c.property

lemma min_tangle_le (c : {s : set (tangle α γ hγ) // s.nonempty}) {x} (hx : x ∈ c.1) :
  of_tangle α hγ (min_tangle c) ≤ of_tangle α hγ x :=
not_lt.1 $ (well_founded_of_tangle hγ).not_lt_min c.val c.property hx

lemma A_map_order (hδ : δ < α) (c : {s : set (tangle α γ hγ) // s.nonempty}) :
  of_tangle α hγ (min_tangle c) <
    of_tangle α (coe_lt_coe.2 hδ) (min_tangle ⟨A_map hδ c.1, c.2.A_map⟩) :=
begin
  obtain ⟨t, ht, s, hs, h⟩ := mem_A_map.1 (min_tangle_mem ⟨A_map hδ c.1, c.2.A_map⟩),
  rw ←h,
  exact (min_tangle_le c ht).trans_lt (f_map_position_raising γ δ hγ hδ t s hs),
end

/-- Tool that lets us use well-founded recursion on codes via `μ`. -/
noncomputable def code_min_map (c : nonempty_code α β hβ) : μ :=
of_tangle α _ $ min_tangle ⟨c.val.elts, c.property⟩

/-- The pullback `<` relation on codes is well-founded. -/
lemma code_wf : well_founded (inv_image μr (code_min_map : nonempty_code α β hβ → μ)) :=
inv_image.wf (code_min_map) μwf.wf

/-- The A-map, phrased as a function on `α`-codes. -/
def A_map_code (hδ : δ < β) (c : code α β hβ) : code α β hβ :=
⟨δ, coe_lt_coe.2 hδ, A_map (hδ.trans_le hβ) c.elts⟩

@[simp] lemma extension_A_map_code (hδ : δ < β) (c : code α β hβ) :
  (A_map_code hδ c).extension = δ := rfl

@[simp] lemma elts_A_map_code (hδ : δ < β) (c : code α β hβ) :
  (A_map_code hδ c).elts = A_map (hδ.trans_le hβ) c.elts := rfl

@[simp] lemma A_map_code_mk (γ hγ s) (hδ : δ < β) :
  A_map_code hδ (⟨γ, hγ, s⟩ : code α β hβ) = ⟨δ, coe_lt_coe.2 hδ, A_map (hδ.trans_le hβ) s⟩ := rfl

@[simp] lemma A_map_code_is_empty {hδ : δ < β} : (A_map_code hδ c).is_empty ↔ c.is_empty :=
by { cases c, exact A_map_eq_empty }

alias A_map_code_is_empty ↔ _ code.is_empty.A_map_code

attribute [protected] code.is_empty.A_map_code

lemma A_map_code_inj_on (hδ : δ < β) :
  {c : code α β hβ | c.elts.nonempty}.inj_on (A_map_code hδ : code α β hβ → code α β hβ) :=
begin
  rintro ⟨γ, hγ, s⟩ hs ⟨ε, hε, t⟩ ht h,
  have := (congr_arg_heq code.elts h).eq,
  dsimp at this,
  have := A_map_disjoint_range _ _ hs this,
  subst this,
  rw A_map_injective _ this,
end

lemma A_map_code_order (hδ : δ < β) (c : nonempty_code α β hβ) :
  code_min_map c < code_min_map ⟨A_map_code hδ c.1, c.2.A_map⟩ :=
A_map_order _ _

/-- This relation on `α`-codes allows us to state that there are only finitely many iterated images
under the inverse A-map. -/
@[mk_iff] inductive A_map_rel' (c : nonempty_code α β hβ) : nonempty_code α β hβ → Prop
| intro (δ : Λ) (hδ : δ < β) : (c : code α β hβ).extension ≠ δ →
  A_map_rel' ⟨A_map_code hδ (c : code α β hβ), c.2.A_map⟩

lemma A_map_subrelation :
  subrelation A_map_rel' (inv_image μr (code_min_map : nonempty_code α β hβ → μ))
| c _ (A_map_rel'.intro δ hδ hc) := A_map_code_order _ _

/-- There are only finitely many iterated images under any inverse A-map. -/
lemma A_map_rel'_well_founded (hβ : β ≤ α) :
  well_founded (A_map_rel' : nonempty_code α β hβ → nonempty_code α β hβ → Prop) :=
A_map_subrelation.wf code_wf

instance : has_well_founded (nonempty_code α β hβ) := ⟨_, A_map_rel'_well_founded hβ⟩

/-- There is at most one inverse under an A-map. This corresponds to the fact that there is only one
code which is related (on the left) to any given code under the A-map relation. -/
lemma A_map_rel'_subsingleton (c : nonempty_code α β hβ) :
  {d : nonempty_code α β hβ | A_map_rel' d c}.subsingleton :=
begin
  intros x hx y hy,
  simp only [subtype.val_eq_coe, ne.def, A_map_rel'_iff, mem_set_of_eq] at hx hy,
  obtain ⟨δ, hδ, -, rfl⟩ := hx,
  obtain ⟨ε, hε, -, h⟩ := hy,
  rw subtype.ext_iff at h,
  have : δ = ε := coe_injective ((code.ext_iff _ _).1 h).1,
  subst this,
  exact subtype.coe_injective (A_map_code_inj_on _ x.2 y.2 h),
end

/-- This relation on `α`-codes allows us to state that there are only finitely many iterated images
under the inverse A-map. -/
@[mk_iff] inductive A_map_rel (c : code α β hβ) : code α β hβ → Prop
| intro (δ : Λ) (hδ : δ < β) : c.extension ≠ δ → A_map_rel (A_map_code hδ c)

infix ` ↝ `:62 := A_map_rel

lemma A_map_rel_subsingleton (hc : c.elts.nonempty) : {d : code α β hβ | d ↝ c}.subsingleton :=
begin
  intros d hd e he,
  simp only [A_map_rel_iff, mem_set_of_eq] at hd he,
  obtain ⟨δ, hδ, heδ, rfl⟩ := hd,
  obtain ⟨ε, hε, -, h⟩ := he,
  have : δ = ε := coe_injective ((code.ext_iff _ _).1 h).1,
  subst this,
  refine A_map_code_inj_on _ (A_map_nonempty.1 hc) _ h,
  rw h at hc,
  exact A_map_nonempty.1 hc,
end

lemma eq_of_A_map_code {hδ : δ < β} {hε : ε < β} (hc : c.elts.nonempty) (hcδ : c.extension ≠ δ)
  (hdε : d.extension ≠ ε) (h : A_map_code hδ c = A_map_code hε d) : c = d :=
begin
  refine A_map_rel_subsingleton (by exact hc.A_map) (A_map_rel.intro _ hδ hcδ) _,
  simp_rw h,
  exact A_map_rel.intro _ _ hdε,
end

lemma A_map_rel_A_map_code {hδ : δ < β} (hd : d.elts.nonempty) (hdδ : d.extension ≠ δ) :
  c ↝ A_map_code hδ d ↔ c = d :=
begin
  refine ⟨λ h, A_map_rel_subsingleton (by exact hd.A_map) h $ A_map_rel.intro _ _ hdδ, _⟩,
  rintro rfl,
  exact ⟨_, _, hdδ⟩,
end

end con_nf
