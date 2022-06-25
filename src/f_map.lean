import code

/-!
# f-maps
Consider a code `(α, γ, G)`. We are interested in the alternative extensions of this object at
different proper type indices `δ : Λ`. We will define the function `A_δ` which will map the code
`(α, γ, G)` to a new code `(α, δ, D)`. The elements of `D` are produced by the so-called f-maps.
In particular, elements of `D` are of the form `to_tangle M` where `M` is a near-litter to some
litter `N`, which in turn is given by an f-map.
-/

open with_bot
open_locale cardinal

universe u

namespace con_nf
open params
variables [params.{u}] {α β γ : Λ} [phase_1a.{u} α]

instance (h : β < α) : linear_order (code α β h) := sorry

lemma well_founded_code (h : β < α) : @well_founded (code α β h) (<) := sorry

lemma well_founded_of_tangle (h : β < α) :
  well_founded (λ a b, of_tangle _ h a < of_tangle _ _ b) :=
well_founded.inv_image _ is_well_order.wf

/-!
We now define the f-maps. We will do so in two stages; first, we define it as a function `μ → μ`,
(named `f_map_core`) and then raise it to be litter-valued and defined on tangles. This allows some
nicer definitional properties, such as that the resulting litter is of the form `⟨⟨β, γ⟩, χ⟩` for
`χ : μ`.

The value of an f-map is defined as a litter that satisfies two conditions, the second and third
bullet points on the blueprint (the first is a type-level condition that the resulting litter is of
the form `⟨⟨β, γ⟩, χ⟩`). In order to show that the f-maps are well-defined, we show that this set of
candidate litters is non-empty. In particular, the set of all possible litters has size `μ`, and
each constraint only removes `< μ` elements from this candidate set.

The following two lemmas will prove that for each constraint, we remove less than `μ` litters from
our pool of potential litters.
-/

local attribute [semireducible] litter

/-- Principal segments (sets of the form `{y | y < x}`) have cardinality `< μ`. -/
lemma principal_seg_card_lt (x : μ) : #{y // y < x} < #μ := cardinal.card_typein_lt (<) x μ_ord.symm

/-- Initial segments (sets of the form `{y | y ≤ x}`) have cardinality `< μ`. -/
lemma initial_seg_card_lt (x : μ) : #{y // y ≤ x} < #μ :=
begin
  have : {y | y ≤ x} = {y | y < x} ∪ {x},
  { rw set.union_def, simp, simp_rw le_iff_lt_or_eq },
  rw ← set.coe_set_of, rw this,
  rw cardinal.mk_union_of_disjoint,
  rw set.coe_set_of,
  rw cardinal.mk_singleton,
  by_cases ℵ₀ ≤ #{y // y < x},
  { convert (principal_seg_card_lt x), exact cardinal.add_one_eq h },
  { transitivity ℵ₀,
    push_neg at h, exact cardinal.add_lt_aleph_0 h cardinal.one_lt_aleph_0,
    exact lt_of_le_of_lt κ_regular.aleph_0_le κ_lt_μ },
  { simp }
end

lemma mk_litters_inflationary_constraint' (β γ : Λ) (hβ : β < α) (hγ : γ < α) (x : μ) :
#{N : (Σ i, {s // is_near_litter ⟨⟨β, γ⟩, i⟩ s}) |
  of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, N.fst⟩, N.snd⟩) ≤ x} < #μ :=
begin
  refine lt_of_le_of_lt (cardinal.mk_le_of_injective _) (initial_seg_card_lt x),
  { rintro ⟨⟨i, N⟩, hN⟩, exact ⟨of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, i⟩, N⟩), hN⟩ },
  rintros ⟨⟨i, N⟩, hN⟩ ⟨⟨j, M⟩, hM⟩ h,
  simp at h, obtain ⟨hij, hNM⟩ := h, subst hij, simp at hNM, subst hNM
end

/-- One of the constraints in defining the f-maps is that for all near-litters to the result litter
`N`, they are positioned higher than `x` in `μ` (under `to_tangle`). We show that there are less
than `μ` litters that do *not* satisfy this constraint. -/
lemma mk_litters_inflationary_constraint (β γ : Λ) (hβ : β < α) (hγ : γ < α) (x : μ) :
#{i : μ | ∃ N : {s // is_near_litter ⟨⟨β, γ⟩, i⟩ s},
  of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, i⟩, N⟩) ≤ x} < #μ :=
begin
  suffices : #{i : μ | ∃ N : {s // is_near_litter ⟨⟨β, γ⟩, i⟩ s},
    of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, i⟩, N⟩) ≤ x}
    ≤ #{N : (Σ i, {s // is_near_litter ⟨⟨β, γ⟩, i⟩ s}) |
    of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, N.fst⟩, N.snd⟩) ≤ x},
  { exact lt_of_le_of_lt this (mk_litters_inflationary_constraint' _ _ hβ hγ _) },
  dsimp, refine ⟨⟨λ ⟨i, hi⟩, ⟨⟨i, hi.some⟩, hi.some_spec⟩, _⟩⟩,
  rintros ⟨i, N, hN⟩ ⟨j, M, hM⟩ hij, simp at hij ⊢, exact hij.left
end

/-- Only `< μ` elements of `μ` have been hit so far by f_map_core. -/
lemma mk_litters_inj_constraint (β γ : Λ) (hβ : β < α) (hγ : γ < α) (x : μ)
(f_map_core : Π (y < x), μ) : #{i : μ | ∃ y < x, f_map_core y ‹_› = i} < #μ :=
begin
  have : {i | ∃ y < x, f_map_core y ‹_› = i}
    = {i | ∃ (y : {y // y < x}), f_map_core y.val y.property = i} := by simp,
  rw this, exact lt_of_le_of_lt cardinal.mk_range_le (principal_seg_card_lt x),
end

/-- The core of the definition for the f-maps. This is essentially the definition as in the
blueprint, except that it is defined as a function `μ → μ` instead of from tangles to litters.
However, given the conversion functions in `phase_1a`, it is an easy translation into the true
`f_map` as required. -/
noncomputable def f_map_core (β γ : Λ) (hβ : β < α) (hγ : γ < α) : μ → μ
| x := let f_map_core' := λ (y < x), f_map_core y in have this : {i : μ |
    (∀ N : {s // is_near_litter ⟨⟨β, γ⟩, i⟩ s},
      x < of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, i⟩, N⟩))
    ∧ ∀ y (H : y < x), f_map_core' y H ≠ i
  }.nonempty, begin
    by_contradiction, refine lt_irrefl (#μ) _,
    rw set.not_nonempty_iff_eq_empty at h,
    rw ← cardinal.mk_emptyc_iff at h,

    refine lt_of_le_of_lt _ _,
    exact #{a : μ | (∃ (N : {s // is_near_litter ((β, γ), a) s}),
        (of_tangle γ hγ) ((to_tangle γ hγ) ⟨((β, γ), a), N⟩) ≤ x)
      ∨ ∃ y (H : y < x), f_map_core' y H = a},

    { convert cardinal.mk_union_le
        {i : μ |
          (∀ N : {s // is_near_litter ⟨⟨β, γ⟩, i⟩ s},
            x < of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, i⟩, N⟩))
          ∧ ∀ y (H : y < x), f_map_core' y H ≠ i }
        ({i : μ | ∃ N : {s // is_near_litter ⟨⟨β, γ⟩, i⟩ s},
            of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, i⟩, N⟩) ≤ x}
          ∪ {i : μ | ∃ y (H : y < x), f_map_core' y H = i}) using 1,
      { rw ← cardinal.mk_univ, congr,
        refine (set.eq_univ_of_forall _).symm,
        intro i,
        by_cases h₁ : (∀ (N : subtype (is_near_litter ((β, γ), i))),
          x < (of_tangle γ hγ) ((to_tangle γ hγ) ⟨((β, γ), i), N⟩))
          ∧ ∀ y (H : y < x), f_map_core' y H ≠ i,
        { left, exact h₁ },
        { right,
          dsimp,
          rw not_and_distrib at h₁,
          rw not_forall at h₁,
          cases h₁,
          { left, obtain ⟨N, hN⟩ := h₁, exact ⟨N, le_of_not_lt hN⟩ },
          { right, rw not_forall at h₁, obtain ⟨y, hy⟩ := h₁, simp at hy ⊢, exact ⟨y, hy⟩ } } },
      { rw h, rw zero_add, rw set.union_def, refl } },

    { have inflationary := mk_litters_inflationary_constraint β γ hβ hγ x,
      have inj := mk_litters_inj_constraint β γ hβ hγ x (λ y hy, f_map_core y),
      refine lt_of_le_of_lt (cardinal.mk_union_le _ _) (cardinal.add_lt_of_lt _ inflationary inj),
      exact κ_regular.aleph_0_le.trans κ_le_μ }
  end, this.some
using_well_founded { dec_tac := `[assumption] }

/-- The f-maps. -/
noncomputable def f_map (β γ : Λ) (hβ : β < α) (hγ : γ < α)
(a : tangle α β (coe_lt_coe.2 hβ)) : litter := ⟨⟨β, γ⟩, f_map_core β γ hβ hγ (of_tangle _ _ a)⟩

/-!
The f-maps have a number of useful properties.
This is `f-map-properties` in the blueprint.
TODO: Once these properties have all been proven, we can be (relatively) certain that the definition
of `f_map` is correct.
-/

lemma f_map_injective (β γ : Λ) (hβ : β < α) (hγ : γ < α) : function.injective $ f_map β γ hβ hγ := sorry

lemma f_map_range (β γ : Λ) (hβ : β < α) (hγ : γ < α) (x : tangle α β (coe_lt_coe.2 hβ)) :
(f_map β γ hβ hγ x).fst = ⟨β, γ⟩ := rfl

/-- The f-maps have disjoint ranges; that is, for each choice of pair `(β, γ)`, the range of `f_map`
is disjoint. -/
lemma f_map_disjoint : pairwise (@disjoint (set litter) _ _ on
  (λ ⟨β, γ⟩, set.range (f_map β.val γ.val β.property γ.property)
    : {β // β < α} × {γ // γ < α} → set litter)) :=
begin
  rintros ⟨β₁, γ₁⟩ ⟨β₂, γ₂⟩ hne N hN,
  simp at hN ⊢,
  refine hne _,
  obtain ⟨⟨x₁, hN₁⟩, ⟨x₂, hN₂⟩⟩ := hN,
  have h₁ : N.fst = ⟨β₁, γ₁⟩ := by { rw ← hN₁, exact f_map_range _ _ _ _ _ },
  have h₂ : N.fst = ⟨β₂, γ₂⟩ := by { rw ← hN₂, exact f_map_range _ _ _ _ _ },
  rw h₁ at h₂, simp at h₂, obtain ⟨β_eq, γ_eq⟩ := h₂,
  simp, refine ⟨_, _⟩; ext; assumption,
end

lemma f_map_position_raising (β γ : Λ) (hβ : β < α) (hγ : γ < α) (x : tangle α β (coe_lt_coe.2 hβ))
(N : set atom) (hN : is_near_litter (f_map β γ hβ hγ x) N) :
of_tangle β hβ x < of_tangle γ hγ (to_tangle γ hγ ⟨f_map β γ hβ hγ x, N, hN⟩) := sorry
end con_nf
