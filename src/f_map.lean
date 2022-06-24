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

/-- One of the constraints in defining the f-maps is that for all near-litters to the result litter
`N`, they are positioned higher than `x` in `μ` (under `to_tangle`). We show that there are less
than `μ` litters that do *not* satisfy this constraint. -/
lemma mk_litters_inflationary_constraint (β γ : Λ) (hβ : β < α) (hγ : γ < α) (x : μ) :
#{y : μ | ∃ N : {s // is_near_litter ⟨⟨β, γ⟩, y⟩ s},
  of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, y⟩, N⟩) ≤ x} < #μ :=
begin
  /- 1. reduce to the version before, with the Σ type - the set in the statement of the lemma is the image of "the set of all near litters N such that of_tangle N ≤ of_tangle a", by forgetting the set component
  should be a lemma: where there is a surjective fn, card image ≤ card of domain
  2. this set of near-litters has an injection into the predecessors in μ -- each predecessor can rule out at most one litter -/
  /- rw ← mk_litter,
  refine le_antisymm _ _,
  { rw ← @cardinal.mk_univ litter,
    refine cardinal.mk_le_mk_of_subset _,
    simp },
  { refine ⟨⟨λ j, ⟨_, _⟩, _⟩⟩,
    /- let j_ord := @ordinal.typein _
      (λ i j, of_tangle _ hβ (to_tangle _ _ i) < of_tangle _ hγ (to_tangle _ _ j))
      ⟨well_founded_of_litter hβ hγ⟩ j, -/
    sorry, sorry, sorry } -/
  sorry
end

/-- Only `< μ` elements of `μ` have been hit so far by f_map_core. -/
lemma mk_litters_inj_constraint (β γ : Λ) (hβ : β < α) (hγ : γ < α) (x : μ) (f_map_core' : {y // y < x} → μ) :
#{i : μ | ∃ y, f_map_core' y = i} < #μ :=
begin
  /- same proof sketch; each predecessor can rule out at most one thing -/
  /- have μ,
  choose a well-ordering of μ with smallest order type (as an ordinal)
  the initial ordinal of a cardinal is the smallest order type of a set of that cardinality
  the initial ordinal of μ, all proper initial segments have smaller cardinality than μ
  by contradiction, use this set -/
  sorry
end

/-- The core of the definition for the f-maps. This is essentially the definition as in the
blueprint, except that it is defined as a function `μ → μ` instead of from tangles to litters.
However, given the conversion functions in `phase_1a`, it is an easy translation into the true
`f_map` as required. -/
noncomputable def f_map_core (β γ : Λ) (hβ : β < α) (hγ : γ < α) : μ → μ
| x := (have this : {i : μ |
    (∀ N : {s // is_near_litter ⟨⟨β, γ⟩, i⟩ s},
      x < of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, i⟩, N⟩))
    ∧ ∀ y < x, f_map_core y ≠ i
  }.nonempty, begin
    -- The equation compiler uses `hy` as the condition required for well-founded recursion.
    have f_map_core' : {y // y < x} → μ := λ ⟨y, hy⟩, f_map_core y,
    sorry
  end, this).some
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
