import code

/-!
# f-maps
-/

open with_bot
open_locale cardinal

universe u

namespace con_nf
open params
variables [params.{u}] {α β γ : Λ} [phase_1a.{u} α]

instance (h : β ≤ α) : linear_order (code α β h) := sorry

lemma well_founded_code (h : β ≤ α) : @well_founded (code α β h) (<) := sorry

lemma well_founded_of_tangle (h : β < α) :
  well_founded (λ a b, of_tangle _ h a < of_tangle _ _ b) :=
well_founded.inv_image _ is_well_order.wf

local attribute [semireducible] litter

lemma mk_litters_inflationary_constraint (β γ : Λ) (hβ : β < α) (hγ : γ < α) (x : μ) :
#{y : μ | ∃ N : {s // is_near_litter ⟨⟨β, γ⟩, y⟩ s}, of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, y⟩, N⟩) ≤ x} < #μ :=
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

/-- Only <μ elements of μ have been hit so far by f_map_core. -/
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

noncomputable def f_map_core (β γ : Λ) (hβ : β < α) (hγ : γ < α) : μ → μ
| x := (have this : {i : μ |
    (∀ N : {s // is_near_litter ⟨⟨β, γ⟩, i⟩ s},
      x < of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, i⟩, N⟩))
    ∧ ∀ y < x, f_map_core y ≠ i
  }.nonempty, begin
    have f_map_core' : {y // y < x} → μ := λ ⟨y, hy⟩, f_map_core y,
    sorry
  end, this).some
using_well_founded { dec_tac := `[assumption] }

/-- The f-maps. -/
noncomputable def f_map (β γ : Λ) (hβ : β < α) (hγ : γ < α) (a : tangle α β (coe_lt_coe.2 hβ)) : litter := ⟨⟨β, γ⟩, f_map_core β γ hβ hγ (of_tangle _ _ a)⟩

lemma f_map_injective (β γ : Λ) (hβ : β < α) (hγ : γ < α) : function.injective $ f_map β γ hβ hγ := sorry

lemma f_map_range (β γ : Λ) (hβ : β < α) (hγ : γ < α) (x : tangle α β (coe_lt_coe.2 hβ)) :
(f_map β γ hβ hγ x).fst = ⟨β, γ⟩ := sorry

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
of_tangle β hβ x < of_tangle γ hγ (to_tangle γ hγ (f_map β γ hβ hγ x)) := sorry

end con_nf
