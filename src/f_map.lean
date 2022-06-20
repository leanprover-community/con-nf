import code

/-!
# f-maps
-/

open with_bot

universe u

namespace con_nf
open params
variables [params.{u}] {α β γ : Λ} [phase_1a.{u} α]

instance (h : β ≤ α) : linear_order (code α β h) := sorry

lemma well_founded_code (h : β ≤ α) : @well_founded (code α β h) (<) := sorry

lemma well_founded_of_tangle (h : β < α) :
  well_founded (λ a b, of_tangle _ h a < of_tangle _ _ b) :=
well_founded.inv_image _ is_well_order.wf

/-- The f-maps. -/
noncomputable def f_map (β γ : Λ) (hβ : β ≤ α) (hγ : γ < α) : tangle α γ (coe_lt_coe.2 hγ) → litter
| a := (sorry : {i | of_tangle _ _ a < of_tangle _ hγ (to_tangle _ _ i) ∧
    ∀ b, of_tangle _ hγ b < of_tangle _ _ a → f_map b ≠ i}.nonempty).some
using_well_founded
{ rel_tac := λ _ _, `[exact ⟨λ a b, of_tangle _ _ a < of_tangle _ _ b, well_founded_of_tangle _⟩],
  dec_tac := `[assumption] }

lemma f_map_injective (β γ : Λ) (hβ : β ≤ α) (hγ : γ < α) : function.injective $ f_map β γ hβ hγ := sorry

local attribute [semireducible] litter

lemma f_map_range (β γ : Λ) (hβ : β ≤ α) (hγ : γ < α) (x : tangle α γ (coe_lt_coe.2 hγ)) :
(f_map β γ hβ hγ x).fst = ⟨β, γ⟩ := sorry

/-- The f-maps have disjoint ranges; that is, for each choice of pair `(β, γ)`, the range of `f_map`
is disjoint. -/
lemma f_map_disjoint : pairwise (@disjoint (set litter) _ _ on
  (λ ⟨β, γ⟩, set.range (f_map β.val γ.val β.property γ.property)
    : {β // β ≤ α} × {γ // γ < α} → set litter)) :=
begin
  rintros ⟨β₁, γ₁⟩ ⟨β₂, γ₂⟩ hne N hN,
  simp at hN ⊢,
  refine hne _,
  obtain ⟨⟨x₁, hN₁⟩, ⟨x₂, hN₂⟩⟩ := hN,
  have h₁ : N.fst = ⟨β₁, γ₁⟩ := by { rw ← hN₁, exact f_map_range _ _ _ _ _ },
  have h₂ : N.fst = ⟨β₂, γ₂⟩ := by { rw ← hN₂, exact f_map_range _ _ _ _ _ },
  rw h₁ at h₂, simp at h₂, obtain ⟨β_eq, γ_eq⟩ := h₂,
  simp, refine ⟨_, _⟩; ext; assumption
end

lemma f_map_position_raising (β γ : Λ) (hβ : β ≤ α) (hγ : γ < α) (x : tangle α γ (coe_lt_coe.2 hγ))
(N : set atom) (hN : is_near_litter (f_map β γ hβ hγ x) N) :
of_tangle γ hγ x < of_tangle γ hγ (to_tangle γ hγ (f_map β γ hβ hγ x)) := sorry

end con_nf
