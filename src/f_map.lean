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

end con_nf
