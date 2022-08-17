import phase2.freedom_of_action.atom_case
import phase2.freedom_of_action.near_litter_case
import phase2.freedom_of_action.flexible_case
import phase2.freedom_of_action.non_flexible_case

open quiver set sum with_bot

universe u

namespace con_nf

variables [params.{u}]
variables {α : Λ} [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [typed_positions.{}] [phase_2_assumptions α] {B : le_index α}

namespace allowable_spec

open struct_perm spec


lemma total_of_is_max_aux (σ : allowable_spec B) (hσ : is_max σ)
  (foa : ∀ (B : lt_index α), freedom_of_action (B : le_index α)) :
  Π (c : support_condition B), c ∈ σ.val.domain
| ⟨inl a, A⟩ := begin
    obtain ⟨ρ, hσρ, hρ⟩ := exists_ge_atom σ a A (λ c hc, total_of_is_max_aux c),
    exact domain_subset_of_le (hσ hσρ) hρ,
  end
| ⟨inr N, A⟩ := begin
    by_cases hnl : litter_set N.fst = N.snd,
    { -- This is a litter.
      have hind : ∀ c (hc : c ≺ ⟨inr N, A⟩), c ∈ σ.val.domain := λ c hc, total_of_is_max_aux c,
      obtain ⟨L, N, hN⟩ := N,
      dsimp only at hnl, rw subtype.coe_mk at hnl, subst hnl,
      by_cases flex L A,
      { -- This litter is flexible.
        obtain ⟨ρ, hρ₁, hρ₂⟩ := exists_ge_flex σ h,
        unfold has_le.le at hρ₁,
        rwa hρ₁.le.antisymm (hσ hρ₁).le },
      { -- This litter is non-flexible.
        unfold flex at h,
        push_neg at h,
        obtain ⟨β, δ, γ, hγ, hδ, hγδ, C, rfl, t, rfl⟩ := h,
        obtain ⟨ρ, hρ₁, hρ₂⟩ := exists_ge_non_flex hγ hδ hγδ t hind foa,
        rw ge_iff_le at hρ₁,
        rwa hρ₁.le.antisymm (hσ hρ₁).le } },
    { -- This is a near-litter.
      obtain ⟨ρ, hρ₁, hρ₂⟩ := exists_ge_near_litter σ N A hnl (λ c hc, total_of_is_max_aux c),
      rw ge_iff_le at hρ₁,
      rwa hρ₁.le.antisymm (hσ hρ₁).le }
  end
using_well_founded { dec_tac := `[assumption] }

/-- Any maximal allowable partial permutation under `≤` is total. -/
lemma total_of_is_max (σ : allowable_spec B) (hσ : is_max σ)
  (foa : ∀ (B : lt_index α), freedom_of_action (B : le_index α)) : σ.val.total :=
total_of_is_max_aux σ hσ foa

/-- Any maximal allowable partial permutation under `≤` is co-total. -/
lemma co_total_of_is_max (σ : allowable_spec B) (hσ : is_max σ)
  (foa : ∀ B : lt_index α, freedom_of_action (B : le_index α)) : σ.val.co_total :=
(total_of_is_max σ⁻¹ (λ ρ hρ, by { rw [←inv_le_inv, inv_inv] at ⊢ hρ, exact hσ hρ }) foa).of_inv

variables (α)

/-- The hypothesis that we are in the synthesised context at `α`.
This allows us to combine a set of allowable permutations at all lower paths into an allowable
permutation at level `α`
This may not be the best way to phrase the assumption - the definition is subject to change when
we actually create a proof of the proposition. -/
def synthesised_context : Prop := Π (σ : allowable_spec ⟨α, path.nil⟩)
  (hσ₁ : σ.val.total)
  (hσ₂ : σ.val.co_total)
  (foa : ∀ (B : lt_index α), freedom_of_action (B : le_index α))
  (lower_allowable : ∀ B : proper_lt_index α, (σ.val.lower B.path).allowable (B : le_index α))
  (exists_lower_allowable :
    ∀ (B : proper_lt_index α), ∃ (π : allowable_path (B : le_index α)),
      π.to_struct_perm.satisfies (σ.val.lower B.path)),
  ∃ π : allowable_path ⟨α, path.nil⟩, π.to_struct_perm.satisfies σ.val

variables {α}

/-- Any allowable partial permutation extends to an allowable permutation at level `α`, given that
it is total and co-total. This is `total-allowable-partial-perm-actual` in the blueprint. -/
lemma extends_to_allowable_of_total (σ : allowable_spec ⟨α, path.nil⟩)
  (hσ₁ : σ.val.total) (hσ₂ : σ.val.co_total)
  (foa : ∀ (B : lt_index α), freedom_of_action (B : le_index α)) (syn : synthesised_context α) :
  ∃ π : allowable_path ⟨α, path.nil⟩, π.to_struct_perm.satisfies σ.val :=
begin
  have lower_allowable : ∀ B : proper_lt_index α, (σ.val.lower B.path).allowable (B : le_index α),
  { intro B,
    have := σ.2.lower B.path (coe_lt_coe.2 $ B.index_lt.trans_le $ le_rfl),
    rw path.nil_comp at this,
    exact this },
  have exists_lower_allowable : ∀ (B : proper_lt_index α), ∃ (π : allowable_path (B : le_index α)),
    π.to_struct_perm.satisfies (σ.val.lower B.path) :=
    λ B, foa B ⟨σ.val.lower B.path, lower_allowable _⟩,
  exact syn σ hσ₁ hσ₂ foa lower_allowable exists_lower_allowable,
end

end allowable_spec

/-- The *freedom of action theorem*. If freedom of action holds at all lower levels and paths (all
`B : lt_index` in our formulation), it holds at level `α`. -/
theorem freedom_of_action_propagates (foa : ∀ B : lt_index α, freedom_of_action (B : le_index α))
  (syn : allowable_spec.synthesised_context α) :
  freedom_of_action ⟨α, path.nil⟩ :=
begin
  intro σ,
  obtain ⟨ρ, -, hσρ, hρ⟩ := σ.maximal_perm,
  have : is_max ρ := λ τ hτ, hρ τ (hσρ.trans hτ) hτ,
  have ρ_total := allowable_spec.total_of_is_max ρ this foa,
  have ρ_co_total := allowable_spec.co_total_of_is_max ρ this foa,
  obtain ⟨π, hπ⟩ := ρ.extends_to_allowable_of_total ρ_total ρ_co_total foa syn,
  exact ⟨π, hπ.mono hσρ.le⟩,
end

end con_nf
