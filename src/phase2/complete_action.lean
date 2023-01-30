import phase2.atom_completion
import phase2.litter_completion

open set sum
open_locale pointwise

universe u

namespace con_nf
variables [params.{u}] {α : Λ} [position_data.{}] [phase_2_assumptions α] {β : Iic α}

namespace struct_approx

def near_litter_hypothesis (N : near_litter) (A : extended_index β) (H : hypothesis ⟨inr N, A⟩) :
  hypothesis ⟨inr N.1.to_near_litter, A⟩ := {
  atom_image := λ a B h, H.atom_image a B (begin
    by_cases h' : litter_set N.fst = N.snd,
    suffices : N.fst.to_near_litter = N,
    { rwa this at h, },
    { ext : 1,
      refl,
      exact h', },
    exact relation.trans_gen.tail h (constrains.near_litter N h' A),
  end),
  near_litter_image := λ N' B h, H.near_litter_image N' B (begin
    by_cases h' : litter_set N.fst = N.snd,
    suffices : N.fst.to_near_litter = N,
    { rwa this at h, },
    { ext : 1,
      refl,
      exact h', },
    exact relation.trans_gen.tail h (constrains.near_litter N h' A),
  end),
}

def near_litter_completion_map (π : struct_approx β) (hfoa : ∀ γ < β, freedom_of_action γ)
  (N : near_litter) (A : extended_index β) (H : hypothesis ⟨inr N, A⟩) : set atom :=
(near_litter_approx.largest_sublitter (π A)
  (litter_completion π hfoa N.1 A (near_litter_hypothesis N A H)) ∪
  (π A) • (N \ near_litter_approx.largest_sublitter (π A) N.1)) \
  coe '' ((sublitter_bijection
    (near_litter_approx.largest_sublitter (π A) N.1)
    (near_litter_approx.largest_sublitter (π A)
      (litter_completion π hfoa N.1 A (near_litter_hypothesis N A H)))) '' {x | (x : atom) ∉ N})

lemma near_litter_completion_map_is_near_litter
  (π : struct_approx β) (hfoa : ∀ γ < β, freedom_of_action γ)
  (N : near_litter) (A : extended_index β) (H : hypothesis ⟨inr N, A⟩) :
  is_near_litter (π.litter_completion hfoa N.fst A (near_litter_hypothesis N A H))
    (π.near_litter_completion_map hfoa N A H) :=
begin
  simp only [near_litter_completion_map, is_near_litter, is_near,
    set.symm_diff_def, near_litter_approx.coe_largest_sublitter],
  -- TODO: respell near_litter_completion_map to have nicer properties
  sorry
end

noncomputable def near_litter_completion (π : struct_approx β) (hfoa : ∀ γ < β, freedom_of_action γ)
  (N : near_litter) (A : extended_index β) (H : hypothesis ⟨inr N, A⟩) : near_litter :=
⟨litter_completion π hfoa N.1 A (near_litter_hypothesis N A H),
  near_litter_completion_map π hfoa N A H,
  near_litter_completion_map_is_near_litter π hfoa N A H⟩

end struct_approx

end con_nf
