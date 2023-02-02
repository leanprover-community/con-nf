import phase2.atom_completion
import phase2.litter_completion

open set sum
open_locale pointwise

universe u

namespace con_nf

namespace struct_approx
variables [params.{u}] {α : Λ} [position_data.{}] [phase_2_assumptions α]
  {β : Iic α} [freedom_of_action_hypothesis β]

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

def near_litter_completion_map (π : struct_approx β) (hπ : π.free)
  (N : near_litter) (A : extended_index β) (H : hypothesis ⟨inr N, A⟩) : set atom :=
(near_litter_approx.largest_sublitter (π A)
  (litter_completion π hπ N.1 A (near_litter_hypothesis N A H)) ∪
  (π A) • (N \ near_litter_approx.largest_sublitter (π A) N.1)) \
  coe '' ((sublitter_bijection
    (near_litter_approx.largest_sublitter (π A) N.1)
    (near_litter_approx.largest_sublitter (π A)
      (litter_completion π hπ N.1 A (near_litter_hypothesis N A H)))) '' {x | (x : atom) ∉ N})

-- TODO: Move next three lemmas.
lemma near_litter_approx.near_litter_domain_small (π : near_litter_approx) (N : near_litter) :
  small ((N : set atom) ∩ π.atom_perm.domain) :=
begin
  rw [← symm_diff_symm_diff_cancel_left (litter_set N.fst) N, inter_symm_diff_distrib_right],
  exact small.symm_diff (π.domain_small N.fst) (small.mono (inter_subset_left _ _) N.2.prop),
end

lemma largest_sublitter_symm_diff_small (π : near_litter_approx) (N : near_litter) :
  small ((π.largest_sublitter N.fst : set atom) ∆ N) :=
begin
  refine is_near_litter.near _ _,
  exact N.fst,
  exact (near_litter.is_near_litter (π.largest_sublitter N.fst).to_near_litter _).mpr rfl,
  rw near_litter.is_near_litter,
end

lemma largest_sublitter_diff_small (π : near_litter_approx) (N : near_litter) :
  small ((π.largest_sublitter N.fst : set atom) \ N) :=
small.mono (subset_union_left _ _) (largest_sublitter_symm_diff_small π N)

lemma near_litter_completion_map_is_near_litter (π : struct_approx β)
  (hπ : π.free) (N : near_litter) (A : extended_index β) (H : hypothesis ⟨inr N, A⟩) :
  is_near_litter (π.litter_completion hπ N.fst A (near_litter_hypothesis N A H))
    (π.near_litter_completion_map hπ N A H) :=
begin
  simp only [near_litter_completion_map, is_near_litter, is_near,
    set.symm_diff_def, near_litter_approx.coe_largest_sublitter, diff_diff_right],
  refine small.union (small.union _ _) _,
  { rw [← diff_diff, diff_diff_right, diff_self, empty_union],
    exact small.mono (diff_subset _ _) ((π A).domain_small _), },
  { refine small.mono (inter_subset_right _ _) (small.image (small.image _)),
    exact lt_of_eq_of_lt
      (cardinal.mk_sep ((π A).largest_sublitter N.fst : set atom) (λ x, x ∉ N)).symm
      (largest_sublitter_diff_small (π A) N), },
  { rw diff_diff_comm,
    rw union_diff_distrib,
    rw [sdiff_sdiff_self, bot_eq_empty, empty_union],
    refine small.mono (diff_subset _ _) (small.mono (diff_subset _ _) _),
    refine small.image (small.union _ _),
    { refine N.2.prop.mono _,
      rw set.symm_diff_def,
      exact subset_union_right _ _, },
    { exact near_litter_approx.near_litter_domain_small _ _, }, },
end

noncomputable def near_litter_completion (π : struct_approx β) (hπ : π.free)
  (N : near_litter) (A : extended_index β) (H : hypothesis ⟨inr N, A⟩) : near_litter :=
⟨litter_completion π hπ N.1 A (near_litter_hypothesis N A H),
  near_litter_completion_map π hπ N A H,
  near_litter_completion_map_is_near_litter π hπ N A H⟩

end struct_approx

end con_nf
