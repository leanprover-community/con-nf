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
  π A • (N ∩ (π A).atom_perm.domain)) ∆
  ⋃ (a : atom) (ha : a ∈ (litter_set N.1 ∆ N) \ (π A).atom_perm.domain),
    {H.atom_image a A (relation.trans_gen.single (constrains.symm_diff N a ha.1 A))}

-- TODO: Move this lemma
lemma near_litter_approx.near_litter_domain_small (π : near_litter_approx) (N : near_litter) :
  small ((N : set atom) ∩ π.atom_perm.domain) :=
begin
  rw [← symm_diff_symm_diff_cancel_left (litter_set N.fst) N, inter_symm_diff_distrib_right],
  exact small.symm_diff (π.domain_small N.fst) (small.mono (inter_subset_left _ _) N.2.prop),
end

/-
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
-/

lemma near_litter_completion_map_is_near_litter (π : struct_approx β)
  (hπ : π.free) (N : near_litter) (A : extended_index β) (H : hypothesis ⟨inr N, A⟩) :
  is_near_litter (π.litter_completion hπ N.fst A (near_litter_hypothesis N A H))
    (π.near_litter_completion_map hπ N A H) :=
begin
  rw [near_litter_completion_map, is_near_litter, is_near, near_litter_approx.coe_largest_sublitter,
    ← symm_diff_assoc, symm_diff_comm, ← small.symm_diff_iff _],
  { rw [set.symm_diff_def, ← diff_diff, sdiff_sdiff_right_self, inf_eq_inter,
      union_diff_distrib, sdiff_sdiff_self, bot_eq_empty, empty_union],
    exact small.union (small.mono (diff_subset _ _) ((π A).domain_small _))
      (small.mono (diff_subset _ _) ((near_litter_approx.near_litter_domain_small _ _).image)), },
  { exact small.bUnion (small.mono (diff_subset _ _) N.2.prop) (λ _ _, small_singleton _), },
end

noncomputable def near_litter_completion (π : struct_approx β) (hπ : π.free)
  (N : near_litter) (A : extended_index β) (H : hypothesis ⟨inr N, A⟩) : near_litter :=
⟨litter_completion π hπ N.1 A (near_litter_hypothesis N A H),
  near_litter_completion_map π hπ N A H,
  near_litter_completion_map_is_near_litter π hπ N A H⟩

@[simp] lemma near_litter_completion_fst_eq (π : struct_approx β) (hπ : π.free)
  (N : near_litter) (A : extended_index β) (H : hypothesis ⟨inr N, A⟩) :
  (π.near_litter_completion hπ N A H).1 =
  litter_completion π hπ N.1 A (near_litter_hypothesis N A H) := rfl

end struct_approx

end con_nf
