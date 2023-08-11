import phase2.litter_completion

open set sum
open_locale pointwise

universe u

namespace con_nf

namespace struct_approx
variables [params.{u}] {α : Λ} [position_data.{}] [phase_2_assumptions α]
  {β : Iic α} [freedom_of_action_hypothesis β]

def near_litter_hypothesis (A : extended_index β) (N : near_litter) (H : hypothesis ⟨inr N, A⟩) :
  hypothesis ⟨inr N.1.to_near_litter, A⟩ := {
  atom_image := λ B a h, H.atom_image B a (begin
    by_cases h' : litter_set N.fst = N.snd,
    suffices : N.fst.to_near_litter = N,
    { rwa this at h, },
    { ext : 1,
      refl,
      exact h', },
    exact relation.trans_gen.tail h (constrains.near_litter N h' A),
  end),
  near_litter_image := λ B N' h, H.near_litter_image B N' (begin
    by_cases h' : litter_set N.fst = N.snd,
    suffices : N.fst.to_near_litter = N,
    { rwa this at h, },
    { ext : 1,
      refl,
      exact h', },
    exact relation.trans_gen.tail h (constrains.near_litter N h' A),
  end),
}

def near_litter_completion_map (π : struct_approx β)
  (A : extended_index β) (N : near_litter) (H : hypothesis ⟨inr N, A⟩) : set atom :=
(near_litter_approx.largest_sublitter (π A)
  (π.litter_completion A N.1 (near_litter_hypothesis A N H)) ∪
  π A • (N ∩ (π A).atom_perm.domain)) ∆
  ⋃ (a : atom) (ha : a ∈ (litter_set N.1 ∆ N) \ (π A).atom_perm.domain),
    {H.atom_image A a (relation.trans_gen.single (constrains.symm_diff N a ha.1 A))}

lemma near_litter_completion_map_is_near_litter (π : struct_approx β)
  (A : extended_index β) (N : near_litter) (H : hypothesis ⟨inr N, A⟩) :
  is_near_litter (π.litter_completion A N.fst (near_litter_hypothesis A N H))
    (π.near_litter_completion_map A N H) :=
begin
  rw [near_litter_completion_map, is_near_litter, is_near, near_litter_approx.coe_largest_sublitter,
    ← symm_diff_assoc, symm_diff_comm, ← small.symm_diff_iff _],
  { rw [set.symm_diff_def, ← diff_diff, sdiff_sdiff_right_self, inf_eq_inter,
      union_diff_distrib, sdiff_sdiff_self, bot_eq_empty, empty_union],
    exact small.union (small.mono (diff_subset _ _) ((π A).domain_small _))
      (small.mono (diff_subset _ _) ((near_litter_approx.near_litter_domain_small _ _).image)), },
  { exact small.bUnion (small.mono (diff_subset _ _) N.2.prop) (λ _ _, small_singleton _), },
end

noncomputable def near_litter_completion (π : struct_approx β)
  (A : extended_index β) (N : near_litter) (H : hypothesis ⟨inr N, A⟩) : near_litter :=
⟨litter_completion π A N.1 (near_litter_hypothesis A N H),
  near_litter_completion_map π A N H,
  near_litter_completion_map_is_near_litter π A N H⟩

@[simp] lemma near_litter_completion_fst_eq (π : struct_approx β)
  (A : extended_index β) (N : near_litter) (H : hypothesis ⟨inr N, A⟩) :
  (π.near_litter_completion A N H).1 =
  litter_completion π A N.1 (near_litter_hypothesis A N H) := rfl

end struct_approx

end con_nf
