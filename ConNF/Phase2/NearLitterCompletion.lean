import ConNF.Phase2.LitterCompletion

#align_import phase2.near_litter_completion

open Set Sum

open scoped Pointwise

universe u

namespace ConNF

namespace StructApprox

variable [Params.{u}] {α : Λ} [PositionData] [Phase2Assumptions α] {β : Iic α}
  [FreedomOfActionHypothesis β]

def nearLitterHypothesis (A : ExtendedIndex β) (N : NearLitter) (H : Hypothesis ⟨inr N, A⟩) :
    Hypothesis ⟨inr N.1.toNearLitter, A⟩
    where
  atomImage B a h :=
    H.atomImage B a
      (by
        by_cases h' : litter_set N.fst = N.snd
        suffices N.fst.to_near_litter = N by rwa [this] at h
        · ext : 1
          rfl
          exact h'
        exact Relation.TransGen.tail h (constrains.near_litter N h' A))
  nearLitterImage B N' h :=
    H.nearLitterImage B N'
      (by
        by_cases h' : litter_set N.fst = N.snd
        suffices N.fst.to_near_litter = N by rwa [this] at h
        · ext : 1
          rfl
          exact h'
        exact Relation.TransGen.tail h (constrains.near_litter N h' A))

def nearLitterCompletionMap (π : StructApprox β) (A : ExtendedIndex β) (N : NearLitter)
    (H : Hypothesis ⟨inr N, A⟩) : Set Atom :=
  (NearLitterApprox.largestSublitter (π A) (π.litterCompletion A N.1 (nearLitterHypothesis A N H)) ∪
      π A • (N ∩ (π A).atomPerm.domain)) ∆
    ⋃ (a : Atom) (ha : a ∈ litterSet N.1 ∆ N \ (π A).atomPerm.domain),
      {H.atomImage A a (Relation.TransGen.single (Constrains.symm_diff N a ha.1 A))}

theorem nearLitterCompletionMap_isNearLitter (π : StructApprox β) (A : ExtendedIndex β)
    (N : NearLitter) (H : Hypothesis ⟨inr N, A⟩) :
    IsNearLitter (π.litterCompletion A N.fst (nearLitterHypothesis A N H))
      (π.nearLitterCompletionMap A N H) :=
  by
  rw [near_litter_completion_map, is_near_litter, is_near, near_litter_approx.coe_largest_sublitter,
    ← symmDiff_assoc, symmDiff_comm, ← small.symm_diff_iff _]
  · rw [Set.symmDiff_def, ← diff_diff, sdiff_sdiff_right_self, inf_eq_inter, union_diff_distrib,
      sdiff_sdiff_self, bot_eq_empty, empty_union]
    exact
      small.union (small.mono (diff_subset _ _) ((π A).domain_small _))
        (small.mono (diff_subset _ _) (near_litter_approx.near_litter_domain_small _ _).image)
  · exact small.bUnion (small.mono (diff_subset _ _) N.2.Prop) fun _ _ => small_singleton _

noncomputable def nearLitterCompletion (π : StructApprox β) (A : ExtendedIndex β) (N : NearLitter)
    (H : Hypothesis ⟨inr N, A⟩) : NearLitter :=
  ⟨litterCompletion π A N.1 (nearLitterHypothesis A N H), nearLitterCompletionMap π A N H,
    nearLitterCompletionMap_isNearLitter π A N H⟩

@[simp]
theorem nearLitterCompletion_fst_eq (π : StructApprox β) (A : ExtendedIndex β) (N : NearLitter)
    (H : Hypothesis ⟨inr N, A⟩) :
    (π.nearLitterCompletion A N H).1 = litterCompletion π A N.1 (nearLitterHypothesis A N H) :=
  rfl

end StructApprox

end ConNF
