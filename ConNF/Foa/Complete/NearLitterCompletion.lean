import ConNF.Foa.Complete.LitterCompletion

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
        by_cases h' : litterSet N.fst = N.snd
        suffices N.fst.toNearLitter = N by rwa [this] at h
        · ext : 1
          exact h'
        exact Relation.TransGen.tail h (Constrains.nearLitter N h' A))
  nearLitterImage B N' h :=
    H.nearLitterImage B N'
      (by
        by_cases h' : litterSet N.fst = N.snd
        suffices N.fst.toNearLitter = N by rwa [this] at h
        · ext : 1
          exact h'
        exact Relation.TransGen.tail h (Constrains.nearLitter N h' A))

def nearLitterCompletionMap (π : StructApprox β) (A : ExtendedIndex β) (N : NearLitter)
    (H : Hypothesis ⟨inr N, A⟩) : Set Atom :=
  (NearLitterApprox.largestSublitter (π A) (π.litterCompletion A N.1 (nearLitterHypothesis A N H)) ∪
      π A • ((N : Set Atom) ∩ (π A).atomPerm.domain)) ∆
    ⋃ (a : Atom) (ha : a ∈ litterSet N.1 ∆ N \ (π A).atomPerm.domain),
      {H.atomImage A a (Relation.TransGen.single (Constrains.symmDiff N a ha.1 A))}

theorem nearLitterCompletionMap_isNearLitter (π : StructApprox β) (A : ExtendedIndex β)
    (N : NearLitter) (H : Hypothesis ⟨inr N, A⟩) :
    IsNearLitter (π.litterCompletion A N.fst (nearLitterHypothesis A N H))
      (π.nearLitterCompletionMap A N H) := by
  rw [nearLitterCompletionMap, IsNearLitter, IsNear, NearLitterApprox.coe_largestSublitter,
    ← symmDiff_assoc, symmDiff_comm, ← Small.symmDiff_iff _]
  · rw [Set.symmDiff_def, ← diff_diff, sdiff_sdiff_right_self, union_diff_distrib,
      sdiff_sdiff_self, bot_eq_empty, empty_union]
    exact Small.union (Small.mono (diff_subset _ _) ((π A).domain_small _))
      (Small.mono (diff_subset _ _) (NearLitterApprox.nearLitter_domain_small _ _).image)
  · exact Small.bUnion (Small.mono (diff_subset _ _) N.2.prop) fun _ _ => small_singleton _

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