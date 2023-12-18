import ConNF.FOA.Approximation.NearLitterApprox

open Set

open scoped Classical

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : TypeIndex}
  (π : NearLitterApprox) (A : ExtendedIndex β)

namespace NearLitterApprox

def idOnFlexible : PartialPerm Litter where
  toFun := id
  invFun := id
  domain := {L | Flexible A L} \ π.litterPerm.domain
  toFun_domain' _ h := h
  invFun_domain' _ h := h
  left_inv' _ _ := rfl
  right_inv' _ _ := rfl

theorem idOnFlexible_domain :
    (idOnFlexible π A).domain = {L | Flexible A L} \ π.litterPerm.domain :=
  rfl

theorem idOnFlexible_domain_disjoint : Disjoint π.litterPerm.domain (idOnFlexible π A).domain :=
  by rw [disjoint_iff_inter_eq_empty, idOnFlexible_domain, inter_diff_self]

noncomputable def flexibleCompletionLitterPerm : PartialPerm Litter :=
  PartialPerm.piecewise π.litterPerm (idOnFlexible π A) (idOnFlexible_domain_disjoint π A)

theorem flexibleCompletionLitterPerm_domain :
    (flexibleCompletionLitterPerm π A).domain = π.litterPerm.domain ∪ {L | Flexible A L} := by
  rw [flexibleCompletionLitterPerm, PartialPerm.piecewise_domain, idOnFlexible_domain,
    union_diff_self]

noncomputable def flexibleCompletion : NearLitterApprox
    where
  atomPerm := π.atomPerm
  litterPerm := flexibleCompletionLitterPerm π A
  domain_small := π.domain_small

theorem flexibleCompletion_litterPerm_domain :
    (flexibleCompletion π A).litterPerm.domain = π.litterPerm.domain ∪ {L | Flexible A L} := by
  rw [flexibleCompletion, flexibleCompletionLitterPerm_domain]

theorem flexibleCompletion_litterPerm_domain_free (hπ : π.Free A) :
    (flexibleCompletion π A).litterPerm.domain = {L | Flexible A L} := by
  rw [flexibleCompletion_litterPerm_domain, union_eq_right]
  exact fun L hL => hπ L hL

theorem flexibleCompletion_smul_eq (L : Litter) :
    flexibleCompletion π A • L = flexibleCompletionLitterPerm π A L :=
  rfl

theorem flexibleCompletion_smul_of_mem_domain (L : Litter) (hL : L ∈ π.litterPerm.domain) :
    flexibleCompletion π A • L = π.litterPerm L := by
  rw [flexibleCompletion_smul_eq, flexibleCompletionLitterPerm,
    PartialPerm.piecewise_apply_eq_left hL]

theorem flexibleCompletion_smul_flexible (hπ : π.Free A) (L : Litter) (hL : Flexible A L) :
    Flexible A (flexibleCompletion π A • L) := by
  have := PartialPerm.map_domain (flexibleCompletion π A).litterPerm (x := ?_) ?_
  · rw [flexibleCompletion_litterPerm_domain_free π A hπ] at this
    exact this
  · rw [flexibleCompletion_litterPerm_domain_free π A hπ]
    exact hL

theorem flexibleCompletion_symm_smul_flexible (hπ : π.Free A) (L : Litter) (hL : Flexible A L) :
    Flexible A ((flexibleCompletion π A).symm • L) := by
  have := PartialPerm.map_domain (flexibleCompletion π A).symm.litterPerm (x := ?_) ?_
  · rw [symm_litterPerm, PartialPerm.symm_domain,
      flexibleCompletion_litterPerm_domain_free π A hπ] at this
    exact this
  · rw [symm_litterPerm, PartialPerm.symm_domain,
      flexibleCompletion_litterPerm_domain_free π A hπ]
    exact hL

end NearLitterApprox

end ConNF
