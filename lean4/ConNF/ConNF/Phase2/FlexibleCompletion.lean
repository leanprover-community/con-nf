import ConNF.Phase2.Approximation

#align_import phase2.flexible_completion

open Set

open scoped Classical

universe u

namespace ConNf

variable [Params.{u}] (α : Λ) [PositionData] [Phase2Assumptions α] {β : TypeIndex}
  (π : NearLitterApprox) (A : ExtendedIndex β)

namespace NearLitterApprox

def idOnFlexible : LocalPerm Litter where
  toFun := id
  invFun := id
  domain := {L | Flexible α L A} \ π.litterPerm.domain
  toFun_domain' L h := h
  invFun_domain' L h := h
  left_inv' L h := rfl
  right_inv' L h := rfl

theorem idOnFlexible_domain :
    (idOnFlexible α π A).domain = {L | Flexible α L A} \ π.litterPerm.domain :=
  rfl

theorem idOnFlexible_domain_disjoint : Disjoint π.litterPerm.domain (idOnFlexible α π A).domain :=
  by rw [disjoint_iff_inter_eq_empty, id_on_flexible_domain, inter_diff_self]

noncomputable def flexibleCompletionLitterPerm : LocalPerm Litter :=
  LocalPerm.piecewise π.litterPerm (idOnFlexible α π A) (idOnFlexible_domain_disjoint α π A)

theorem flexibleCompletionLitterPerm_domain' :
    (flexibleCompletionLitterPerm α π A).domain = π.litterPerm.domain ∪ {L | Flexible α L A} := by
  rw [flexible_completion_litter_perm, LocalPerm.piecewise_domain, id_on_flexible_domain,
    union_diff_self]

noncomputable def flexibleCompletion : NearLitterApprox
    where
  atomPerm := π.atomPerm
  litterPerm := flexibleCompletionLitterPerm α π A
  domain_small := π.domain_small

theorem flexibleCompletion_litterPerm_domain :
    (flexibleCompletion α π A).litterPerm.domain = π.litterPerm.domain ∪ {L | Flexible α L A} := by
  rw [flexible_completion, flexible_completion_litter_perm_domain']

theorem flexibleCompletion_litterPerm_domain_free (hπ : π.Free α A) :
    (flexibleCompletion α π A).litterPerm.domain = {L | Flexible α L A} :=
  by
  rw [flexible_completion_litter_perm_domain, union_eq_right_iff_subset]
  exact fun L hL => hπ L hL

theorem flexibleCompletion_smul_eq (L : Litter) :
    flexibleCompletion α π A • L = flexibleCompletionLitterPerm α π A L :=
  rfl

theorem flexibleCompletion_smul_of_mem_domain (L : Litter) (hL : L ∈ π.litterPerm.domain) :
    flexibleCompletion α π A • L = π.litterPerm L := by
  rw [flexible_completion_smul_eq, flexible_completion_litter_perm,
    LocalPerm.piecewise_apply_eq_left hL]

theorem flexibleCompletionSmulFlexible (hπ : π.Free α A) (L : Litter) (hL : Flexible α L A) :
    Flexible α (flexibleCompletion α π A • L) A :=
  by
  have := LocalPerm.map_domain (flexible_completion α π A).litterPerm
  rw [flexible_completion_litter_perm_domain_free α π A hπ] at this
  exact this hL

theorem flexibleCompletionSymmSmulFlexible (hπ : π.Free α A) (L : Litter) (hL : Flexible α L A) :
    Flexible α ((flexibleCompletion α π A).symm • L) A :=
  by
  have := LocalPerm.map_domain (flexible_completion α π A).symm.litterPerm
  rw [symm_litter_perm, LocalPerm.symm_domain,
    flexible_completion_litter_perm_domain_free α π A hπ] at this
  exact this hL

end NearLitterApprox

end ConNf
