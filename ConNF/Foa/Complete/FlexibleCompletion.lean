import ConNF.Foa.Approximation.NearLitterApprox

open Set

open scoped Classical

universe u

namespace ConNF

variable [Params.{u}] (α : Λ) [BasePositions] [FoaAssumptions α] {β : TypeIndex}
  (π : NearLitterApprox) (A : ExtendedIndex β)

namespace NearLitterApprox

def idOnFlexible : LocalPerm Litter where
  toFun := id
  invFun := id
  domain := {L | Flexible α A L} \ π.litterPerm.domain
  toFun_domain' _ h := h
  invFun_domain' _ h := h
  left_inv' _ _ := rfl
  right_inv' _ _ := rfl

theorem idOnFlexible_domain :
    (idOnFlexible α π A).domain = {L | Flexible α A L} \ π.litterPerm.domain :=
  rfl

theorem idOnFlexible_domain_disjoint : Disjoint π.litterPerm.domain (idOnFlexible α π A).domain :=
  by rw [disjoint_iff_inter_eq_empty, idOnFlexible_domain, inter_diff_self]

noncomputable def flexibleCompletionLitterPerm : LocalPerm Litter :=
  LocalPerm.piecewise π.litterPerm (idOnFlexible α π A) (idOnFlexible_domain_disjoint α π A)

theorem flexibleCompletionLitterPerm_domain :
    (flexibleCompletionLitterPerm α π A).domain = π.litterPerm.domain ∪ {L | Flexible α A L} := by
  rw [flexibleCompletionLitterPerm, LocalPerm.piecewise_domain, idOnFlexible_domain,
    union_diff_self]

noncomputable def flexibleCompletion : NearLitterApprox
    where
  atomPerm := π.atomPerm
  litterPerm := flexibleCompletionLitterPerm α π A
  domain_small := π.domain_small

theorem flexibleCompletion_litterPerm_domain :
    (flexibleCompletion α π A).litterPerm.domain = π.litterPerm.domain ∪ {L | Flexible α A L} := by
  rw [flexibleCompletion, flexibleCompletionLitterPerm_domain]

theorem flexibleCompletion_litterPerm_domain_free (hπ : π.Free α A) :
    (flexibleCompletion α π A).litterPerm.domain = {L | Flexible α A L} := by
  rw [flexibleCompletion_litterPerm_domain, union_eq_right]
  exact fun L hL => hπ L hL

theorem flexibleCompletion_smul_eq (L : Litter) :
    flexibleCompletion α π A • L = flexibleCompletionLitterPerm α π A L :=
  rfl

theorem flexibleCompletion_smul_of_mem_domain (L : Litter) (hL : L ∈ π.litterPerm.domain) :
    flexibleCompletion α π A • L = π.litterPerm L := by
  rw [flexibleCompletion_smul_eq, flexibleCompletionLitterPerm,
    LocalPerm.piecewise_apply_eq_left hL]

theorem flexibleCompletion_smul_flexible (hπ : π.Free α A) (L : Litter) (hL : Flexible α A L) :
    Flexible α A (flexibleCompletion α π A • L) := by
  have := LocalPerm.map_domain (flexibleCompletion α π A).litterPerm (x := ?_) ?_
  · rw [flexibleCompletion_litterPerm_domain_free α π A hπ] at this
    exact this
  · rw [flexibleCompletion_litterPerm_domain_free α π A hπ]
    exact hL

theorem flexibleCompletion_symm_smul_flexible (hπ : π.Free α A) (L : Litter) (hL : Flexible α A L) :
    Flexible α A ((flexibleCompletion α π A).symm • L) := by
  have := LocalPerm.map_domain (flexibleCompletion α π A).symm.litterPerm (x := ?_) ?_
  · rw [symm_litterPerm, LocalPerm.symm_domain,
      flexibleCompletion_litterPerm_domain_free α π A hπ] at this
    exact this
  · rw [symm_litterPerm, LocalPerm.symm_domain,
      flexibleCompletion_litterPerm_domain_free α π A hπ]
    exact hL

end NearLitterApprox

end ConNF
