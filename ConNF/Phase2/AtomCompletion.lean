import ConNF.Phase2.Approximation

open Set Sum

open scoped Classical

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [PositionData] [Phase2Assumptions α] {β : Iic α} (π : StructApprox β)

namespace StructApprox

open NearLitterApprox Hypothesis

theorem orderIso_apply_mem {S T : Sublitter} {a} {L : Litter}
    (h : (S.orderIso T a : Atom) ∈ litterSet L) : T.litter = L := by
  rw [← Litter.litter_toSublitter L, ← Sublitter.inter_nonempty_iff]
  exact ⟨_, (S.orderIso T a).prop, h⟩

theorem orderIso_apply_eq {S T U V : Sublitter} {a b}
    (h : (S.orderIso T a : Atom) = U.orderIso V b) : T.litter = V.litter := by
  rw [Subtype.coe_eq_iff] at h
  exact (orderIso_apply_mem (T.subset h.choose)).symm

/-- Computes the action of a structural approximation `π` on an atom `a`. -/
noncomputable def atomCompletion (A : ExtendedIndex β) (a : Atom) (H : Hypothesis ⟨inl a, A⟩) :
    Atom :=
  if h : a ∈ (π A).atomPerm.domain then π A • a
  else
    ((π A).largestSublitter a.1).orderIso
      ((π A).largestSublitter
        (H.nearLitterImage A a.1.toNearLitter (Relation.TransGen.single <| Constrains.atom a A)).1)
      ⟨a, (π A).mem_largestSublitter_of_not_mem_domain a h⟩

end StructApprox

end ConNF
