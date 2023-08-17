import ConNF.Phase2.Approximation

#align_import phase2.atom_completion

open Set Sum

open scoped Classical

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [PositionData] [Phase2Assumptions α] {β : Iic α} (π : StructApprox β)

namespace StructApprox

open NearLitterApprox Hypothesis

theorem orderIso_apply_mem {S T : Sublitter} {a} {L : Litter}
    (h : (S.OrderIso T a : Atom) ∈ litterSet L) : T.Litter = L :=
  by
  rw [← litter.litter_to_sublitter L, ← sublitter.inter_nonempty_iff]
  exact ⟨_, (S.order_iso T a).Prop, h⟩

theorem orderIso_apply_eq {S T U V : Sublitter} {a b}
    (h : (S.OrderIso T a : Atom) = U.OrderIso V b) : T.Litter = V.Litter :=
  by
  rw [Subtype.coe_eq_iff] at h
  exact (order_iso_apply_mem (T.subset h.some)).symm

/-- Computes the action of a structural approximation `π` on an atom `a`. -/
noncomputable def atomCompletion (A : ExtendedIndex β) (a : Atom) (H : Hypothesis ⟨inl a, A⟩) :
    Atom :=
  if h : a ∈ (π A).atomPerm.domain then π A • a
  else
    ((π A).largestSublitter a.1).OrderIso
      ((π A).largestSublitter
        (H.nearLitterImage A a.1.toNearLitter (Relation.TransGen.single <| Constrains.atom a A)).1)
      ⟨a, (π A).mem_largestSublitter_of_not_mem_domain a h⟩

end StructApprox

end ConNF
