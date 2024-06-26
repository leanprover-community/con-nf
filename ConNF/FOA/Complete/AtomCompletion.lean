import ConNF.FOA.Complete.HypAction
import ConNF.FOA.Approx

/-!
# Induced action: Atoms

In this file, we describe the induced action of an approximation on atoms.

## Main declarations

* `ConNF.StructApprox.atomCompletion`: The induced action of a structural approximation on an atom.
-/

open Set Sum

open scoped Classical

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions] [FOAAssumptions] {β : Λ} (π : StructApprox β)

namespace StructApprox

open BaseApprox HypAction

theorem equiv_apply_mem {S T : Sublitter} {a} {L : Litter}
    (h : (S.equiv T a : Atom) ∈ litterSet L) : T.litter = L := by
  rw [← Litter.litter_toSublitter L, ← Sublitter.inter_nonempty_iff]
  exact ⟨_, (S.equiv T a).prop, h⟩

theorem equiv_apply_eq {S T U V : Sublitter} {a b}
    (h : (S.equiv T a : Atom) = U.equiv V b) : T.litter = V.litter := by
  rw [Subtype.coe_eq_iff] at h
  exact (equiv_apply_mem (T.subset h.choose)).symm

/-- Computes the action of a structural approximation `π` on an atom `a`. -/
noncomputable def atomCompletion (A : ExtendedIndex β) (a : Atom) (H : HypAction ⟨A, inl a⟩) :
    Atom :=
  if h : a ∈ (π A).atomPerm.domain then π A • a
  else
    ((π A).largestSublitter a.1).equiv
      ((π A).largestSublitter
        (H.nearLitterImage A a.1.toNearLitter (Relation.TransGen.single <| Constrains.atom A a)).1)
      ⟨a, (π A).mem_largestSublitter_of_not_mem_domain a h⟩

end StructApprox

end ConNF
