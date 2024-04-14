import ConNF.FOA.Basic.Flexible
import ConNF.FOA.LAction.StructLAction
import ConNF.FOA.LAction.FillAtomRange
import ConNF.FOA.LAction.FillAtomOrbits

open Quiver Set

universe u

namespace ConNF

variable [Params.{u}]

/-!
# Refinements of actions
-/

namespace BaseLAction

variable (φ : BaseLAction) (hφ : φ.Lawful)

noncomputable def refine (hφ : φ.Lawful) : BaseLAction :=
  φ.fillAtomRange.fillAtomOrbits (φ.fillAtomRangeLawful hφ)

variable {φ} {hφ}

theorem refineLawful : (φ.refine hφ).Lawful :=
  fillAtomOrbitsLawful _ _ (fillAtomRange_symmDiff_subset_ran hφ)

@[simp]
theorem refine_atomMap {a : Atom} (ha : (φ.atomMap a).Dom) :
    (φ.refine hφ).atomMap a = φ.atomMap a := by
  unfold refine
  refine' Part.ext' _ _
  · simp only [ha, fillAtomOrbits_atomMap, orbitAtomMap_dom_iff,
      fillAtomRange_atomMap, iff_true_iff]
    exact Or.inl (Or.inl ha)
  intros
  refine' (φ.fillAtomRange.orbitAtomMap_eq_of_mem_dom _ _ (Or.inl ha)).trans _
  exact φ.supportedAction_eq_of_dom ha

@[simp]
theorem refine_atomMap_get {a : Atom} (ha : (φ.atomMap a).Dom) :
    ((φ.refine hφ).atomMap a).get (Or.inl (Or.inl ha)) = (φ.atomMap a).get ha := by
  simp only [refine_atomMap ha]

@[simp]
theorem refine_litterMap : (φ.refine hφ).litterMap = φ.litterMap :=
  rfl

theorem refine_precise : Precise (φ.refine hφ) :=
  fillAtomOrbits_precise _ (fillAtomRange_symmDiff_subset_ran hφ)

end BaseLAction

namespace StructLAction

variable {β : TypeIndex} (φ : StructLAction β) (hφ : φ.Lawful)

noncomputable def refine : StructLAction β := fun A => (φ A).refine (hφ A)

variable {φ} {hφ}

theorem refine_lawful : (φ.refine hφ).Lawful := fun _ => BaseLAction.refineLawful

@[simp]
theorem refine_apply {A : ExtendedIndex β} : φ.refine hφ A = (φ A).refine (hφ A) :=
  rfl

theorem refine_atomMap {A : ExtendedIndex β} {a : Atom} (ha : ((φ A).atomMap a).Dom) :
    ((φ A).refine (hφ A)).atomMap a = (φ A).atomMap a :=
  BaseLAction.refine_atomMap ha

@[simp]
theorem refine_atomMap_get {A : ExtendedIndex β} {a : Atom} (ha : ((φ A).atomMap a).Dom) :
    (((φ A).refine (hφ A)).atomMap a).get (Or.inl (Or.inl ha)) = ((φ A).atomMap a).get ha :=
  BaseLAction.refine_atomMap_get ha

@[simp]
theorem refine_litterMap {A : ExtendedIndex β} :
    ((φ A).refine (hφ A)).litterMap = (φ A).litterMap :=
  rfl

theorem refine_precise : Precise (φ.refine hφ) := fun _ => BaseLAction.refine_precise

end StructLAction

namespace StructLAction

variable [Level] [BasePositions] [FOAAssumptions] {β : Λ}

/-- Refine and complete this action into a structural approximation. -/
noncomputable def rc (φ : StructLAction β) (h : φ.Lawful) : StructApprox β :=
  (φ.refine h).complete refine_lawful

theorem rc_smul_atom_eq {φ : StructLAction β} {h : φ.Lawful} {B : ExtendedIndex β} {a : Atom}
    (ha : ((φ B).atomMap a).Dom) : φ.rc h B • a = ((φ B).atomMap a).get ha := by
  refine' (BaseLAction.complete_smul_atom_eq _ _).trans _
  · exact Or.inl (Or.inl ha)
  · simp only [refine_apply, refine_atomMap ha]

theorem rc_smul_litter_eq {φ : StructLAction β} {hφ : φ.Lawful} {B : ExtendedIndex β} (L : Litter) :
    φ.rc hφ B • L = (φ.refine hφ B).flexibleLitterPartialPerm (refine_lawful B) B L :=
  rfl

theorem rc_symm_smul_litter_eq {φ : StructLAction β} {hφ : φ.Lawful} {B : ExtendedIndex β}
    (L : Litter) :
    (φ.rc hφ B).symm • L = ((φ.refine hφ B).flexibleLitterPartialPerm (refine_lawful B) B).symm L :=
  rfl

theorem rc_free (φ : StructLAction β) (h₁ : φ.Lawful) (h₂ : φ.MapFlexible) :
    (φ.rc h₁).Free := by
  rintro B L' ((hL' | ⟨L', hL', rfl⟩) | hL')
  · exact hL'.2
  · rw [BaseLAction.roughLitterMapOrElse_of_dom _ hL'.1]
    exact h₂ B L' hL'.1 hL'.2
  · exact (PartialPerm.sandboxSubset_subset _ _ hL').2

theorem rc_comp_atomPerm {γ : Λ} {φ : StructLAction β} {hφ : φ.Lawful}
    (A : Path (β : TypeIndex) γ) (B : ExtendedIndex γ) :
    (rc (φ.comp A) (hφ.comp A) B).atomPerm =
    (φ.rc hφ (A.comp B)).atomPerm := by
  unfold rc refine complete BaseLAction.refine BaseLAction.complete
  simp_rw [Tree.comp_apply]

theorem rc_comp_smul_atom {γ : Λ} {φ : StructLAction β} {hφ : φ.Lawful}
    (A : Path (β : TypeIndex) γ) (B : ExtendedIndex γ) (a : Atom) :
    rc (φ.comp A) (hφ.comp A) B • a = φ.rc hφ (A.comp B) • a := by
  change BaseApprox.atomPerm _ _ = BaseApprox.atomPerm _ _
  rw [rc_comp_atomPerm]

end StructLAction

end ConNF
