import ConNF.Foa.Basic.Flexible
import ConNF.Foa.Action.StructAction
import ConNF.Foa.Action.FillAtomRange
import ConNF.Foa.Action.FillAtomOrbits

open Quiver Set

universe u

namespace ConNF

variable [Params.{u}]

/-!
# Refinements of actions
-/

namespace NearLitterAction

variable (φ : NearLitterAction) (hφ : φ.Lawful)

noncomputable def refine (hφ : φ.Lawful) : NearLitterAction :=
  φ.fillAtomRange.fillAtomOrbits (φ.fillAtomRangeLawful hφ)

variable {φ} {hφ}

theorem refineLawful : (φ.refine hφ).Lawful :=
  fillAtomOrbitsLawful _ _ (fillAtomRange_symmDiff_subset_ran hφ)

@[simp]
theorem refine_atomMap {a : Atom} (ha : (φ.atomMap a).Dom) :
    (φ.refine hφ).atomMap a = φ.atomMap a :=
  by
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

end NearLitterAction

namespace StructAction

variable {β : TypeIndex} (φ : StructAction β) (hφ : φ.Lawful)

noncomputable def refine : StructAction β := fun A => (φ A).refine (hφ A)

variable {φ} {hφ}

theorem refine_lawful : (φ.refine hφ).Lawful := fun _ => NearLitterAction.refineLawful

@[simp]
theorem refine_apply {A : ExtendedIndex β} : φ.refine hφ A = (φ A).refine (hφ A) :=
  rfl

theorem refine_atomMap {A : ExtendedIndex β} {a : Atom} (ha : ((φ A).atomMap a).Dom) :
    ((φ A).refine (hφ A)).atomMap a = (φ A).atomMap a :=
  NearLitterAction.refine_atomMap ha

@[simp]
theorem refine_atomMap_get {A : ExtendedIndex β} {a : Atom} (ha : ((φ A).atomMap a).Dom) :
    (((φ A).refine (hφ A)).atomMap a).get (Or.inl (Or.inl ha)) = ((φ A).atomMap a).get ha :=
  NearLitterAction.refine_atomMap_get ha

@[simp]
theorem refine_litterMap {A : ExtendedIndex β} :
    ((φ A).refine (hφ A)).litterMap = (φ A).litterMap :=
  rfl

theorem refine_precise : Precise (φ.refine hφ) := fun _ => NearLitterAction.refine_precise

theorem refineSupports {α : Λ} [BasePositions] [Phase2Assumptions α] {β : Iio α} {t : Tangle β}
    (φ : StructAction β) (hφ : φ.Lawful) (h : φ.Supports t) : (φ.refine hφ).Supports t :=
  { atom_mem := fun a B ha => Or.inl (Or.inl <| h.atom_mem a B ha)
    litter_mem := h.litter_mem }

end StructAction

namespace StructAction

variable {α : Λ} [BasePositions] [Phase2Assumptions α] {β : Iio α}

/-- Refine and complete this action into a structural approximation. -/
noncomputable def rc (φ : StructAction β) (h : φ.Lawful) : StructApprox β :=
  (φ.refine h).complete refine_lawful

theorem rc_smul_atom_eq {φ : StructAction β} {h : φ.Lawful} {B : ExtendedIndex β} {a : Atom}
    (ha : ((φ B).atomMap a).Dom) : φ.rc h B • a = ((φ B).atomMap a).get ha := by
  refine' (NearLitterAction.complete_smul_atom_eq _ _).trans _
  · exact Or.inl (Or.inl ha)
  · simp only [refine_apply, refine_atomMap ha]

theorem rc_smul_litter_eq {φ : StructAction β} {hφ : φ.Lawful} {B : ExtendedIndex β} (L : Litter) :
    φ.rc hφ B • L = (φ.refine hφ B).flexibleLitterPerm (refine_lawful B) B L :=
  rfl

theorem rc_free (φ : StructAction β) (h₁ : φ.Lawful) (h₂ : φ.MapFlexible) :
    (show StructApprox (β : Iic α) from φ.rc h₁).Free := by
  rintro B L' ((hL' | ⟨L', hL', rfl⟩) | hL')
  · exact hL'.2
  · rw [NearLitterAction.roughLitterMapOrElse_of_dom _ hL'.1]
    exact h₂ L' B hL'.1 hL'.2
  · exact (LocalPerm.sandboxSubset_subset _ _ hL').2

theorem rc_comp_atomPerm {γ : Iio α} {φ : StructAction β} {hφ : φ.Lawful}
    (A : Path (β : TypeIndex) γ) (B : ExtendedIndex γ) :
    ((φ.comp A).rc (hφ.comp A) B).atomPerm = (φ.rc hφ (A.comp B)).atomPerm := by
  unfold rc refine complete NearLitterAction.refine NearLitterAction.complete
  simp_rw [StructAction.comp_apply]

theorem rc_comp_smul_atom {γ : Iio α} {φ : StructAction β} {hφ : φ.Lawful}
    (A : Path (β : TypeIndex) γ) (B : ExtendedIndex γ) (a : Atom) :
    (φ.comp A).rc (hφ.comp A) B • a = φ.rc hφ (A.comp B) • a := by
  change NearLitterApprox.atomPerm _ _ = NearLitterApprox.atomPerm _ _
  rw [rc_comp_atomPerm]

end StructAction

end ConNF
