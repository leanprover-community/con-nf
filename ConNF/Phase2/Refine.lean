import ConNF.Phase2.Flexible
import ConNF.Phase2.StructAction
import ConNF.Phase2.FillAtomRange
import ConNF.Phase2.FillAtomOrbits

#align_import phase2.refine

open Quiver Set

universe u

namespace ConNf

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
  · simp only [ha, fill_atom_orbits_atom_map, orbit_atom_map_dom_iff, fill_atom_range_atom_map,
      iff_true_iff]
    exact Or.inl (Or.inl ha)
  intro h₁ h₂
  refine' (φ.fill_atom_range.orbit_atom_map_eq_of_mem_dom _ _ (Or.inl ha)).trans _
  exact φ.supported_action_eq_of_dom ha

@[simp]
theorem refine_atomMap_get {a : Atom} (ha : (φ.atomMap a).Dom) :
    ((φ.refine hφ).atomMap a).get (Or.inl (Or.inl ha)) = (φ.atomMap a).get ha := by
  simp only [refine_atom_map ha]

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

theorem refine_lawful : (φ.refine hφ).Lawful := fun A => NearLitterAction.refineLawful

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

theorem refine_precise : Precise (φ.refine hφ) := fun A => NearLitterAction.refine_precise

theorem refineSupports {α : Λ} [PositionData] [Phase2Assumptions α] {β : Iio α} {t : Tangle β}
    (φ : StructAction β) (hφ : φ.Lawful) (h : φ.Supports t) : (φ.refine hφ).Supports t :=
  { atom_mem := fun a B ha => Or.inl (Or.inl <| h.atom_mem a B ha)
    litter_mem := h.litter_mem }

end StructAction

namespace StructAction

variable {α : Λ} [PositionData] [Phase2Assumptions α] {β : Iio α}

/-- Refine and complete this action into a structural approximation. -/
noncomputable def rc (φ : StructAction β) (h : φ.Lawful) : StructApprox β :=
  (φ.refine h).complete refine_lawful

theorem rc_smul_atom_eq {φ : StructAction β} {h : φ.Lawful} {B : ExtendedIndex β} {a : Atom}
    (ha : ((φ B).atomMap a).Dom) : φ.rc h B • a = ((φ B).atomMap a).get ha :=
  by
  refine' (near_litter_action.complete_smul_atom_eq _ _).trans _
  · exact Or.inl (Or.inl ha)
  · simp only [refine_apply, refine_atom_map ha]

theorem rc_smul_litter_eq {φ : StructAction β} {hφ : φ.Lawful} {B : ExtendedIndex β} (L : Litter) :
    φ.rc hφ B • L = (φ.refine hφ B).flexibleLitterPerm (refine_lawful B) B L :=
  rfl

theorem rcFree (φ : StructAction β) (h₁ : φ.Lawful) (h₂ : φ.MapFlexible) :
    (show StructApprox (β : Iic α) from φ.rc h₁).Free :=
  by
  rintro B L' ((hL' | ⟨L', hL', rfl⟩) | hL')
  · exact hL'.2
  · rw [near_litter_action.rough_litter_map_or_else_of_dom _ hL'.1]
    exact h₂ L' B hL'.1 hL'.2
  · exact (LocalPerm.sandboxSubset_subset _ _ hL').2

theorem rc_comp_atomPerm {γ : Iio α} {φ : StructAction β} {hφ : φ.Lawful}
    (A : Path (β : TypeIndex) γ) (B : ExtendedIndex γ) :
    ((φ.comp A).rc (hφ.comp A) B).atomPerm = (φ.rc hφ (A.comp B)).atomPerm :=
  by
  unfold rc refine complete near_litter_action.refine near_litter_action.complete
  simp_rw [struct_action.comp_apply]

theorem rc_comp_smul_atom {γ : Iio α} {φ : StructAction β} {hφ : φ.Lawful}
    (A : Path (β : TypeIndex) γ) (B : ExtendedIndex γ) (a : Atom) :
    (φ.comp A).rc (hφ.comp A) B • a = φ.rc hφ (A.comp B) • a :=
  by
  change near_litter_approx.atom_perm _ _ = near_litter_approx.atom_perm _ _
  rw [rc_comp_atom_perm]

end StructAction

end ConNf
