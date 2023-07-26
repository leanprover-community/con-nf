import phase2.flexible
import phase2.struct_action
import phase2.fill_atom_range
import phase2.fill_atom_orbits

open quiver set

universe u

namespace con_nf
variables [params.{u}]

/-!
# Refinements of actions
-/

namespace near_litter_action

variables (φ : near_litter_action) (hφ : φ.lawful)

noncomputable def refine (hφ : φ.lawful) : near_litter_action :=
φ.fill_atom_range.fill_atom_orbits (φ.fill_atom_range_lawful hφ)

variables {φ} {hφ}

lemma refine_lawful : (φ.refine hφ).lawful :=
fill_atom_orbits_lawful _ _ (fill_atom_range_symm_diff_subset_ran hφ)

@[simp] lemma refine_atom_map {a : atom} (ha : (φ.atom_map a).dom) :
  (φ.refine hφ).atom_map a = φ.atom_map a :=
begin
  unfold refine,
  refine part.ext' _ _,
  { simp only [ha, fill_atom_orbits_atom_map, orbit_atom_map_dom_iff, fill_atom_range_atom_map,
      iff_true],
    exact or.inl (or.inl ha), },
  intros h₁ h₂,
  refine (φ.fill_atom_range.orbit_atom_map_eq_of_mem_dom _ _ (or.inl ha)).trans _,
  exact φ.supported_action_eq_of_dom ha,
end

@[simp] lemma refine_atom_map_get {a : atom} (ha : (φ.atom_map a).dom) :
  ((φ.refine hφ).atom_map a).get (or.inl (or.inl ha)) = (φ.atom_map a).get ha :=
by simp only [refine_atom_map ha]

@[simp] lemma refine_litter_map : (φ.refine hφ).litter_map = φ.litter_map := rfl

lemma refine_precise : precise (φ.refine hφ) :=
fill_atom_orbits_precise _ (fill_atom_range_symm_diff_subset_ran hφ)

end near_litter_action

namespace struct_action

variables {β : type_index} (φ : struct_action β) (hφ : φ.lawful)

noncomputable def refine : struct_action β := λ A, (φ A).refine (hφ A)

variables {φ} {hφ}

lemma refine_lawful : (φ.refine hφ).lawful := λ A, near_litter_action.refine_lawful

@[simp] lemma refine_apply {A : extended_index β} :
  φ.refine hφ A = (φ A).refine (hφ A) := rfl

lemma refine_atom_map {A : extended_index β} {a : atom} (ha : ((φ A).atom_map a).dom) :
  ((φ A).refine (hφ A)).atom_map a = (φ A).atom_map a := near_litter_action.refine_atom_map ha

@[simp] lemma refine_atom_map_get {A : extended_index β} {a : atom} (ha : ((φ A).atom_map a).dom) :
  (((φ A).refine (hφ A)).atom_map a).get (or.inl (or.inl ha)) = ((φ A).atom_map a).get ha :=
near_litter_action.refine_atom_map_get ha

@[simp] lemma refine_litter_map {A : extended_index β} :
  ((φ A).refine (hφ A)).litter_map = (φ A).litter_map := rfl

lemma refine_precise : precise (φ.refine hφ) :=
λ A, near_litter_action.refine_precise

lemma refine_supports {α : Λ} [position_data.{}] [phase_2_assumptions α] {β : Iio α}
  {t : tangle β} (φ : struct_action β) (hφ : φ.lawful) (h : φ.supports t) :
  (φ.refine hφ).supports t := {
  atom_mem := λ a B ha, or.inl (or.inl $ h.atom_mem a B ha),
  litter_mem := h.litter_mem,
}

end struct_action

namespace struct_action

variables {α : Λ} [position_data.{}] [phase_2_assumptions α] {β : Iio α}

/-- Refine and complete this action into a structural approximation. -/
noncomputable def rc (φ : struct_action β) (h : φ.lawful) : struct_approx β :=
(φ.refine h).complete refine_lawful

lemma rc_smul_atom_eq {φ : struct_action β} {h : φ.lawful} {B : extended_index β}
  {a : atom} (ha : ((φ B).atom_map a).dom) :
  φ.rc h B • a = ((φ B).atom_map a).get ha :=
begin
  refine (near_litter_action.complete_smul_atom_eq _ _).trans _,
  { exact or.inl (or.inl ha), },
  { simp only [refine_apply, refine_atom_map ha], },
end

lemma rc_smul_litter_eq {φ : struct_action β} {hφ : φ.lawful}
  {B : extended_index β} (L : litter) :
  φ.rc hφ B • L = (φ.refine hφ B).flexible_litter_perm (refine_lawful B) B L := rfl

lemma rc_free (φ : struct_action β) (h₁ : φ.lawful) (h₂ : φ.map_flexible) :
  (show struct_approx (β : Iic α), from φ.rc h₁).free :=
begin
  rintros B L' ((hL' | ⟨L', hL', rfl⟩) | hL'),
  { exact hL'.2, },
  { rw near_litter_action.rough_litter_map_or_else_of_dom _ hL'.1,
    exact h₂ L' B hL'.1 hL'.2, },
  { exact (local_perm.sandbox_subset_subset _ _ hL').2, },
end

end struct_action

end con_nf
