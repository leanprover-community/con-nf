import phase2.fill_atom_range
import phase2.fill_atom_orbits

universe u

namespace con_nf
variables [params.{u}]

/-!
# Refinements of weak approximations
-/

namespace weak_near_litter_approx

variables (w : weak_near_litter_approx)

noncomputable def refine : weak_near_litter_approx :=
w.fill_atom_range.fill_atom_orbits fill_atom_range_symm_diff_subset_ran

variable {w}

@[simp] lemma refine_atom_map {a : atom} (ha : (w.atom_map a).dom) :
  w.refine.atom_map a = w.atom_map a :=
begin
  unfold refine,
  refine part.ext' _ _,
  { simp only [ha, fill_atom_orbits_atom_map, orbit_atom_map_dom_iff, fill_atom_range_atom_map,
      iff_true],
    exact or.inl (or.inl ha), },
  intros h₁ h₂,
  refine (w.fill_atom_range.orbit_atom_map_eq_of_mem_dom _ (or.inl ha)).trans _,
  exact w.supported_action_eq_of_dom ha,
end

@[simp] lemma refine_atom_map_get {a : atom} (ha : (w.atom_map a).dom) :
  (w.refine.atom_map a).get (or.inl (or.inl ha)) = (w.atom_map a).get ha :=
by simp only [refine_atom_map ha]

@[simp] lemma refine_litter_map : w.refine.litter_map = w.litter_map := rfl

lemma refine_precise : precise w.refine :=
fill_atom_orbits_precise fill_atom_range_symm_diff_subset_ran

end weak_near_litter_approx

namespace weak_struct_approx

variables {β : type_index} (w : weak_struct_approx β)

noncomputable def refine : weak_struct_approx β := λ A, (w A).refine

@[simp] lemma refine_apply {A : extended_index β} :
  w.refine A = (w A).refine := rfl

@[simp] lemma refine_atom_map {A : extended_index β} {a : atom} (ha : ((w A).atom_map a).dom) :
  (w A).refine.atom_map a = (w A).atom_map a := weak_near_litter_approx.refine_atom_map ha

@[simp] lemma refine_atom_map_get {A : extended_index β} {a : atom} (ha : ((w A).atom_map a).dom) :
  ((w A).refine.atom_map a).get (or.inl (or.inl ha)) = ((w A).atom_map a).get ha :=
weak_near_litter_approx.refine_atom_map_get ha

@[simp] lemma refine_litter_map {A : extended_index β} :
  (w A).refine.litter_map = (w A).litter_map := rfl

lemma refine_precise : precise w.refine :=
λ A, weak_near_litter_approx.refine_precise

end weak_struct_approx

end con_nf
