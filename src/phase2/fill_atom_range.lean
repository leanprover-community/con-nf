import phase2.near_litter_action

open cardinal quiver set sum with_bot
open_locale cardinal classical pointwise

universe u

namespace con_nf
variables [params.{u}]

/-!
# Filling in ranges of near litter actions
TODO: Rename the gadgetry created in this file.
-/

namespace near_litter_action

variables (φ : near_litter_action)

noncomputable def preimage_litter : litter :=
φ.not_banned_litter_nonempty.some

lemma preimage_litter_not_banned : ¬φ.banned_litter φ.preimage_litter :=
φ.not_banned_litter_nonempty.some.prop

/-- An atom is called *without preimage* if it is not in the range of the approximation,
but it is in a litter near some near-litter in the range.
Atoms without preimage need to have something map to it, so that the resulting map that we use in
the freedom of action theorem actually maps to the correct near-litter. -/
@[mk_iff] structure without_preimage (a : atom) : Prop :=
(mem_map : ∃ (L : litter) (hL : (φ.litter_map L).dom), a ∈ litter_set ((φ.litter_map L).get hL).1)
(not_mem_map : ∀ (L : litter) (hL : (φ.litter_map L).dom), a ∉ (φ.litter_map L).get hL)
(not_mem_ran : a ∉ φ.atom_map.ran)

lemma without_preimage_small :
  small {a | φ.without_preimage a} :=
begin
  simp only [without_preimage_iff, set_of_and],
  rw ← inter_assoc,
  refine small.mono (inter_subset_left _ _) _,
  suffices : small ⋃ (L : litter) (hL),
    litter_set ((φ.litter_map L).get hL).1 \ (φ.litter_map L).get hL,
  { refine small.mono _ this,
    rintro a ⟨⟨L, hL, ha₁⟩, ha₂⟩,
    simp only [mem_Union],
    exact ⟨L, hL, ha₁, ha₂ _ _⟩, },
  refine small.bUnion _ _,
  { refine lt_of_le_of_lt _ φ.litter_map_dom_small,
    refine ⟨⟨λ L, ⟨_, L.prop⟩, _⟩⟩,
    intros L₁ L₂ h,
    simp only [subtype.mk_eq_mk, prod.mk.inj_iff, eq_self_iff_true, and_true,
      litter.to_near_litter_injective.eq_iff, subtype.coe_inj] at h,
    exact h, },
  { intros L hL,
    refine small.mono _ ((φ.litter_map L).get hL).2.prop,
    exact λ x hx, or.inl hx, },
end

/-- The subset of the preimage litter that is put in correspondence with the set of
atoms without preimage. -/
def preimage_litter_subset : set atom :=
(le_mk_iff_exists_subset.mp
  (lt_of_lt_of_eq φ.without_preimage_small (mk_litter_set φ.preimage_litter).symm).le).some

lemma preimage_litter_subset_spec :
  φ.preimage_litter_subset ⊆ litter_set φ.preimage_litter ∧
    #φ.preimage_litter_subset = #{a : atom | φ.without_preimage a} :=
(le_mk_iff_exists_subset.mp
  (lt_of_lt_of_eq φ.without_preimage_small (mk_litter_set φ.preimage_litter).symm).le).some_spec

lemma preimage_litter_subset_subset :
  φ.preimage_litter_subset ⊆ litter_set φ.preimage_litter :=
φ.preimage_litter_subset_spec.1

lemma preimage_litter_subset_small :
  small (φ.preimage_litter_subset) :=
lt_of_eq_of_lt φ.preimage_litter_subset_spec.2 φ.without_preimage_small

@[irreducible] noncomputable def preimage_litter_equiv :
  φ.preimage_litter_subset ≃ {a : atom | φ.without_preimage a} :=
(cardinal.eq.mp φ.preimage_litter_subset_spec.2).some

/-- The images of atoms in a litter `L` that were mapped outside the target litter, but
were not in the domain. -/
@[mk_iff] structure mapped_outside (L : litter) (hL : (φ.litter_map L).dom) (a : atom) : Prop :=
(mem_map : a ∈ (φ.litter_map L).get hL)
(not_mem_map : a ∉ litter_set ((φ.litter_map L).get hL).1)
(not_mem_ran : a ∉ φ.atom_map.ran)

/-- There are only `< κ`-many atoms in a litter `L` that are mapped outside the image litter,
and that are not already in the domain. -/
lemma mapped_outside_small (L : litter) (hL : (φ.litter_map L).dom) :
  small {a | φ.mapped_outside L hL a} :=
begin
  simp only [mapped_outside_iff, set_of_and],
  rw ← inter_assoc,
  refine small.mono (inter_subset_left _ _) _,
  refine small.mono _ ((φ.litter_map L).get hL).2.prop,
  exact λ x hx, or.inr hx,
end

lemma without_preimage.not_mapped_outside {a : atom} (ha : φ.without_preimage a)
  (L : litter) (hL : (φ.litter_map L).dom) : ¬φ.mapped_outside L hL a :=
λ ha', ha.not_mem_map L hL ha'.mem_map

lemma mapped_outside.not_without_preimage {a : atom} {L : litter} {hL : (φ.litter_map L).dom}
  (ha : φ.mapped_outside L hL a) : ¬φ.without_preimage a :=
λ ha', ha'.not_mem_map L hL ha.mem_map

/-- The amount of atoms in a litter that are not in the domain already is `κ`. -/
lemma mk_mapped_outside_domain (L : litter) : #(litter_set L \ φ.atom_map.dom : set atom) = #κ :=
begin
  refine le_antisymm _ _,
  { rw ← mk_litter_set,
    exact mk_subtype_mono (λ x hx, hx.1), },
  by_contra' h,
  have := small.union h φ.atom_map_dom_small,
  rw diff_union_self at this,
  exact (mk_litter_set L).not_lt (small.mono (subset_union_left _ _) this),
end

/-- To each litter we associate a subset which is to contain the atoms mapped outside it. -/
def mapped_outside_subset (L : litter) (hL : (φ.litter_map L).dom) : set atom :=
(le_mk_iff_exists_subset.mp
  (lt_of_lt_of_eq (φ.mapped_outside_small L hL) (φ.mk_mapped_outside_domain L).symm).le).some

lemma mapped_outside_subset_spec (L : litter) (hL : (φ.litter_map L).dom) :
  φ.mapped_outside_subset L hL ⊆ litter_set L \ φ.atom_map.dom ∧
    #(φ.mapped_outside_subset L hL) = #{a : atom | φ.mapped_outside L hL a} :=
(le_mk_iff_exists_subset.mp
  (lt_of_lt_of_eq (φ.mapped_outside_small L hL) (φ.mk_mapped_outside_domain L).symm).le).some_spec

lemma mapped_outside_subset_subset (L : litter) (hL : (φ.litter_map L).dom) :
  φ.mapped_outside_subset L hL ⊆ litter_set L :=
λ x hx, ((φ.mapped_outside_subset_spec L hL).1 hx).1

lemma mapped_outside_subset_closure (L : litter) (hL : (φ.litter_map L).dom) :
  φ.mapped_outside_subset L hL ⊆ φ.atom_map.domᶜ :=
λ x hx, ((φ.mapped_outside_subset_spec L hL).1 hx).2

lemma mapped_outside_subset_small (L : litter) (hL : (φ.litter_map L).dom) :
  small (φ.mapped_outside_subset L hL) :=
lt_of_eq_of_lt (φ.mapped_outside_subset_spec L hL).2 (φ.mapped_outside_small L hL)

/-- A correspondence between the "mapped outside" subset of `L` and its atoms which were mapped
outside the target litter. We will use this equivalence to construct an approximation to
use in the freedom of action theorem. -/
@[irreducible] noncomputable def mapped_outside_equiv (L : litter) (hL : (φ.litter_map L).dom) :
  φ.mapped_outside_subset L hL ≃ {a : atom | φ.mapped_outside L hL a} :=
(cardinal.eq.mp (φ.mapped_outside_subset_spec L hL).2).some

noncomputable def supported_action_atom_map_core : atom →. atom :=
λ a, {
  dom := (φ.atom_map a).dom ∨ a ∈ φ.preimage_litter_subset ∨
    ∃ L hL, a ∈ φ.mapped_outside_subset L hL,
  get := λ h, h.elim' (φ.atom_map a).get
    (λ h, h.elim'
      (λ h, φ.preimage_litter_equiv ⟨a, h⟩)
      (λ h, φ.mapped_outside_equiv h.some h.some_spec.some ⟨a, h.some_spec.some_spec⟩)),
}

lemma mem_supported_action_atom_map_core_dom_iff (a : atom) :
  (φ.supported_action_atom_map_core a).dom ↔
  a ∈ φ.atom_map.dom ∪ φ.preimage_litter_subset ∪ ⋃ L hL, φ.mapped_outside_subset L hL :=
begin
  rw supported_action_atom_map_core,
  simp only [pfun.dom_mk, mem_set_of_eq, mem_union, mem_Union],
  rw or_assoc,
  refl,
end

lemma supported_action_atom_map_core_dom_eq :
  φ.supported_action_atom_map_core.dom =
  φ.atom_map.dom ∪ φ.preimage_litter_subset ∪ ⋃ L hL, φ.mapped_outside_subset L hL :=
begin
  ext a : 1,
  exact φ.mem_supported_action_atom_map_core_dom_iff a,
end

lemma supported_action_atom_map_core_dom_small :
  small φ.supported_action_atom_map_core.dom :=
begin
  rw supported_action_atom_map_core_dom_eq,
  refine small.union (small.union φ.atom_map_dom_small _) _,
  { exact φ.preimage_litter_subset_small, },
  { refine small.bUnion _ _,
    { refine lt_of_le_of_lt _ φ.litter_map_dom_small,
      refine ⟨⟨λ L, ⟨_, L.prop⟩, λ L₁ L₂ h, _⟩⟩,
      simp only [subtype.mk_eq_mk, prod.mk.inj_iff, eq_self_iff_true, and_true,
        litter.to_near_litter_injective.eq_iff, subtype.coe_inj] at h,
      exact h, },
    { intros L hL,
      exact φ.mapped_outside_subset_small L hL, }, },
end

lemma mk_supported_action_atom_map_dom :
  #(φ.supported_action_atom_map_core.dom ∆
    ((λ a, part.get_or_else (φ.supported_action_atom_map_core a) (arbitrary atom)) ''
      φ.supported_action_atom_map_core.dom) : set atom) ≤
  #(litter_set $ φ.preimage_litter) :=
begin
  rw mk_litter_set,
  refine le_trans (mk_subtype_mono symm_diff_subset_union) (le_trans (mk_union_le _ _) _),
  refine add_le_of_le κ_regular.aleph_0_le _ _,
  exact le_of_lt φ.supported_action_atom_map_core_dom_small,
  exact le_trans mk_image_le (le_of_lt φ.supported_action_atom_map_core_dom_small),
end

lemma supported_action_eq_of_dom {a : atom} (ha : (φ.atom_map a).dom) :
  (φ.supported_action_atom_map_core a).get (or.inl ha) = (φ.atom_map a).get ha :=
begin
  simp only [supported_action_atom_map_core],
  rw or.elim'_left,
end

lemma supported_action_eq_of_mem_preimage_litter_subset {a : atom}
  (ha : a ∈ φ.preimage_litter_subset) :
  (φ.supported_action_atom_map_core a).get (or.inr (or.inl ha)) = φ.preimage_litter_equiv ⟨a, ha⟩ :=
begin
  simp only [supported_action_atom_map_core],
  rw [or.elim'_right, or.elim'_left],
  intro h',
  have := φ.preimage_litter_not_banned,
  rw banned_litter_iff at this,
  push_neg at this,
  exact this.1 a h' (φ.preimage_litter_subset_subset ha).symm,
end

lemma supported_action_eq_of_mem_mapped_outside_subset {a : atom}
  {L hL} (ha : a ∈ φ.mapped_outside_subset L hL) :
  (φ.supported_action_atom_map_core a).get (or.inr (or.inr ⟨L, hL, ha⟩)) =
  φ.mapped_outside_equiv L hL ⟨a, ha⟩ :=
begin
  have : ∃ L hL, a ∈ φ.mapped_outside_subset L hL := ⟨L, hL, ha⟩,
  simp only [supported_action_atom_map_core],
  rw [or.elim'_right, or.elim'_right],
  { cases eq_of_mem_litter_set_of_mem_litter_set
      (φ.mapped_outside_subset_subset _ hL ha)
      (φ.mapped_outside_subset_subset _ this.some_spec.some this.some_spec.some_spec),
    refl, },
  { intro h,
    have := eq_of_mem_litter_set_of_mem_litter_set
      (φ.mapped_outside_subset_subset _ hL ha)
      (φ.preimage_litter_subset_subset h),
    cases this,
    have := φ.preimage_litter_not_banned,
    rw banned_litter_iff at this,
    push_neg at this,
    cases this.2.1 hL, },
  { exact ((mapped_outside_subset_spec _ _ hL).1 ha).2, },
end

lemma supported_action_atom_map_core_injective ⦃a b : atom⦄ (hφ : φ.lawful)
  (ha : (supported_action_atom_map_core φ a).dom) (hb : (supported_action_atom_map_core φ b).dom)
  (hab : (φ.supported_action_atom_map_core a).get ha =
    (φ.supported_action_atom_map_core b).get hb) :
  a = b :=
begin
  obtain (ha | ha | ⟨L, hL, ha⟩) := ha;
  obtain (hb | hb | ⟨L', hL', hb⟩) := hb,
  { have := (supported_action_eq_of_dom _ ha).symm.trans
      (hab.trans (supported_action_eq_of_dom _ hb)),
    exact hφ.atom_map_injective ha hb this, },
  { have := (supported_action_eq_of_dom _ ha).symm.trans
      (hab.trans (supported_action_eq_of_mem_preimage_litter_subset _ hb)),
    obtain ⟨hab, -⟩ := subtype.coe_eq_iff.mp this.symm,
    cases hab.not_mem_ran ⟨a, ha, rfl⟩, },
  { have := (supported_action_eq_of_dom _ ha).symm.trans
      (hab.trans (supported_action_eq_of_mem_mapped_outside_subset _ hb)),
    obtain ⟨hab, -⟩ := subtype.coe_eq_iff.mp this.symm,
    cases hab.not_mem_ran ⟨a, ha, rfl⟩, },
  { have := (supported_action_eq_of_mem_preimage_litter_subset _ ha).symm.trans
      (hab.trans (supported_action_eq_of_dom _ hb)),
    obtain ⟨hab, -⟩ := subtype.coe_eq_iff.mp this,
    cases hab.not_mem_ran ⟨b, hb, rfl⟩, },
  { have := (supported_action_eq_of_mem_preimage_litter_subset _ ha).symm.trans
      (hab.trans (supported_action_eq_of_mem_preimage_litter_subset _ hb)),
    rw [subtype.coe_inj, embedding_like.apply_eq_iff_eq] at this,
    exact subtype.coe_inj.mpr this, },
  { have := (supported_action_eq_of_mem_preimage_litter_subset _ ha).symm.trans
      (hab.trans (supported_action_eq_of_mem_mapped_outside_subset _ hb)),
    obtain ⟨hab, -⟩ := subtype.coe_eq_iff.mp this,
    cases without_preimage.not_mapped_outside φ hab _ hL'
      (φ.mapped_outside_equiv L' hL' ⟨b, hb⟩).prop, },
  { have := (supported_action_eq_of_mem_mapped_outside_subset _ ha).symm.trans
      (hab.trans (supported_action_eq_of_dom _ hb)),
    obtain ⟨hab, -⟩ := subtype.coe_eq_iff.mp this,
    cases hab.not_mem_ran ⟨b, hb, rfl⟩, },
  { have := (supported_action_eq_of_mem_mapped_outside_subset _ ha).symm.trans
      (hab.trans (supported_action_eq_of_mem_preimage_litter_subset _ hb)),
    obtain ⟨hab, -⟩ := subtype.coe_eq_iff.mp this.symm,
    cases without_preimage.not_mapped_outside φ hab _ hL
      (φ.mapped_outside_equiv L hL ⟨a, ha⟩).prop, },
  { have := (supported_action_eq_of_mem_mapped_outside_subset _ ha).symm.trans
      (hab.trans (supported_action_eq_of_mem_mapped_outside_subset _ hb)),
    cases hφ.litter_map_injective hL hL' _,
    { simp only [subtype.coe_inj, embedding_like.apply_eq_iff_eq] at this,
      exact this, },
    obtain ⟨hab, -⟩ := subtype.coe_eq_iff.mp this,
    exact ⟨_, hab.1, (φ.mapped_outside_equiv L' hL' ⟨b, hb⟩).prop.1⟩, },
end

lemma supported_action_atom_map_core_mem (hφ : φ.lawful)
  (a : atom) (ha : (φ.supported_action_atom_map_core a).dom)
  (L : litter) (hL : (φ.litter_map L).dom) :
  a.fst = L ↔ (φ.supported_action_atom_map_core a).get ha ∈ (φ.litter_map L).get hL :=
begin
  obtain (ha | ha | ⟨L', hL', ha⟩) := ha,
  { rw [hφ.atom_mem a ha L hL, supported_action_eq_of_dom], },
  { rw supported_action_eq_of_mem_preimage_litter_subset,
    split,
    { rintro rfl,
      have := φ.preimage_litter_subset_subset ha,
      rw mem_litter_set at this,
      rw this at hL,
      have := banned_litter.litter_dom _ hL,
      cases φ.preimage_litter_not_banned this, },
    { intro h,
      cases (φ.preimage_litter_equiv ⟨a, ha⟩).prop.not_mem_map L hL h, }, },
  { cases φ.mapped_outside_subset_subset L' hL' ha,
    rw supported_action_eq_of_mem_mapped_outside_subset,
    split,
    { rintro rfl,
      exact (φ.mapped_outside_equiv _ _ _ ).prop.mem_map, },
    { intro h,
      refine hφ.litter_map_injective hL' hL ⟨_, _, h⟩,
      exact (φ.mapped_outside_equiv _ _ _ ).prop.mem_map, }, },
end

noncomputable def fill_atom_range : near_litter_action := {
  atom_map := φ.supported_action_atom_map_core,
  litter_map := φ.litter_map,
  atom_map_dom_small := φ.supported_action_atom_map_core_dom_small,
  litter_map_dom_small := φ.litter_map_dom_small,
}

lemma fill_atom_range_lawful (hφ : φ.lawful) : φ.fill_atom_range.lawful := {
  atom_map_injective := λ a b, φ.supported_action_atom_map_core_injective hφ,
  litter_map_injective := hφ.litter_map_injective,
  atom_mem := φ.supported_action_atom_map_core_mem hφ,
}

variable {φ}

@[simp] lemma fill_atom_range_atom_map :
  φ.fill_atom_range.atom_map = φ.supported_action_atom_map_core := rfl

@[simp] lemma fill_atom_range_litter_map :
  φ.fill_atom_range.litter_map = φ.litter_map := rfl

lemma subset_supported_action_atom_map_core_dom :
  φ.atom_map.dom ⊆ φ.supported_action_atom_map_core.dom :=
subset_union_left _ _

lemma subset_supported_action_atom_map_core_ran :
  φ.atom_map.ran ⊆ φ.supported_action_atom_map_core.ran :=
begin
  rintro _ ⟨a, ha, rfl⟩,
  exact ⟨a, subset_supported_action_atom_map_core_dom ha, φ.supported_action_eq_of_dom _⟩,
end

lemma fill_atom_range_symm_diff_subset_ran (hφ : φ.lawful)
  (L : litter) (hL : (φ.fill_atom_range.litter_map L).dom) :
  ((φ.fill_atom_range.litter_map L).get hL : set atom) ∆ litter_set
    ((φ.fill_atom_range.litter_map L).get hL).fst ⊆ φ.fill_atom_range.atom_map.ran :=
begin
  rintro a,
  by_cases ha₁ : a ∈ φ.atom_map.ran,
  { obtain ⟨b, hb, rfl⟩ := ha₁,
    exact λ _, ⟨b, or.inl hb, φ.supported_action_eq_of_dom hb⟩, },
  rintro (⟨ha₂, ha₃⟩ | ⟨ha₂, ha₃⟩),
  { refine ⟨(φ.mapped_outside_equiv L hL).symm ⟨a, ha₂, ha₃, ha₁⟩, _, _⟩,
    { exact or.inr (or.inr ⟨L, hL, ((φ.mapped_outside_equiv L hL).symm _).prop⟩), },
    { simp only [fill_atom_range_atom_map],
      refine (φ.supported_action_eq_of_mem_mapped_outside_subset
        ((φ.mapped_outside_equiv L hL).symm _).prop).trans _,
      simp only [subtype.coe_eta, equiv.apply_symm_apply, subtype.coe_mk], }, },
  { by_cases ha₄ : ∀ (L' : litter) (hL' : (φ.litter_map L').dom), a ∉ (φ.litter_map L').get hL',
    { refine ⟨φ.preimage_litter_equiv.symm ⟨a, ⟨L, hL, ha₂⟩, ha₄, ha₁⟩, _, _⟩,
      { exact or.inr (or.inl (φ.preimage_litter_equiv.symm _).prop), },
      { simp only [fill_atom_range_atom_map],
        refine (φ.supported_action_eq_of_mem_preimage_litter_subset
          (φ.preimage_litter_equiv.symm _).prop).trans _,
        simp only [subtype.coe_eta, equiv.apply_symm_apply, subtype.coe_mk], }, },
    { push_neg at ha₄,
      obtain ⟨L', hL', ha₄⟩ := ha₄,
      refine ⟨(φ.mapped_outside_equiv L' hL').symm ⟨a, ha₄, _, ha₁⟩, _, _⟩,
      { intro ha,
        have := near_litter.inter_nonempty_of_fst_eq_fst
          (eq_of_mem_litter_set_of_mem_litter_set ha₂ ha),
        cases hφ.litter_map_injective hL hL' this,
        exact ha₃ ha₄, },
      { exact or.inr (or.inr ⟨L', hL', ((φ.mapped_outside_equiv L' hL').symm _).prop⟩), },
      { simp only [fill_atom_range_atom_map],
        refine (φ.supported_action_eq_of_mem_mapped_outside_subset
          ((φ.mapped_outside_equiv L' hL').symm _).prop).trans _,
        simp only [subtype.coe_eta, equiv.apply_symm_apply, subtype.coe_mk], }, }, },
end

end near_litter_action

end con_nf
