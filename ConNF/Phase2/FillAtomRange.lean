import ConNF.Phase2.NearLitterAction

#align_import phase2.fill_atom_range

open Cardinal Quiver Set Sum WithBot

open scoped Cardinal Classical Pointwise

universe u

namespace ConNF

variable [Params.{u}]

/-!
# Filling in ranges of near litter actions
TODO: Rename the gadgetry created in this file.
-/


namespace NearLitterAction

variable (φ : NearLitterAction)

noncomputable def preimageLitter : Litter :=
  φ.not_bannedLitter_nonempty.some

theorem preimageLitter_not_banned : ¬φ.BannedLitter φ.preimageLitter :=
  φ.not_bannedLitter_nonempty.some.prop

/-- An atom is called *without preimage* if it is not in the range of the approximation,
but it is in a litter near some near-litter in the range.
Atoms without preimage need to have something map to it, so that the resulting map that we use in
the freedom of action theorem actually maps to the correct near-litter. -/
@[mk_iff]
structure WithoutPreimage (a : Atom) : Prop where
  mem_map : ∃ (L : Litter) (hL : (φ.litterMap L).Dom), a ∈ litterSet ((φ.litterMap L).get hL).1
  not_mem_map : ∀ (L : Litter) (hL : (φ.litterMap L).Dom), a ∉ (φ.litterMap L).get hL
  not_mem_ran : a ∉ φ.atomMap.ran

theorem withoutPreimage_small : Small {a | φ.WithoutPreimage a} :=
  by
  simp only [without_preimage_iff, set_of_and]
  rw [← inter_assoc]
  refine' small.mono (inter_subset_left _ _) _
  suffices
    Small (⋃ (L : litter) (hL), litter_set ((φ.litter_map L).get hL).1 \ (φ.litter_map L).get hL)
    by
    refine' small.mono _ this
    rintro a ⟨⟨L, hL, ha₁⟩, ha₂⟩
    simp only [mem_Union]
    exact ⟨L, hL, ha₁, ha₂ _ _⟩
  refine' small.bUnion _ _
  · refine' lt_of_le_of_lt _ φ.litter_map_dom_small
    refine' ⟨⟨fun L => ⟨_, L.prop⟩, _⟩⟩
    intro L₁ L₂ h
    simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff, eq_self_iff_true, and_true_iff,
      litter.to_near_litter_injective.eq_iff, Subtype.coe_inj] at h
    exact h
  · intro L hL
    refine' small.mono _ ((φ.litter_map L).get hL).2.prop
    exact fun x hx => Or.inl hx

/-- The subset of the preimage litter that is put in correspondence with the set of
atoms without preimage. -/
def preimageLitterSubset : Set Atom :=
  (le_mk_iff_exists_subset.mp
      (lt_of_lt_of_eq φ.withoutPreimage_small (mk_litterSet φ.preimageLitter).symm).le).some

theorem preimageLitterSubset_spec :
    φ.preimageLitterSubset ⊆ litterSet φ.preimageLitter ∧
      (#φ.preimageLitterSubset) = (#{a : Atom | φ.WithoutPreimage a}) :=
  (le_mk_iff_exists_subset.mp
      (lt_of_lt_of_eq φ.withoutPreimage_small (mk_litterSet φ.preimageLitter).symm).le).choose_spec

theorem preimageLitterSubset_subset : φ.preimageLitterSubset ⊆ litterSet φ.preimageLitter :=
  φ.preimageLitterSubset_spec.1

theorem preimageLitterSubset_small : Small φ.preimageLitterSubset :=
  lt_of_eq_of_lt φ.preimageLitterSubset_spec.2 φ.withoutPreimage_small

noncomputable irreducible_def preimageLitterEquiv :
    φ.preimageLitterSubset ≃ {a : Atom | φ.WithoutPreimage a} :=
  (Cardinal.eq.mp φ.preimageLitterSubset_spec.2).some

/-- The images of atoms in a litter `L` that were mapped outside the target litter, but
were not in the domain. -/
@[mk_iff]
structure MappedOutside (L : Litter) (hL : (φ.litterMap L).Dom) (a : Atom) : Prop where
  mem_map : a ∈ (φ.litterMap L).get hL
  not_mem_map : a ∉ litterSet ((φ.litterMap L).get hL).1
  not_mem_ran : a ∉ φ.atomMap.ran

/-- There are only `< κ`-many atoms in a litter `L` that are mapped outside the image litter,
and that are not already in the domain. -/
theorem mappedOutside_small (L : Litter) (hL : (φ.litterMap L).Dom) :
    Small {a | φ.MappedOutside L hL a} :=
  by
  simp only [mapped_outside_iff, set_of_and]
  rw [← inter_assoc]
  refine' small.mono (inter_subset_left _ _) _
  refine' small.mono _ ((φ.litter_map L).get hL).2.prop
  exact fun x hx => Or.inr hx

theorem WithoutPreimage.not_mappedOutside {a : Atom} (ha : φ.WithoutPreimage a) (L : Litter)
    (hL : (φ.litterMap L).Dom) : ¬φ.MappedOutside L hL a := fun ha' =>
  ha.not_mem_map L hL ha'.mem_map

theorem MappedOutside.not_withoutPreimage {a : Atom} {L : Litter} {hL : (φ.litterMap L).Dom}
    (ha : φ.MappedOutside L hL a) : ¬φ.WithoutPreimage a := fun ha' =>
  ha'.not_mem_map L hL ha.mem_map

/-- The amount of atoms in a litter that are not in the domain already is `κ`. -/
theorem mk_mapped_outside_domain (L : Litter) :
    (#(litterSet L \ φ.atomMap.Dom : Set Atom)) = (#κ) :=
  by
  refine' le_antisymm _ _
  · rw [← mk_litter_set]
    exact mk_subtype_mono fun x hx => hx.1
  by_contra' h
  have := small.union h φ.atom_map_dom_small
  rw [diff_union_self] at this
  exact (mk_litter_set L).not_lt (small.mono (subset_union_left _ _) this)

/-- To each litter we associate a subset which is to contain the atoms mapped outside it. -/
def mappedOutsideSubset (L : Litter) (hL : (φ.litterMap L).Dom) : Set Atom :=
  (le_mk_iff_exists_subset.mp
      (lt_of_lt_of_eq (φ.mappedOutside_small L hL) (φ.mk_mapped_outside_domain L).symm).le).some

theorem mappedOutsideSubset_spec (L : Litter) (hL : (φ.litterMap L).Dom) :
    φ.mappedOutsideSubset L hL ⊆ litterSet L \ φ.atomMap.Dom ∧
      (#φ.mappedOutsideSubset L hL) = (#{a : Atom | φ.MappedOutside L hL a}) :=
  (le_mk_iff_exists_subset.mp
      (lt_of_lt_of_eq (φ.mappedOutside_small L hL)
          (φ.mk_mapped_outside_domain L).symm).le).choose_spec

theorem mappedOutsideSubset_subset (L : Litter) (hL : (φ.litterMap L).Dom) :
    φ.mappedOutsideSubset L hL ⊆ litterSet L := fun x hx =>
  ((φ.mappedOutsideSubset_spec L hL).1 hx).1

theorem mappedOutsideSubset_closure (L : Litter) (hL : (φ.litterMap L).Dom) :
    φ.mappedOutsideSubset L hL ⊆ φ.atomMap.Domᶜ := fun x hx =>
  ((φ.mappedOutsideSubset_spec L hL).1 hx).2

theorem mappedOutsideSubset_small (L : Litter) (hL : (φ.litterMap L).Dom) :
    Small (φ.mappedOutsideSubset L hL) :=
  lt_of_eq_of_lt (φ.mappedOutsideSubset_spec L hL).2 (φ.mappedOutside_small L hL)

/-- A correspondence between the "mapped outside" subset of `L` and its atoms which were mapped
outside the target litter. We will use this equivalence to construct an approximation to
use in the freedom of action theorem. -/
noncomputable irreducible_def mappedOutsideEquiv (L : Litter) (hL : (φ.litterMap L).Dom) :
    φ.mappedOutsideSubset L hL ≃ {a : Atom | φ.MappedOutside L hL a} :=
  (Cardinal.eq.mp (φ.mappedOutsideSubset_spec L hL).2).some

noncomputable def supportedActionAtomMapCore : Atom →. Atom := fun a =>
  { Dom := (φ.atomMap a).Dom ∨ a ∈ φ.preimageLitterSubset ∨ ∃ L hL, a ∈ φ.mappedOutsideSubset L hL
    get := fun h =>
      h.elim' (φ.atomMap a).get fun h =>
        h.elim' (fun h => φ.preimageLitterEquiv ⟨a, h⟩) fun h =>
          φ.mappedOutsideEquiv h.some h.choose_spec.some ⟨a, h.choose_spec.choose_spec⟩ }

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (L hL) -/
theorem mem_supportedActionAtomMapCore_dom_iff (a : Atom) :
    (φ.supportedActionAtomMapCore a).Dom ↔
      a ∈ φ.atomMap.Dom ∪ φ.preimageLitterSubset ∪ ⋃ (L) (hL), φ.mappedOutsideSubset L hL :=
  by
  rw [supported_action_atom_map_core]
  simp only [PFun.dom_mk, mem_set_of_eq, mem_union, mem_Union]
  rw [or_assoc']
  rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (L hL) -/
theorem supportedActionAtomMapCore_dom_eq :
    φ.supportedActionAtomMapCore.Dom =
      φ.atomMap.Dom ∪ φ.preimageLitterSubset ∪ ⋃ (L) (hL), φ.mappedOutsideSubset L hL :=
  by
  ext a : 1
  exact φ.mem_supported_action_atom_map_core_dom_iff a

theorem supportedActionAtomMapCore_dom_small : Small φ.supportedActionAtomMapCore.Dom :=
  by
  rw [supported_action_atom_map_core_dom_eq]
  refine' small.union (small.union φ.atom_map_dom_small _) _
  · exact φ.preimage_litter_subset_small
  · refine' small.bUnion _ _
    · refine' lt_of_le_of_lt _ φ.litter_map_dom_small
      refine' ⟨⟨fun L => ⟨_, L.prop⟩, fun L₁ L₂ h => _⟩⟩
      simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff, eq_self_iff_true, and_true_iff,
        litter.to_near_litter_injective.eq_iff, Subtype.coe_inj] at h
      exact h
    · intro L hL
      exact φ.mapped_outside_subset_small L hL

theorem mk_supported_action_atom_map_dom :
    (#(φ.supportedActionAtomMapCore.Dom ∆
            ((fun a => Part.getOrElse (φ.supportedActionAtomMapCore a) (Inhabited.default Atom)) ''
              φ.supportedActionAtomMapCore.Dom) :
          Set Atom)) ≤
      (#litterSet <| φ.preimageLitter) :=
  by
  rw [mk_litter_set]
  refine' le_trans (mk_subtype_mono symm_diff_subset_union) (le_trans (mk_union_le _ _) _)
  refine' add_le_of_le κ_regular.aleph_0_le _ _
  exact le_of_lt φ.supported_action_atom_map_core_dom_small
  exact le_trans mk_image_le (le_of_lt φ.supported_action_atom_map_core_dom_small)

theorem supported_action_eq_of_dom {a : Atom} (ha : (φ.atomMap a).Dom) :
    (φ.supportedActionAtomMapCore a).get (Or.inl ha) = (φ.atomMap a).get ha :=
  by
  simp only [supported_action_atom_map_core]
  rw [Or.elim'_left]

theorem supported_action_eq_of_mem_preimageLitterSubset {a : Atom}
    (ha : a ∈ φ.preimageLitterSubset) :
    (φ.supportedActionAtomMapCore a).get (Or.inr (Or.inl ha)) = φ.preimageLitterEquiv ⟨a, ha⟩ :=
  by
  simp only [supported_action_atom_map_core]
  rw [Or.elim'_right, Or.elim'_left]
  intro h'
  have := φ.preimage_litter_not_banned
  rw [banned_litter_iff] at this
  push_neg at this
  exact this.1 a h' (φ.preimage_litter_subset_subset ha).symm

theorem supported_action_eq_of_mem_mappedOutsideSubset {a : Atom} {L hL}
    (ha : a ∈ φ.mappedOutsideSubset L hL) :
    (φ.supportedActionAtomMapCore a).get (Or.inr (Or.inr ⟨L, hL, ha⟩)) =
      φ.mappedOutsideEquiv L hL ⟨a, ha⟩ :=
  by
  have : ∃ L hL, a ∈ φ.mapped_outside_subset L hL := ⟨L, hL, ha⟩
  simp only [supported_action_atom_map_core]
  rw [Or.elim'_right, Or.elim'_right]
  · cases
      eq_of_mem_litter_set_of_mem_litter_set (φ.mapped_outside_subset_subset _ hL ha)
        (φ.mapped_outside_subset_subset _ this.some_spec.some this.some_spec.some_spec)
    rfl
  · intro h
    have :=
      eq_of_mem_litter_set_of_mem_litter_set (φ.mapped_outside_subset_subset _ hL ha)
        (φ.preimage_litter_subset_subset h)
    cases this
    have := φ.preimage_litter_not_banned
    rw [banned_litter_iff] at this
    push_neg at this
    cases this.2.1 hL
  · exact ((mapped_outside_subset_spec _ _ hL).1 ha).2

theorem supportedActionAtomMapCore_injective ⦃a b : Atom⦄ (hφ : φ.Lawful)
    (ha : (supportedActionAtomMapCore φ a).Dom) (hb : (supportedActionAtomMapCore φ b).Dom)
    (hab : (φ.supportedActionAtomMapCore a).get ha = (φ.supportedActionAtomMapCore b).get hb) :
    a = b :=
  by
  obtain ha | ha | ⟨L, hL, ha⟩ := ha <;> obtain hb | hb | ⟨L', hL', hb⟩ := hb
  · have :=
      (supported_action_eq_of_dom _ ha).symm.trans (hab.trans (supported_action_eq_of_dom _ hb))
    exact hφ.atom_map_injective ha hb this
  · have :=
      (supported_action_eq_of_dom _ ha).symm.trans
        (hab.trans (supported_action_eq_of_mem_preimage_litter_subset _ hb))
    obtain ⟨hab, -⟩ := subtype.coe_eq_iff.mp this.symm
    cases hab.not_mem_ran ⟨a, ha, rfl⟩
  · have :=
      (supported_action_eq_of_dom _ ha).symm.trans
        (hab.trans (supported_action_eq_of_mem_mapped_outside_subset _ hb))
    obtain ⟨hab, -⟩ := subtype.coe_eq_iff.mp this.symm
    cases hab.not_mem_ran ⟨a, ha, rfl⟩
  · have :=
      (supported_action_eq_of_mem_preimage_litter_subset _ ha).symm.trans
        (hab.trans (supported_action_eq_of_dom _ hb))
    obtain ⟨hab, -⟩ := subtype.coe_eq_iff.mp this
    cases hab.not_mem_ran ⟨b, hb, rfl⟩
  · have :=
      (supported_action_eq_of_mem_preimage_litter_subset _ ha).symm.trans
        (hab.trans (supported_action_eq_of_mem_preimage_litter_subset _ hb))
    rw [Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq] at this
    exact subtype.coe_inj.mpr this
  · have :=
      (supported_action_eq_of_mem_preimage_litter_subset _ ha).symm.trans
        (hab.trans (supported_action_eq_of_mem_mapped_outside_subset _ hb))
    obtain ⟨hab, -⟩ := subtype.coe_eq_iff.mp this
    cases
      without_preimage.not_mapped_outside φ hab _ hL' (φ.mapped_outside_equiv L' hL' ⟨b, hb⟩).prop
  · have :=
      (supported_action_eq_of_mem_mapped_outside_subset _ ha).symm.trans
        (hab.trans (supported_action_eq_of_dom _ hb))
    obtain ⟨hab, -⟩ := subtype.coe_eq_iff.mp this
    cases hab.not_mem_ran ⟨b, hb, rfl⟩
  · have :=
      (supported_action_eq_of_mem_mapped_outside_subset _ ha).symm.trans
        (hab.trans (supported_action_eq_of_mem_preimage_litter_subset _ hb))
    obtain ⟨hab, -⟩ := subtype.coe_eq_iff.mp this.symm
    cases without_preimage.not_mapped_outside φ hab _ hL (φ.mapped_outside_equiv L hL ⟨a, ha⟩).prop
  · have :=
      (supported_action_eq_of_mem_mapped_outside_subset _ ha).symm.trans
        (hab.trans (supported_action_eq_of_mem_mapped_outside_subset _ hb))
    cases hφ.litter_map_injective hL hL' _
    · simp only [Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq] at this
      exact this
    obtain ⟨hab, -⟩ := subtype.coe_eq_iff.mp this
    exact ⟨_, hab.1, (φ.mapped_outside_equiv L' hL' ⟨b, hb⟩).prop.1⟩

theorem supportedActionAtomMapCore_mem (hφ : φ.Lawful) (a : Atom)
    (ha : (φ.supportedActionAtomMapCore a).Dom) (L : Litter) (hL : (φ.litterMap L).Dom) :
    a.fst = L ↔ (φ.supportedActionAtomMapCore a).get ha ∈ (φ.litterMap L).get hL :=
  by
  obtain ha | ha | ⟨L', hL', ha⟩ := ha
  · rw [hφ.atom_mem a ha L hL, supported_action_eq_of_dom]
  · rw [supported_action_eq_of_mem_preimage_litter_subset]
    constructor
    · rintro rfl
      have := φ.preimage_litter_subset_subset ha
      rw [mem_litter_set] at this
      rw [this] at hL
      have := banned_litter.litter_dom _ hL
      cases φ.preimage_litter_not_banned this
    · intro h
      cases (φ.preimage_litter_equiv ⟨a, ha⟩).prop.not_mem_map L hL h
  · cases φ.mapped_outside_subset_subset L' hL' ha
    rw [supported_action_eq_of_mem_mapped_outside_subset]
    constructor
    · rintro rfl
      exact (φ.mapped_outside_equiv _ _ _).prop.mem_map
    · intro h
      refine' hφ.litter_map_injective hL' hL ⟨_, _, h⟩
      exact (φ.mapped_outside_equiv _ _ _).prop.mem_map

noncomputable def fillAtomRange : NearLitterAction
    where
  atomMap := φ.supportedActionAtomMapCore
  litterMap := φ.litterMap
  atomMap_dom_small := φ.supportedActionAtomMapCore_dom_small
  litterMap_dom_small := φ.litterMap_dom_small

theorem fillAtomRangeLawful (hφ : φ.Lawful) : φ.fillAtomRange.Lawful :=
  { atomMap_injective := fun a b => φ.supportedActionAtomMapCore_injective hφ
    litterMap_injective := hφ.litterMap_injective
    atom_mem := φ.supportedActionAtomMapCore_mem hφ }

variable {φ}

@[simp]
theorem fillAtomRange_atomMap : φ.fillAtomRange.atomMap = φ.supportedActionAtomMapCore :=
  rfl

@[simp]
theorem fillAtomRange_litterMap : φ.fillAtomRange.litterMap = φ.litterMap :=
  rfl

theorem subset_supportedActionAtomMapCore_dom : φ.atomMap.Dom ⊆ φ.supportedActionAtomMapCore.Dom :=
  subset_union_left _ _

theorem subset_supportedActionAtomMapCore_ran : φ.atomMap.ran ⊆ φ.supportedActionAtomMapCore.ran :=
  by
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a, subset_supported_action_atom_map_core_dom ha, φ.supported_action_eq_of_dom _⟩

theorem fillAtomRange_symmDiff_subset_ran (hφ : φ.Lawful) (L : Litter)
    (hL : (φ.fillAtomRange.litterMap L).Dom) :
    ((φ.fillAtomRange.litterMap L).get hL : Set Atom) ∆
        litterSet ((φ.fillAtomRange.litterMap L).get hL).fst ⊆
      φ.fillAtomRange.atomMap.ran :=
  by
  rintro a
  by_cases ha₁ : a ∈ φ.atom_map.ran
  · obtain ⟨b, hb, rfl⟩ := ha₁
    exact fun _ => ⟨b, Or.inl hb, φ.supported_action_eq_of_dom hb⟩
  rintro (⟨ha₂, ha₃⟩ | ⟨ha₂, ha₃⟩)
  · refine' ⟨(φ.mapped_outside_equiv L hL).symm ⟨a, ha₂, ha₃, ha₁⟩, _, _⟩
    · exact Or.inr (Or.inr ⟨L, hL, ((φ.mapped_outside_equiv L hL).symm _).prop⟩)
    · simp only [fill_atom_range_atom_map]
      refine'
        (φ.supported_action_eq_of_mem_mapped_outside_subset
              ((φ.mapped_outside_equiv L hL).symm _).prop).trans
          _
      simp only [Subtype.coe_eta, Equiv.apply_symm_apply, Subtype.coe_mk]
  · by_cases ha₄ : ∀ (L' : litter) (hL' : (φ.litter_map L').Dom), a ∉ (φ.litter_map L').get hL'
    · refine' ⟨φ.preimage_litter_equiv.symm ⟨a, ⟨L, hL, ha₂⟩, ha₄, ha₁⟩, _, _⟩
      · exact Or.inr (Or.inl (φ.preimage_litter_equiv.symm _).prop)
      · simp only [fill_atom_range_atom_map]
        refine'
          (φ.supported_action_eq_of_mem_preimage_litter_subset
                (φ.preimage_litter_equiv.symm _).prop).trans
            _
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply, Subtype.coe_mk]
    · push_neg at ha₄
      obtain ⟨L', hL', ha₄⟩ := ha₄
      refine' ⟨(φ.mapped_outside_equiv L' hL').symm ⟨a, ha₄, _, ha₁⟩, _, _⟩
      · intro ha
        have :=
          near_litter.inter_nonempty_of_fst_eq_fst (eq_of_mem_litter_set_of_mem_litter_set ha₂ ha)
        cases hφ.litter_map_injective hL hL' this
        exact ha₃ ha₄
      · exact Or.inr (Or.inr ⟨L', hL', ((φ.mapped_outside_equiv L' hL').symm _).prop⟩)
      · simp only [fill_atom_range_atom_map]
        refine'
          (φ.supported_action_eq_of_mem_mapped_outside_subset
                ((φ.mapped_outside_equiv L' hL').symm _).prop).trans
            _
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply, Subtype.coe_mk]

end NearLitterAction

end ConNF
