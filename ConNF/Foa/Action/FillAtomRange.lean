import ConNF.Foa.Action.NearLitterAction

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

theorem withoutPreimage_small : Small {a | φ.WithoutPreimage a} := by
  simp only [WithoutPreimage_iff, setOf_and]
  rw [← inter_assoc]
  refine' Small.mono (inter_subset_left _ _) _
  suffices
    Small (⋃ (L : Litter) (hL), litterSet ((φ.litterMap L).get hL).1 \ (φ.litterMap L).get hL) by
    refine' Small.mono _ this
    rintro a ⟨⟨L, hL, ha₁⟩, ha₂⟩
    simp only [mem_iUnion]
    exact ⟨L, hL, ha₁, ha₂ _ _⟩
  refine' Small.bUnion _ _
  · refine' lt_of_le_of_lt _ φ.litterMap_dom_small
    refine' ⟨⟨fun L => ⟨_, L.prop⟩, _⟩⟩
    intro L₁ L₂ h
    simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff, eq_self_iff_true, and_true_iff,
      Litter.toNearLitter_injective.eq_iff, Subtype.coe_inj] at h
    exact h
  · intro L hL
    refine' Small.mono _ ((φ.litterMap L).get hL).2.prop
    exact fun x hx => Or.inl hx

/-- The subset of the preimage litter that is put in correspondence with the set of
atoms without preimage. -/
def preimageLitterSubset : Set Atom :=
  (le_mk_iff_exists_subset.mp
      (lt_of_lt_of_eq φ.withoutPreimage_small (mk_litterSet φ.preimageLitter).symm).le).choose

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
    Small {a | φ.MappedOutside L hL a} := by
  simp only [MappedOutside_iff, setOf_and]
  rw [← inter_assoc]
  refine' Small.mono (inter_subset_left _ _) _
  refine' Small.mono _ ((φ.litterMap L).get hL).2.prop
  exact fun x hx => Or.inr hx

theorem WithoutPreimage.not_mappedOutside {a : Atom} (ha : φ.WithoutPreimage a) (L : Litter)
    (hL : (φ.litterMap L).Dom) : ¬φ.MappedOutside L hL a := fun ha' =>
  ha.not_mem_map L hL ha'.mem_map

theorem MappedOutside.not_withoutPreimage {a : Atom} {L : Litter} {hL : (φ.litterMap L).Dom}
    (ha : φ.MappedOutside L hL a) : ¬φ.WithoutPreimage a := fun ha' =>
  ha'.not_mem_map L hL ha.mem_map

/-- The amount of atoms in a litter that are not in the domain already is `κ`. -/
theorem mk_mapped_outside_domain (L : Litter) :
    (#(litterSet L \ φ.atomMap.Dom : Set Atom)) = (#κ) := by
  refine' le_antisymm _ _
  · rw [← mk_litterSet]
    exact mk_subtype_mono fun x hx => hx.1
  by_contra' h
  have := Small.union h φ.atomMap_dom_small
  rw [diff_union_self] at this
  exact (mk_litterSet L).not_lt (Small.mono (subset_union_left _ _) this)

/-- To each litter we associate a subset which is to contain the atoms mapped outside it. -/
def mappedOutsideSubset (L : Litter) (hL : (φ.litterMap L).Dom) : Set Atom :=
  (le_mk_iff_exists_subset.mp
      (lt_of_lt_of_eq (φ.mappedOutside_small L hL) (φ.mk_mapped_outside_domain L).symm).le).choose

theorem mappedOutsideSubset_spec (L : Litter) (hL : (φ.litterMap L).Dom) :
    φ.mappedOutsideSubset L hL ⊆ litterSet L \ φ.atomMap.Dom ∧
      #(φ.mappedOutsideSubset L hL) = #{a : Atom | φ.MappedOutside L hL a} :=
  (le_mk_iff_exists_subset.mp
      (lt_of_lt_of_eq (φ.mappedOutside_small L hL)
          (φ.mk_mapped_outside_domain L).symm).le).choose_spec

theorem mappedOutsideSubset_subset (L : Litter) (hL : (φ.litterMap L).Dom) :
    φ.mappedOutsideSubset L hL ⊆ litterSet L := fun _ hx =>
  ((φ.mappedOutsideSubset_spec L hL).1 hx).1

theorem mappedOutsideSubset_closure (L : Litter) (hL : (φ.litterMap L).Dom) :
    φ.mappedOutsideSubset L hL ⊆ φ.atomMap.Domᶜ := fun _ hx =>
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
          φ.mappedOutsideEquiv h.choose h.choose_spec.choose ⟨a, h.choose_spec.choose_spec⟩ }

theorem mem_supportedActionAtomMapCore_dom_iff (a : Atom) :
    (φ.supportedActionAtomMapCore a).Dom ↔
      a ∈ φ.atomMap.Dom ∪ φ.preimageLitterSubset ∪ ⋃ (L) (hL), φ.mappedOutsideSubset L hL := by
  rw [supportedActionAtomMapCore]
  simp only [PFun.dom_mk, mem_setOf_eq, mem_union, mem_iUnion]
  rw [or_assoc]
  rfl

theorem supportedActionAtomMapCore_dom_eq :
    φ.supportedActionAtomMapCore.Dom =
      φ.atomMap.Dom ∪ φ.preimageLitterSubset ∪ ⋃ (L) (hL), φ.mappedOutsideSubset L hL := by
  ext a : 1
  exact φ.mem_supportedActionAtomMapCore_dom_iff a

theorem supportedActionAtomMapCore_dom_small : Small φ.supportedActionAtomMapCore.Dom := by
  rw [supportedActionAtomMapCore_dom_eq]
  refine' Small.union (Small.union φ.atomMap_dom_small _) _
  · exact φ.preimageLitterSubset_small
  · refine' Small.bUnion _ _
    · refine' lt_of_le_of_lt _ φ.litterMap_dom_small
      refine' ⟨⟨fun L => ⟨_, L.prop⟩, fun L₁ L₂ h => _⟩⟩
      simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff, eq_self_iff_true, and_true_iff,
        Litter.toNearLitter_injective.eq_iff, Subtype.coe_inj] at h
      exact h
    · intro L hL
      exact φ.mappedOutsideSubset_small L hL

theorem mk_supportedActionAtomMap_dom :
    (#(φ.supportedActionAtomMapCore.Dom ∆
        ((fun a => Part.getOrElse (φ.supportedActionAtomMapCore a) default) ''
          φ.supportedActionAtomMapCore.Dom) : Set Atom)) ≤
      #(litterSet φ.preimageLitter) := by
  rw [mk_litterSet]
  refine' le_trans (mk_subtype_mono symmDiff_subset_union) (le_trans (mk_union_le _ _) _)
  refine' add_le_of_le κ_isRegular.aleph0_le _ _
  · exact le_of_lt φ.supportedActionAtomMapCore_dom_small
  · exact le_trans mk_image_le (le_of_lt φ.supportedActionAtomMapCore_dom_small)

theorem supportedAction_eq_of_dom {a : Atom} (ha : (φ.atomMap a).Dom) :
    (φ.supportedActionAtomMapCore a).get (Or.inl ha) = (φ.atomMap a).get ha := by
  simp only [supportedActionAtomMapCore]
  rw [Or.elim'_left]

theorem supportedAction_eq_of_mem_preimageLitterSubset {a : Atom}
    (ha : a ∈ φ.preimageLitterSubset) :
    (φ.supportedActionAtomMapCore a).get (Or.inr (Or.inl ha)) = φ.preimageLitterEquiv ⟨a, ha⟩ := by
  simp only [supportedActionAtomMapCore]
  rw [Or.elim'_right, Or.elim'_left]
  intro h'
  have := φ.preimageLitter_not_banned
  rw [BannedLitter_iff] at this
  push_neg at this
  exact this.1 a h' (φ.preimageLitterSubset_subset ha).symm

theorem supportedAction_eq_of_mem_mappedOutsideSubset {a : Atom}
    {L : Litter} {hL : (litterMap φ L).Dom}
    (ha : a ∈ φ.mappedOutsideSubset L hL) :
    (φ.supportedActionAtomMapCore a).get (Or.inr (Or.inr ⟨L, hL, ha⟩)) =
      φ.mappedOutsideEquiv L hL ⟨a, ha⟩ := by
  simp only [supportedActionAtomMapCore]
  rw [Or.elim'_right, Or.elim'_right]
  · generalize_proofs
    have : ∃ (L : Litter), ∃ (hL : (litterMap φ L).Dom), a ∈ φ.mappedOutsideSubset L hL
    · exact ⟨L, hL, ha⟩
    cases eq_of_mem_litterSet_of_mem_litterSet (φ.mappedOutsideSubset_subset _ hL ha)
      (φ.mappedOutsideSubset_subset _ this.choose_spec.choose this.choose_spec.choose_spec)
    rfl
  · intro h
    have := eq_of_mem_litterSet_of_mem_litterSet (φ.mappedOutsideSubset_subset _ hL ha)
      (φ.preimageLitterSubset_subset h)
    cases this
    have := φ.preimageLitter_not_banned
    rw [BannedLitter_iff] at this
    push_neg at this
    cases this.2.1 hL
  · exact ((mappedOutsideSubset_spec _ _ hL).1 ha).2

theorem supportedActionAtomMapCore_injective ⦃a b : Atom⦄ (hφ : φ.Lawful)
    (ha : (supportedActionAtomMapCore φ a).Dom) (hb : (supportedActionAtomMapCore φ b).Dom)
    (hab : (φ.supportedActionAtomMapCore a).get ha = (φ.supportedActionAtomMapCore b).get hb) :
    a = b := by
  obtain ha | ha | ⟨L, hL, ha⟩ := ha <;> obtain hb | hb | ⟨L', hL', hb⟩ := hb
  · have := (supportedAction_eq_of_dom _ ha).symm.trans (hab.trans (supportedAction_eq_of_dom _ hb))
    exact hφ.atomMap_injective ha hb this
  · have := (supportedAction_eq_of_dom _ ha).symm.trans
      (hab.trans (supportedAction_eq_of_mem_preimageLitterSubset _ hb))
    obtain ⟨hab, -⟩ := Subtype.coe_eq_iff.mp this.symm
    cases hab.not_mem_ran ⟨a, ha, rfl⟩
  · have := (supportedAction_eq_of_dom _ ha).symm.trans
      (hab.trans (supportedAction_eq_of_mem_mappedOutsideSubset _ hb))
    obtain ⟨hab, -⟩ := Subtype.coe_eq_iff.mp this.symm
    cases hab.not_mem_ran ⟨a, ha, rfl⟩
  · have := (supportedAction_eq_of_mem_preimageLitterSubset _ ha).symm.trans
      (hab.trans (supportedAction_eq_of_dom _ hb))
    obtain ⟨hab, -⟩ := Subtype.coe_eq_iff.mp this
    cases hab.not_mem_ran ⟨b, hb, rfl⟩
  · have := (supportedAction_eq_of_mem_preimageLitterSubset _ ha).symm.trans
      (hab.trans (supportedAction_eq_of_mem_preimageLitterSubset _ hb))
    rw [Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq] at this
    exact Subtype.coe_inj.mpr this
  · have := (supportedAction_eq_of_mem_preimageLitterSubset _ ha).symm.trans
      (hab.trans (supportedAction_eq_of_mem_mappedOutsideSubset _ hb))
    obtain ⟨hab, -⟩ := Subtype.coe_eq_iff.mp this
    cases WithoutPreimage.not_mappedOutside φ hab _ hL' (φ.mappedOutsideEquiv L' hL' ⟨b, hb⟩).prop
  · have := (supportedAction_eq_of_mem_mappedOutsideSubset _ ha).symm.trans
      (hab.trans (supportedAction_eq_of_dom _ hb))
    obtain ⟨hab, -⟩ := Subtype.coe_eq_iff.mp this
    cases hab.not_mem_ran ⟨b, hb, rfl⟩
  · have := (supportedAction_eq_of_mem_mappedOutsideSubset _ ha).symm.trans
      (hab.trans (supportedAction_eq_of_mem_preimageLitterSubset _ hb))
    obtain ⟨hab, -⟩ := Subtype.coe_eq_iff.mp this.symm
    cases WithoutPreimage.not_mappedOutside φ hab _ hL (φ.mappedOutsideEquiv L hL ⟨a, ha⟩).prop
  · have := (supportedAction_eq_of_mem_mappedOutsideSubset _ ha).symm.trans
      (hab.trans (supportedAction_eq_of_mem_mappedOutsideSubset _ hb))
    have := hφ.litterMap_injective hL hL' ?_
    · cases this
      simp only [mem_setOf_eq, coe_setOf, Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq,
        Subtype.mk.injEq] at this
      exact this
    · obtain ⟨hab, -⟩ := Subtype.coe_eq_iff.mp this
      exact ⟨_, hab.1, (φ.mappedOutsideEquiv L' hL' ⟨b, hb⟩).prop.1⟩

theorem supportedActionAtomMapCore_mem (hφ : φ.Lawful) (a : Atom)
    (ha : (φ.supportedActionAtomMapCore a).Dom) (L : Litter) (hL : (φ.litterMap L).Dom) :
    a.fst = L ↔ (φ.supportedActionAtomMapCore a).get ha ∈ (φ.litterMap L).get hL := by
  obtain ha | ha | ⟨L', hL', ha⟩ := ha
  · rw [hφ.atom_mem a ha L hL, supportedAction_eq_of_dom]
  · rw [supportedAction_eq_of_mem_preimageLitterSubset]
    constructor
    · rintro rfl
      have := φ.preimageLitterSubset_subset ha
      rw [mem_litterSet] at this
      rw [this] at hL
      have := BannedLitter.litterDom _ hL
      cases φ.preimageLitter_not_banned this
    · intro h
      cases (φ.preimageLitterEquiv ⟨a, ha⟩).prop.not_mem_map L hL h
  · cases φ.mappedOutsideSubset_subset L' hL' ha
    rw [supportedAction_eq_of_mem_mappedOutsideSubset]
    constructor
    · rintro rfl
      exact (φ.mappedOutsideEquiv _ _ ⟨a, ha⟩).prop.mem_map
    · intro h
      refine' hφ.litterMap_injective hL' hL ⟨_, _, h⟩
      exact (φ.mappedOutsideEquiv _ _ ⟨a, ha⟩).prop.mem_map

noncomputable def fillAtomRange : NearLitterAction
    where
  atomMap := φ.supportedActionAtomMapCore
  litterMap := φ.litterMap
  atomMap_dom_small := φ.supportedActionAtomMapCore_dom_small
  litterMap_dom_small := φ.litterMap_dom_small

theorem fillAtomRangeLawful (hφ : φ.Lawful) : φ.fillAtomRange.Lawful
    where
  atomMap_injective := fun _ _ => φ.supportedActionAtomMapCore_injective hφ
  litterMap_injective := hφ.litterMap_injective
  atom_mem := φ.supportedActionAtomMapCore_mem hφ

variable {φ}

@[simp]
theorem fillAtomRange_atomMap : φ.fillAtomRange.atomMap = φ.supportedActionAtomMapCore :=
  rfl

@[simp]
theorem fillAtomRange_litterMap : φ.fillAtomRange.litterMap = φ.litterMap :=
  rfl

theorem subset_supportedActionAtomMapCore_dom :
    φ.atomMap.Dom ⊆ φ.supportedActionAtomMapCore.Dom :=
  subset_union_left _ _

theorem subset_supportedActionAtomMapCore_ran :
    φ.atomMap.ran ⊆ φ.supportedActionAtomMapCore.ran := by
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a, subset_supportedActionAtomMapCore_dom ha, φ.supportedAction_eq_of_dom _⟩

theorem fillAtomRange_symmDiff_subset_ran (hφ : φ.Lawful) (L : Litter)
    (hL : (φ.fillAtomRange.litterMap L).Dom) :
    ((φ.fillAtomRange.litterMap L).get hL : Set Atom) ∆
        litterSet ((φ.fillAtomRange.litterMap L).get hL).fst ⊆
      φ.fillAtomRange.atomMap.ran := by
  intro a
  by_cases ha₁ : a ∈ φ.atomMap.ran
  · obtain ⟨b, hb, rfl⟩ := ha₁
    exact fun _ => ⟨b, Or.inl hb, φ.supportedAction_eq_of_dom hb⟩
  rintro (⟨ha₂, ha₃⟩ | ⟨ha₂, ha₃⟩)
  · refine' ⟨(φ.mappedOutsideEquiv L hL).symm ⟨a, ha₂, ha₃, ha₁⟩, _, _⟩
    · exact Or.inr (Or.inr ⟨L, hL, ((φ.mappedOutsideEquiv L hL).symm _).prop⟩)
    · simp only [fillAtomRange_atomMap]
      refine' (φ.supportedAction_eq_of_mem_mappedOutsideSubset
        ((φ.mappedOutsideEquiv L hL).symm _).prop).trans _
      simp only [Subtype.coe_eta, Equiv.apply_symm_apply, Subtype.coe_mk]
  · by_cases ha₄ : ∀ (L' : Litter) (hL' : (φ.litterMap L').Dom), a ∉ (φ.litterMap L').get hL'
    · refine' ⟨φ.preimageLitterEquiv.symm ⟨a, ⟨L, hL, ha₂⟩, ha₄, ha₁⟩, _, _⟩
      · exact Or.inr (Or.inl (φ.preimageLitterEquiv.symm _).prop)
      · simp only [fillAtomRange_atomMap]
        refine' (φ.supportedAction_eq_of_mem_preimageLitterSubset
          (φ.preimageLitterEquiv.symm _).prop).trans _
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply, Subtype.coe_mk]
    · push_neg at ha₄
      obtain ⟨L', hL', ha₄⟩ := ha₄
      refine' ⟨(φ.mappedOutsideEquiv L' hL').symm ⟨a, ha₄, _, ha₁⟩, _, _⟩
      · intro ha
        have := NearLitter.inter_nonempty_of_fst_eq_fst
          (eq_of_mem_litterSet_of_mem_litterSet ha₂ ha)
        cases hφ.litterMap_injective hL hL' this
        exact ha₃ ha₄
      · exact Or.inr (Or.inr ⟨L', hL', ((φ.mappedOutsideEquiv L' hL').symm _).prop⟩)
      · simp only [fillAtomRange_atomMap]
        refine' (φ.supportedAction_eq_of_mem_mappedOutsideSubset
          ((φ.mappedOutsideEquiv L' hL').symm _).prop).trans _
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply, Subtype.coe_mk]

end NearLitterAction

end ConNF
