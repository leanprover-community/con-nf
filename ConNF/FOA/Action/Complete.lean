import ConNF.FOA.Action.NearLitterAction

/-!
# Completed permutations
-/

open Cardinal Quiver Set Sum WithBot

open scoped Cardinal Classical Pointwise

universe u

namespace ConNF

variable [Params.{u}] (φ : NearLitterAction) [BasePositions] [Level]
  [FOAAssumptions] {β : Λ} {A : ExtendedIndex β}

namespace NearLitterAction

/-- The *sandbox litter* for a near-litter action is an arbitrarily chosen litter that
isn't banned. -/
noncomputable def sandboxLitter : Litter :=
  φ.not_bannedLitter_nonempty.some

theorem sandboxLitter_not_banned : ¬φ.BannedLitter φ.sandboxLitter :=
  φ.not_bannedLitter_nonempty.some.prop

theorem mk_atomMap_image_le_mk_sandbox :
    #(φ.atomMap.Dom ∆ (φ.atomMapOrElse '' φ.atomMap.Dom) : Set Atom) ≤
      #(litterSet φ.sandboxLitter) := by
  rw [mk_litterSet]
  refine' le_trans (mk_subtype_mono symmDiff_subset_union) (le_trans (mk_union_le _ _) _)
  refine' add_le_of_le Params.κ_isRegular.aleph0_le _ _
  exact le_of_lt φ.atomMap_dom_small
  exact le_trans mk_image_le (le_of_lt φ.atomMap_dom_small)

theorem disjoint_sandbox :
    Disjoint (φ.atomMap.Dom ∪ φ.atomMapOrElse '' φ.atomMap.Dom) (litterSet φ.sandboxLitter) := by
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem]
  rintro a ⟨ha₁, ha₂⟩
  rw [mem_litterSet] at ha₂
  have hnb := φ.sandboxLitter_not_banned
  rw [← ha₂] at hnb
  obtain (ha₁ | ha₁) := ha₁
  · exact hnb (BannedLitter.atomDom a ha₁)
  · refine' hnb _
    simp only [mem_image, PFun.mem_dom] at ha₁
    obtain ⟨b, ⟨_, hb, rfl⟩, rfl⟩ := ha₁
    rw [φ.atomMapOrElse_of_dom hb]
    exact BannedLitter.atomMap b hb

/-- A local permutation induced by completing the orbits of atoms in a near-litter action.
This function creates forward and backward images of atoms in the *sandbox litter*,
a litter which is away from the domain and range of the approximation in question, so it should
not interfere with other constructions. -/
noncomputable def atomLocalPerm (hφ : φ.Lawful) : LocalPerm Atom :=
  LocalPerm.complete φ.atomMapOrElse φ.atomMap.Dom (litterSet φ.sandboxLitter)
    φ.mk_atomMap_image_le_mk_sandbox
    (by simpa only [mk_litterSet] using Params.κ_isRegular.aleph0_le)
    φ.disjoint_sandbox (φ.atomMapOrElse_injective hφ)

theorem sandboxSubset_small :
    Small
      (LocalPerm.sandboxSubset φ.mk_atomMap_image_le_mk_sandbox
        (by simpa only [mk_litterSet] using Params.κ_isRegular.aleph0_le)) := by
  rw [Small]
  rw [Cardinal.mk_congr (LocalPerm.sandboxSubsetEquiv _ _)]
  simp only [mk_sum, mk_prod, mk_denumerable, lift_aleph0, lift_uzero, lift_id]
  refine' add_lt_of_lt Params.κ_isRegular.aleph0_le _ _ <;>
    refine' mul_lt_of_lt Params.κ_isRegular.aleph0_le
      (lt_of_le_of_lt aleph0_le_mk_Λ Params.Λ_lt_κ) _ <;>
    refine' lt_of_le_of_lt (mk_subtype_mono (diff_subset _ _)) _
  · exact φ.atomMap_dom_small
  · exact lt_of_le_of_lt mk_image_le φ.atomMap_dom_small

theorem atomLocalPerm_domain_small (hφ : φ.Lawful) : Small (φ.atomLocalPerm hφ).domain :=
  Small.union (Small.union φ.atomMap_dom_small (lt_of_le_of_lt mk_image_le φ.atomMap_dom_small))
    φ.sandboxSubset_small

/-- A near-litter approximation built from this near-litter action.
Its action on atoms matches that of the action, and its rough action on litters
matches the given litter permutation. -/
noncomputable def complete (hφ : φ.Lawful) (A : ExtendedIndex β) : NearLitterApprox
    where
  atomPerm := φ.atomLocalPerm hφ
  litterPerm := φ.flexibleLitterLocalPerm hφ A
  domain_small _ := Small.mono (inter_subset_right _ _) (φ.atomLocalPerm_domain_small hφ)

theorem atomLocalPerm_apply_eq (hφ : φ.Lawful) {a : Atom} (ha : (φ.atomMap a).Dom) :
    φ.atomLocalPerm hφ a = (φ.atomMap a).get ha := by
  rwa [atomLocalPerm, LocalPerm.complete_apply_eq, atomMapOrElse_of_dom]

theorem complete_smul_atom_eq {hφ : φ.Lawful} {a : Atom} (ha : (φ.atomMap a).Dom) :
    φ.complete hφ A • a = (φ.atomMap a).get ha :=
  φ.atomLocalPerm_apply_eq hφ ha

@[simp]
theorem complete_smul_litter_eq {hφ : φ.Lawful} (L : Litter) :
    φ.complete hφ A • L = φ.flexibleLitterLocalPerm hφ A L :=
  rfl

theorem smul_atom_eq {hφ : φ.Lawful} {π : NearLitterPerm}
    (hπ : (φ.complete hφ A).ExactlyApproximates π) {a : Atom} (ha : (φ.atomMap a).Dom) :
    π • a = (φ.atomMap a).get ha := by
  rw [← hπ.map_atom a (Or.inl (Or.inl ha)), φ.complete_smul_atom_eq ha]

theorem smul_toNearLitter_eq_of_preciseAt {hφ : φ.Lawful} {π : NearLitterPerm}
    (hπ : (φ.complete hφ A).ExactlyApproximates π) {L : Litter} (hL : (φ.litterMap L).Dom)
    (hφL : φ.PreciseAt hL) (hπL : π • L = ((φ.litterMap L).get hL).1) :
    π • L.toNearLitter = (φ.litterMap L).get hL := by
  refine' SetLike.coe_injective _
  ext a : 1
  simp only [mem_smul_set_iff_inv_smul_mem, NearLitterPerm.smul_nearLitter_coe, Litter.coe_toNearLitter,
    mem_litterSet, SetLike.mem_coe]
  constructor
  · intro ha
    by_cases h : π.IsException a
    · suffices h' : π⁻¹ • a ∈ φ.atomMap.Dom
      · rw [hφ.atom_mem _ h' L hL] at ha
        have := hπ.map_atom _ (Or.inl (Or.inl h'))
        rw [φ.complete_smul_atom_eq h'] at this
        rw [this, smul_inv_smul] at ha
        exact ha
      rw [← hπ.symm_map_atom a (hπ.exception_mem _ h)] at ha ⊢
      obtain (hdom | hdom) | hdom :=
        (φ.complete hφ A).atomPerm.symm.map_domain (hπ.exception_mem _ h)
      · exact hdom
      · obtain ⟨c, hc₁, hc₂⟩ := hdom
        rw [φ.atomMapOrElse_of_dom hc₁] at hc₂
        have := hφL.fwd c hc₁ (by rwa [hc₂])
        rw [hc₂] at this
        exact this
      · exfalso
        refine φ.sandboxLitter_not_banned ?_
        rw [← eq_of_mem_litterSet_of_mem_litterSet ha (LocalPerm.sandboxSubset_subset _ _ hdom)]
        exact BannedLitter.litterDom L hL
    · by_contra h'
      simp only [NearLitterPerm.IsException, mem_litterSet, not_or, Classical.not_not, ha] at h
      obtain ⟨b, hb, rfl⟩ :=
        hφL.diff (Or.inr ⟨by rw [← hπL, h.2, smul_inv_smul, mem_litterSet], h'⟩)
      refine' h' ((hφ.atom_mem b hb L hL).mp _)
      have := hπ.map_atom b (Or.inl (Or.inl hb))
      rw [φ.complete_smul_atom_eq hb] at this
      rw [this, inv_smul_smul] at ha
      exact ha
  · intro ha
    by_cases h : π⁻¹ • a ∈ φ.atomMap.Dom
    · rw [hφ.atom_mem _ h L hL]
      have := hπ.map_atom _ (Or.inl (Or.inl h))
      rw [φ.complete_smul_atom_eq h] at this
      rw [this, smul_inv_smul]
      exact ha
    have haL : a ∈ litterSet ((φ.litterMap L).get hL).fst
    · by_contra h'
      obtain ⟨b, hb, rfl⟩ := hφL.diff (Or.inl ⟨ha, h'⟩)
      have := hπ.map_atom b (Or.inl (Or.inl hb))
      rw [φ.complete_smul_atom_eq hb] at this
      rw [this, inv_smul_smul] at h
      exact h hb
    by_contra h'
    have hex : π.IsException a
    · refine' Or.inr fun h'' => h' (h''.trans _)
      rw [inv_smul_eq_iff, hπL]
      exact haL
    obtain (hdom | ⟨b, hb₁, hb₂⟩) | hdom := hπ.exception_mem a hex
    · obtain ⟨b, hb₁, hb₂⟩ := hφL.back ⟨hdom, ha⟩
      have := hπ.map_atom b (Or.inl (Or.inl hb₁))
      rw [φ.complete_smul_atom_eq hb₁] at this
      rw [this, smul_eq_iff_eq_inv_smul] at hb₂
      rw [hb₂] at hb₁
      exact h hb₁
    · rw [φ.atomMapOrElse_of_dom hb₁] at hb₂
      have := hπ.map_atom b (Or.inl (Or.inl hb₁))
      rw [φ.complete_smul_atom_eq hb₁, hb₂, ← inv_smul_eq_iff] at this
      rw [this] at h
      exact h hb₁
    · refine' φ.sandboxLitter_not_banned _
      rw [eq_of_mem_litterSet_of_mem_litterSet (LocalPerm.sandboxSubset_subset _ _ hdom) haL]
      exact BannedLitter.litterMap L hL

theorem smul_nearLitter_eq_of_preciseAt {hφ : φ.Lawful} {π : NearLitterPerm}
    (hπ : (φ.complete hφ A).ExactlyApproximates π) {N : NearLitter} (hN : (φ.litterMap N.1).Dom)
    (hw : φ.PreciseAt hN) (hπL : π • N.1 = ((φ.litterMap N.1).get hN).1) :
    ((π • N : NearLitter) : Set Atom) =
    ((φ.litterMap N.1).get hN : Set Atom) ∆ (π • litterSet N.1 ∆ N) := by
  refine' (NearLitterPerm.smul_nearLitter_eq_smul_symmDiff_smul _ _).trans _
  rw [← φ.smul_toNearLitter_eq_of_preciseAt hπ hN hw hπL]
  rfl

end NearLitterAction

end ConNF
