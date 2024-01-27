import ConNF.FOA.Action.NearLitterAction

open Cardinal Quiver Set Sum WithBot

open scoped Cardinal Classical Pointwise symmDiff

universe u

namespace ConNF

variable [Params.{u}]

@[ext]
structure NearLitterBehaviour where
  atomMap : Atom →. Atom
  nearLitterMap : NearLitter →. NearLitter
  atomMap_dom_small : Small atomMap.Dom
  nearLitterMap_dom_small : Small nearLitterMap.Dom

namespace NearLitterBehaviour

structure Lawful (ξ : NearLitterBehaviour) : Prop where
  atomMap_injective : ∀ ⦃a b : Atom⦄ (ha : (ξ.atomMap a).Dom) (hb : (ξ.atomMap b).Dom),
    (ξ.atomMap a).get ha = (ξ.atomMap b).get hb → a = b
  atom_mem_iff : ∀ ⦃a : Atom⦄ (ha : (ξ.atomMap a).Dom)
    ⦃N : NearLitter⦄ (hN : (ξ.nearLitterMap N).Dom),
    (ξ.atomMap a).get ha ∈ (ξ.nearLitterMap N).get hN ↔ a ∈ N
  dom_of_mem_symmDiff : ∀ (a : Atom) ⦃N₁ N₂ : NearLitter⦄,
    N₁.fst = N₂.fst → (ξ.nearLitterMap N₁).Dom → (ξ.nearLitterMap N₂).Dom →
    a ∈ (N₁ : Set Atom) ∆ N₂ → (ξ.atomMap a).Dom
  dom_of_mem_inter : ∀ (a : Atom) ⦃N₁ N₂ : NearLitter⦄,
    N₁.fst ≠ N₂.fst → (ξ.nearLitterMap N₁).Dom → (ξ.nearLitterMap N₂).Dom →
    a ∈ (N₁ : Set Atom) ∩ N₂ → (ξ.atomMap a).Dom
  ran_of_mem_symmDiff : ∀ (a : Atom) ⦃N₁ N₂ : NearLitter⦄,
    N₁.fst = N₂.fst → (hN₁ : (ξ.nearLitterMap N₁).Dom) → (hN₂ : (ξ.nearLitterMap N₂).Dom) →
    a ∈ ((ξ.nearLitterMap N₁).get hN₁ : Set Atom) ∆ (ξ.nearLitterMap N₂).get hN₂ →
    a ∈ ξ.atomMap.ran
  ran_of_mem_inter : ∀ (a : Atom) ⦃N₁ N₂ : NearLitter⦄,
    N₁.fst ≠ N₂.fst → (hN₁ : (ξ.nearLitterMap N₁).Dom) → (hN₂ : (ξ.nearLitterMap N₂).Dom) →
    a ∈ ((ξ.nearLitterMap N₁).get hN₁ : Set Atom) ∩ (ξ.nearLitterMap N₂).get hN₂ →
    a ∈ ξ.atomMap.ran

theorem map_nearLitter_fst {ξ : NearLitterBehaviour} (hξ : ξ.Lawful) ⦃N₁ N₂ : NearLitter⦄
    (hN₁ : (ξ.nearLitterMap N₁).Dom) (hN₂ : (ξ.nearLitterMap N₂).Dom) :
    N₁.fst = N₂.fst ↔ ((ξ.nearLitterMap N₁).get hN₁).fst = ((ξ.nearLitterMap N₂).get hN₂).fst := by
  constructor
  · intro h
    rw [← NearLitter.isNear_iff_fst_eq_fst]
    refine (Small.pFun_image (f := ξ.atomMap) ξ.atomMap_dom_small).mono ?_
    intro a ha
    obtain ⟨b, hb, rfl⟩ := hξ.ran_of_mem_symmDiff a h hN₁ hN₂ ha
    exact ⟨b, hb, hb, rfl⟩
  · intro h
    by_contra h'
    suffices : Small (((ξ.nearLitterMap N₁).get hN₁ : Set Atom) ∩ (ξ.nearLitterMap N₂).get hN₂)
    · rw [Small, NearLitter.mk_inter_of_fst_eq_fst h, lt_self_iff_false] at this
      exact this
    refine (Small.pFun_image (f := ξ.atomMap) ξ.atomMap_dom_small).mono ?_
    intro a ha
    obtain ⟨b, hb, rfl⟩ := hξ.ran_of_mem_inter a h' hN₁ hN₂ ha
    exact ⟨b, hb, hb, rfl⟩

def HasLitters (ξ : NearLitterBehaviour) : Prop :=
  ∀ ⦃N : NearLitter⦄, (ξ.nearLitterMap N).Dom → (ξ.nearLitterMap N.1.toNearLitter).Dom

def extraAtoms (ξ : NearLitterBehaviour) : Set Atom :=
  ⋃ (N ∈ ξ.nearLitterMap.Dom), litterSet N.1 \ N

theorem extraAtoms_small (ξ : NearLitterBehaviour) : Small ξ.extraAtoms :=
  Small.bUnion ξ.nearLitterMap_dom_small (fun N _ => N.2.2.mono (fun _ => Or.inl))

@[mk_iff]
inductive BannedLitter (ξ : NearLitterBehaviour) : Litter → Prop
  | atomMap (a : Atom) (h) : BannedLitter ξ ((ξ.atomMap a).get h).1
  | nearLitterMap (N : NearLitter) (h) : BannedLitter ξ ((ξ.nearLitterMap N).get h).1
  | diff (N : NearLitter) (h) (a : Atom) :
    a ∈ ((ξ.nearLitterMap N).get h : Set Atom) \ litterSet ((ξ.nearLitterMap N).get h).1 →
    BannedLitter ξ a.1

theorem bannedLitter_of_mem {ξ : NearLitterBehaviour} (a : Atom) (N : NearLitter)
    (hN : (ξ.nearLitterMap N).Dom) (ha : a ∈ (ξ.nearLitterMap N).get hN) : ξ.BannedLitter a.1 := by
  by_cases h : a.1 = (Part.get (nearLitterMap ξ N) hN).1
  · rw [h]
    exact BannedLitter.nearLitterMap N hN
  · exact BannedLitter.diff N hN _ ⟨ha, h⟩

theorem bannedLitter_small (ξ : NearLitterBehaviour) : Small {L | ξ.BannedLitter L} := by
  simp only [bannedLitter_iff, mem_diff, SetLike.mem_coe, mem_litterSet]
  refine Small.union ?_ (Small.union ?_ ?_)
  · refine' lt_of_le_of_lt _ ξ.atomMap_dom_small
    refine' ⟨⟨fun L => ⟨_, L.prop.choose_spec.choose⟩, fun L₁ L₂ h => _⟩⟩
    simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff] at h
    have := L₁.prop.choose_spec.choose_spec
    simp_rw [h] at this
    exact Subtype.coe_injective (this.trans L₂.prop.choose_spec.choose_spec.symm)
  · refine' lt_of_le_of_lt _ ξ.nearLitterMap_dom_small
    refine' ⟨⟨fun L => ⟨_, L.prop.choose_spec.choose⟩, fun L₁ L₂ h => _⟩⟩
    simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff] at h
    have := L₁.prop.choose_spec.choose_spec
    simp_rw [h] at this
    exact Subtype.coe_injective (this.trans L₂.prop.choose_spec.choose_spec.symm)
  · have : Small
      (⋃ (L : NearLitter) (h : (ξ.nearLitterMap L).Dom),
        ((ξ.nearLitterMap L).get h : Set Atom) \ litterSet ((ξ.nearLitterMap L).get h).1)
    · refine' Small.bUnion _ _
      · refine' lt_of_le_of_lt _ ξ.nearLitterMap_dom_small
        refine' ⟨⟨fun N => ⟨_, N.prop⟩, fun N₁ N₂ h => _⟩⟩
        simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff] at h
        exact Subtype.coe_inj.mp h
      · intro L hL
        refine' Small.mono _ ((ξ.nearLitterMap L).get hL).2.prop
        exact fun x hx => Or.inr hx
    refine' lt_of_le_of_lt _ this
    refine' ⟨⟨fun L => ⟨L.prop.choose_spec.choose_spec.choose, _⟩, fun L₁ L₂ h => _⟩⟩
    · simp only [mem_iUnion]
      exact ⟨_, _, L.prop.choose_spec.choose_spec.choose_spec.1⟩
    simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff] at h
    have := L₁.prop.choose_spec.choose_spec.choose_spec.2
    rw [h] at this
    exact Subtype.coe_injective (this.trans L₂.prop.choose_spec.choose_spec.choose_spec.2.symm)

theorem mk_not_bannedLitter (ξ : NearLitterBehaviour) : #{L | ¬ξ.BannedLitter L} = #μ := by
  have := mk_sum_compl {L | ξ.BannedLitter L}
  rw [compl_setOf, mk_litter] at this
  rw [← this, add_eq_right]
  · by_contra h
    have h' := add_le_add (le_of_lt ξ.bannedLitter_small) (le_of_not_le h)
    rw [this] at h'
    refine' not_lt_of_le h' _
    refine' Cardinal.add_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le Params.κ_lt_μ _
    exact lt_of_le_of_lt Params.κ_isRegular.aleph0_le Params.κ_lt_μ
  · by_contra h
    have h' := add_le_add (le_of_lt ξ.bannedLitter_small) (le_of_not_le h)
    rw [this] at h'
    refine' not_lt_of_le h' _
    refine' Cardinal.add_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le Params.κ_lt_μ _
    exact lt_trans ξ.bannedLitter_small Params.κ_lt_μ

theorem not_bannedLitter_nonempty (ξ : NearLitterBehaviour) : Nonempty {L | ¬ξ.BannedLitter L} := by
  simp only [← mk_ne_zero_iff, mk_not_bannedLitter, Ne.def, mk_ne_zero, not_false_iff]

noncomputable def sandboxLitter (ξ : NearLitterBehaviour) : Litter :=
  ξ.not_bannedLitter_nonempty.some

theorem sandboxLitter_not_banned (ξ : NearLitterBehaviour) : ¬ξ.BannedLitter ξ.sandboxLitter :=
  ξ.not_bannedLitter_nonempty.some.prop

def LitterPresent (ξ : NearLitterBehaviour) (L : Litter) : Prop :=
  ∃ N : NearLitter, (ξ.nearLitterMap N).Dom ∧ N.1 = L

def innerAtoms (ξ : NearLitterBehaviour) (L : Litter) : Set Atom :=
  ⋂ (N : NearLitter) (_ : (ξ.nearLitterMap N).Dom ∧ N.1 = L), N \ litterSet L

def outerAtoms (ξ : NearLitterBehaviour) (L : Litter) : Set Atom :=
  litterSet L \ (⋃ (N : NearLitter) (_ : (ξ.nearLitterMap N).Dom), N)

def allOuterAtoms (ξ : NearLitterBehaviour) : Set Atom :=
  ⋃ (L : Litter) (_ : ξ.LitterPresent L), ξ.outerAtoms L

theorem mem_innerAtoms_iff {ξ : NearLitterBehaviour}
    (L : Litter) (hL : ξ.LitterPresent L) (a : Atom) :
    a ∈ ξ.innerAtoms L ↔ a.1 ≠ L ∧ ∀ N (_ : (ξ.nearLitterMap N).Dom ∧ N.1 = L), a ∈ N := by
  obtain ⟨N, hN, rfl⟩ := hL
  rw [innerAtoms]
  aesop

@[simp]
theorem mem_outerAtoms_iff {ξ : NearLitterBehaviour} (L : Litter) (a : Atom) :
    a ∈ ξ.outerAtoms L ↔ a.1 = L ∧ ∀ N, (ξ.nearLitterMap N).Dom → a ∉ N :=
  by simp only [outerAtoms, mem_diff, mem_litterSet, mem_iUnion, SetLike.mem_coe,
    exists_prop, not_exists, not_and]

@[simp]
theorem mem_allOuterAtoms_iff {ξ : NearLitterBehaviour} (a : Atom) :
    a ∈ ξ.allOuterAtoms ↔ ξ.LitterPresent a.1 ∧ ∀ N, (ξ.nearLitterMap N).Dom → a ∉ N :=
  by simp only [allOuterAtoms, mem_iUnion, mem_outerAtoms_iff, exists_and_left,
    exists_prop, exists_eq_left']

theorem litterPresent_small (ξ : NearLitterBehaviour) : Small {L | ξ.LitterPresent L} := by
  have : Small (⋃ (N : NearLitter) (_ : (ξ.nearLitterMap N).Dom), {N.1})
  · refine Small.bUnion ξ.nearLitterMap_dom_small ?_
    simp only [PFun.mem_dom, small_singleton, forall_exists_index, implies_true, forall_const]
  refine Small.mono ?_ this
  simp only [LitterPresent]
  rintro _ ⟨N, hN, rfl⟩
  exact ⟨_, ⟨N, rfl⟩, _, ⟨hN, rfl⟩, rfl⟩

theorem litterPresent_small' (ξ : NearLitterBehaviour) :
    Small {N : NearLitter | N.IsLitter ∧ ∃ N', (nearLitterMap ξ N').Dom ∧ N'.fst = N.fst} := by
  have : Small {L | ∃ N, (nearLitterMap ξ N).Dom ∧ N.fst = L}
  · refine (ξ.nearLitterMap_dom_small.image (f := fun N => N.1)).mono ?_
    rintro _ ⟨N, hN, rfl⟩
    exact ⟨N, hN, rfl⟩
  refine (this.image (f := Litter.toNearLitter)).mono ?_
  rintro _ ⟨⟨L⟩, N, hN, rfl⟩
  refine ⟨N.1, ⟨N, hN, rfl⟩, rfl⟩

theorem innerAtoms_small {ξ : NearLitterBehaviour} (L : Litter) (hL : ξ.LitterPresent L) :
    Small (ξ.innerAtoms L) := by
  obtain ⟨N, hN, rfl⟩ := hL
  refine Small.mono (biInter_subset_of_mem ⟨hN, rfl⟩) ?_
  exact Small.mono (fun _ => Or.inr) N.2.prop

theorem outerAtoms_small {ξ : NearLitterBehaviour} (L : Litter) (hL : ξ.LitterPresent L) :
    Small (ξ.outerAtoms L) := by
  obtain ⟨N, hN, rfl⟩ := hL
  rw [outerAtoms]
  refine Small.mono ?_ (Small.mono (fun _ => Or.inl) N.2.prop)
  refine Set.diff_subset_diff_right ?_
  intro a ha
  exact ⟨_, ⟨N, rfl⟩, _, ⟨hN, rfl⟩, ha⟩

theorem allOuterAtoms_small {ξ : NearLitterBehaviour} : Small ξ.allOuterAtoms :=
  Small.bUnion ξ.litterPresent_small ξ.outerAtoms_small

/-- The codomain for the inner atoms. -/
def innerAtomsCod (ξ : NearLitterBehaviour) (L : Litter) : Set Atom :=
  (⋂ (N : NearLitter) (hN : (ξ.nearLitterMap N).Dom ∧ N.1 = L), (ξ.nearLitterMap N).get hN.1) \
    ξ.atomMap.ran

@[simp]
theorem mem_innerAtomsCod_iff {ξ : NearLitterBehaviour} (L : Litter) (a : Atom) :
    a ∈ ξ.innerAtomsCod L ↔ (∀ N (hN : (ξ.nearLitterMap N).Dom ∧ N.1 = L),
      a ∈ (ξ.nearLitterMap N).get hN.1) ∧ a ∉ ξ.atomMap.ran :=
  by simp only [innerAtomsCod, mem_diff, mem_iInter, SetLike.mem_coe]

theorem innerAtomsCod_subset (ξ : NearLitterBehaviour)
    (N : NearLitter) (hN : (ξ.nearLitterMap N).Dom) :
    ξ.innerAtomsCod N.1 ⊆ (ξ.nearLitterMap N).get hN := by
  intro a ha
  refine ha.1 _ ⟨N, subset_antisymm ?_ ?_⟩
  · intro a' ha'
    exact ha' _ ⟨⟨hN, rfl⟩, rfl⟩
  · rintro a' ha' _ ⟨_, rfl⟩
    exact ha'

theorem innerAtomsCod_eq {ξ : NearLitterBehaviour}
    (N : NearLitter) (hN : (ξ.nearLitterMap N).Dom) :
    ξ.innerAtomsCod N.1 = ((ξ.nearLitterMap N).get hN : Set Atom) \
      ((⋃ (N' : NearLitter) (hN' : (ξ.nearLitterMap N').Dom ∧ N'.1 = N.1),
        (ξ.nearLitterMap N').get hN'.1 ∆ (ξ.nearLitterMap N).get hN) ∪ ξ.atomMap.ran) := by
  refine subset_antisymm ?_ ?_
  · intro a ha
    rw [mem_innerAtomsCod_iff] at ha
    refine ⟨ha.1 _ ⟨hN, rfl⟩, ?_⟩
    rintro ⟨_, ⟨N', rfl⟩, _, ⟨hN', rfl⟩, ha' | ha'⟩ <;> aesop
  · intro a ha
    rw [mem_innerAtomsCod_iff]
    obtain ⟨ha₁, ha₂⟩ := ha
    constructor
    · intro N' hN'
      contrapose! ha₂
      exact Or.inl ⟨_, ⟨N', rfl⟩, _, ⟨hN', rfl⟩, Or.inr ⟨ha₁, ha₂⟩⟩
    · contrapose! ha₂
      exact Or.inr ha₂

theorem innerAtomsCod_eq_aux {ξ : NearLitterBehaviour} (hξ : ξ.Lawful)
    (N : NearLitter) (hN : (ξ.nearLitterMap N).Dom) :
    Small ((⋃ (N' : NearLitter) (hN' : (ξ.nearLitterMap N').Dom ∧ N'.1 = N.1),
      (ξ.nearLitterMap N').get hN'.1 ∆ (ξ.nearLitterMap N).get hN) ∪ ξ.atomMap.ran) := by
  refine Small.union (Small.bUnion ?_ ?_) ?_
  · exact Small.mono (fun _ h => h.1) ξ.nearLitterMap_dom_small
  · intro N' hN'
    refine Small.mono ?_ (Small.pFun_image ξ.atomMap_dom_small (f := ξ.atomMap))
    intro a ha
    obtain ⟨b, hb₁, hb₂⟩ := hξ.ran_of_mem_symmDiff a hN'.2 hN'.1 hN ha
    exact ⟨b, hb₁, hb₁, hb₂⟩
  · refine Small.mono ?_ (Small.pFun_image ξ.atomMap_dom_small (f := ξ.atomMap))
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, ha, rfl⟩

theorem mk_innerAtomsCod {ξ : NearLitterBehaviour} (hξ : ξ.Lawful)
    (L : Litter) (hL : ξ.LitterPresent L) : #(ξ.innerAtomsCod L) = #κ := by
  obtain ⟨N, hN, rfl⟩ := hL
  refine le_antisymm ?_ ?_
  · refine (mk_le_mk_of_subset (ξ.innerAtomsCod_subset N hN)).trans ?_
    simp only [SetLike.coe_sort_coe, mk_nearLitter'', le_refl]
  · rw [innerAtomsCod_eq N hN]
    by_contra! h
    have := Small.union h (ξ.innerAtomsCod_eq_aux hξ N hN)
    rw [diff_union_self] at this
    refine (Small.mono (fun _ => Or.inl) this).not_le ?_
    simp only [SetLike.coe_sort_coe, mk_nearLitter'', le_refl]

theorem mk_innerAtoms_lt {ξ : NearLitterBehaviour} (hξ : ξ.Lawful)
    (L : Litter) (hL : ξ.LitterPresent L) :
    #(ξ.innerAtoms L) < #(ξ.innerAtomsCod L) := by
  rw [mk_innerAtomsCod hξ L hL]
  exact ξ.innerAtoms_small L hL

noncomputable irreducible_def innerAtomsEmbedding {ξ : NearLitterBehaviour} (hξ : ξ.Lawful)
    (L : Litter) (hL : ξ.LitterPresent L) :
    ξ.innerAtoms L ↪ ξ.innerAtomsCod L :=
  ((Cardinal.le_def _ _).mp (mk_innerAtoms_lt hξ L hL).le).some

noncomputable irreducible_def outerAtomsEmbedding (ξ : NearLitterBehaviour) :
    ξ.allOuterAtoms ↪ litterSet ξ.sandboxLitter :=
  ((Cardinal.le_def _ _).mp (allOuterAtoms_small.le.trans
    (le_of_eq ((mk_litterSet _).symm)))).some

theorem eq_of_mem_innerAtoms {ξ : NearLitterBehaviour} (hξ : ξ.Lawful) (a : Atom)
    (ha : ¬(ξ.atomMap a).Dom) {L₁ L₂ : Litter}
    (hL₁ : ξ.LitterPresent L₁) (hL₂ : ξ.LitterPresent L₂)
    (ha₁ : a ∈ ξ.innerAtoms L₁) (ha₂ : a ∈ ξ.innerAtoms L₂) : L₁ = L₂ := by
  rw [mem_innerAtoms_iff L₁ hL₁] at ha₁
  rw [mem_innerAtoms_iff L₂ hL₂] at ha₂
  obtain ⟨N₁, hN₁, rfl⟩ := hL₁
  obtain ⟨N₂, hN₂, rfl⟩ := hL₂
  have h₁ := ha₁.2 N₁ ⟨hN₁, rfl⟩
  have h₂ := ha₂.2 N₂ ⟨hN₂, rfl⟩
  by_contra h
  exact ha (hξ.dom_of_mem_inter a h hN₁ hN₂ ⟨h₁, h₂⟩)

theorem innerAtoms_allOuterAtoms {ξ : NearLitterBehaviour} (a : Atom)
    {L : Litter} (hL : ξ.LitterPresent L)
    (ha₁ : a ∈ ξ.innerAtoms L) (ha₂ : a ∈ ξ.allOuterAtoms) : False := by
  rw [mem_innerAtoms_iff L hL] at ha₁
  rw [mem_allOuterAtoms_iff] at ha₂
  obtain ⟨N, hN, rfl⟩ := hL
  refine ha₂.2 N hN (ha₁.2 N ⟨hN, rfl⟩)

noncomputable def extraAtomMap (ξ : NearLitterBehaviour) (hξ : ξ.Lawful) : Atom →. Atom :=
  fun a => ⟨
    (ξ.atomMap a).Dom ∨ (∃ L, ξ.LitterPresent L ∧ a ∈ ξ.innerAtoms L) ∨
      a ∈ ξ.allOuterAtoms,
    fun h => h.elim' (ξ.atomMap a).get (fun h => h.elim'
      (fun h => ξ.innerAtomsEmbedding hξ _ h.choose_spec.1 ⟨a, h.choose_spec.2⟩)
      (fun h => ξ.outerAtomsEmbedding ⟨a, h⟩))⟩

theorem extraAtomMap_dom_small (ξ : NearLitterBehaviour) (hξ : ξ.Lawful) :
    Small (ξ.extraAtomMap hξ).Dom := by
  refine Small.union ξ.atomMap_dom_small (Small.union ?_ ξ.allOuterAtoms_small)
  suffices : Small (⋃ (L : Litter) (_ :  ξ.LitterPresent L), ξ.innerAtoms L)
  · refine Small.mono ?_ this
    rintro a ⟨L, hL, ha⟩
    exact ⟨_, ⟨L, rfl⟩, _, ⟨hL, rfl⟩, ha⟩
  refine Small.bUnion ξ.litterPresent_small ?_
  intro L hL
  exact ξ.innerAtoms_small L hL

theorem extraAtomMap_eq_of_dom {ξ : NearLitterBehaviour} {hξ : ξ.Lawful}
    (a : Atom) (ha : (ξ.atomMap a).Dom) :
    (ξ.extraAtomMap hξ a).get (Or.inl ha) = (ξ.atomMap a).get ha := by
  unfold extraAtomMap
  dsimp only
  rw [Or.elim'_left]

theorem extraAtomMap_eq_of_innerAtoms {ξ : NearLitterBehaviour} {hξ : ξ.Lawful}
    (a : Atom) (ha : ¬(ξ.atomMap a).Dom)
    (L : Litter) (hL : ξ.LitterPresent L) (ha' : a ∈ ξ.innerAtoms L) :
    (ξ.extraAtomMap hξ a).get (Or.inr (Or.inl ⟨L, hL, ha'⟩)) =
      ξ.innerAtomsEmbedding hξ L hL ⟨a, ha'⟩ := by
  unfold extraAtomMap
  dsimp only
  have : ∃ L, ξ.LitterPresent L ∧ a ∈ ξ.innerAtoms L := ⟨L, hL, ha'⟩
  rw [Or.elim'_right _ _ _ ha, Or.elim'_left _ _ _ this]
  have := eq_of_mem_innerAtoms hξ a ha hL this.choose_spec.1 ha' this.choose_spec.2
  subst this
  rfl

theorem extraAtomMap_eq_of_allOuterAtoms {ξ : NearLitterBehaviour} {hξ : ξ.Lawful}
    (a : Atom) (ha : ¬(ξ.atomMap a).Dom) (ha' : a ∈ ξ.allOuterAtoms) :
    (ξ.extraAtomMap hξ a).get (Or.inr (Or.inr ha')) = ξ.outerAtomsEmbedding ⟨a, ha'⟩ := by
  unfold extraAtomMap
  dsimp only
  rw [Or.elim'_right _ _ _ ha, Or.elim'_right]
  rintro ⟨L, hL₁, haL⟩
  exact innerAtoms_allOuterAtoms a hL₁ haL ha'

theorem innerAtomsEmbedding_ne_atomMap {ξ : NearLitterBehaviour} {hξ : ξ.Lawful}
    {a : Atom} (ha : (ξ.atomMap a).Dom)
    {L : Litter} {hL : ξ.LitterPresent L} (b : ξ.innerAtoms L) :
    (ξ.atomMap a).get ha ≠ ξ.innerAtomsEmbedding hξ L hL b := by
  intro h
  have := (ξ.innerAtomsEmbedding hξ L hL b).prop
  rw [← h] at this
  exact this.2 ⟨a, ha, rfl⟩

theorem outerAtomsEmbedding_ne_atomMap {ξ : NearLitterBehaviour}
    {a : Atom} (ha : (ξ.atomMap a).Dom) (b : ξ.allOuterAtoms) :
    (ξ.atomMap a).get ha ≠ ξ.outerAtomsEmbedding b := by
  intro h
  have := (ξ.outerAtomsEmbedding b).prop
  rw [← h] at this
  refine sandboxLitter_not_banned ξ ?_
  rw [← this]
  exact BannedLitter.atomMap a ha

theorem innerAtomsEmbedding_ne_outerAtomsEmbedding {ξ : NearLitterBehaviour} {hξ : ξ.Lawful}
    {L : Litter} {hL : ξ.LitterPresent L} (a : ξ.innerAtoms L) (b : ξ.allOuterAtoms) :
    (ξ.innerAtomsEmbedding hξ L hL a : Atom) ≠ ξ.outerAtomsEmbedding b := by
  intro h
  have := (ξ.outerAtomsEmbedding b).prop
  rw [← h] at this
  refine sandboxLitter_not_banned ξ ?_
  rw [← this]
  have := (ξ.innerAtomsEmbedding hξ L hL a).prop
  obtain ⟨N, hN, rfl⟩ := hL
  exact bannedLitter_of_mem _ _ _ (this.1 _ ⟨N, rfl⟩ _ ⟨⟨hN, rfl⟩, rfl⟩)

theorem innerAtomsEmbedding_disjoint {ξ : NearLitterBehaviour} {hξ : ξ.Lawful}
    {L₁ L₂ : Litter} {hL₁ : ξ.LitterPresent L₁} {hL₂ : ξ.LitterPresent L₂}
    (a₁ : ξ.innerAtoms L₁) (a₂ : ξ.innerAtoms L₂)
    (h : (ξ.innerAtomsEmbedding hξ L₁ hL₁ a₁ : Atom) = ξ.innerAtomsEmbedding hξ L₂ hL₂ a₂) :
    L₁ = L₂ := by
  have h₁ := (ξ.innerAtomsEmbedding hξ L₁ hL₁ a₁).prop
  have h₂ := (ξ.innerAtomsEmbedding hξ L₂ hL₂ a₂).prop
  obtain ⟨N₁, hN₁, rfl⟩ := hL₁
  obtain ⟨N₂, hN₂, rfl⟩ := hL₂
  rw [h] at h₁
  have h₁' := h₁.1 _ ⟨N₁, rfl⟩ _ ⟨⟨hN₁, rfl⟩, rfl⟩
  have h₂' := h₂.1 _ ⟨N₂, rfl⟩ _ ⟨⟨hN₂, rfl⟩, rfl⟩
  simp only [SetLike.mem_coe] at h₁' h₂'
  by_contra! h'
  exact h₁.2 (hξ.ran_of_mem_inter _ h' hN₁ hN₂ ⟨h₁', h₂'⟩)

theorem extraAtomMap_injective {ξ : NearLitterBehaviour} {hξ : ξ.Lawful} ⦃a b : Atom⦄
    (ha : (ξ.extraAtomMap hξ a).Dom) (hb : (ξ.extraAtomMap hξ b).Dom)
    (h : (ξ.extraAtomMap hξ a).get ha = (ξ.extraAtomMap hξ b).get hb) : a = b := by
  by_cases ha' : (ξ.atomMap a).Dom <;> by_cases hb' : (ξ.atomMap b).Dom
  · rw [extraAtomMap_eq_of_dom a ha', extraAtomMap_eq_of_dom b hb'] at h
    exact hξ.atomMap_injective ha' hb' h
  · obtain (hb | ⟨Lb, hLb₁, hLb₂⟩ | hb) := hb
    · cases hb' hb
    · rw [extraAtomMap_eq_of_dom a ha', extraAtomMap_eq_of_innerAtoms b hb' Lb hLb₁ hLb₂] at h
      cases innerAtomsEmbedding_ne_atomMap _ _ h
    · rw [extraAtomMap_eq_of_dom a ha', extraAtomMap_eq_of_allOuterAtoms b hb' hb] at h
      cases outerAtomsEmbedding_ne_atomMap _ _ h
  · obtain (ha | ⟨La, hLa₁, hLa₂⟩ | ha) := ha
    · cases ha' ha
    · rw [extraAtomMap_eq_of_innerAtoms a ha' La hLa₁ hLa₂, extraAtomMap_eq_of_dom b hb'] at h
      cases innerAtomsEmbedding_ne_atomMap _ _ h.symm
    · rw [extraAtomMap_eq_of_allOuterAtoms a ha' ha, extraAtomMap_eq_of_dom b hb'] at h
      cases outerAtomsEmbedding_ne_atomMap _ _ h.symm
  · obtain (ha | ⟨La, hLa₁, hLa₂⟩ | ha) := ha
    · cases ha' ha
    · obtain (hb | ⟨Lb, hLb₁, hLb₂⟩ | hb) := hb
      · cases hb' hb
      · rw [extraAtomMap_eq_of_innerAtoms a ha' La hLa₁ hLa₂,
          extraAtomMap_eq_of_innerAtoms b hb' Lb hLb₁ hLb₂] at h
        cases innerAtomsEmbedding_disjoint _ _ h
        cases (EmbeddingLike.apply_eq_iff_eq _).mp (Subtype.coe_injective h)
        rfl
      · rw [extraAtomMap_eq_of_innerAtoms a ha' La hLa₁ hLa₂,
          extraAtomMap_eq_of_allOuterAtoms b hb' hb] at h
        cases innerAtomsEmbedding_ne_outerAtomsEmbedding _ _ h
    · obtain (hb | ⟨Lb, hLb₁, hLb₂⟩ | hb) := hb
      · cases hb' hb
      · rw [extraAtomMap_eq_of_allOuterAtoms a ha' ha,
          extraAtomMap_eq_of_innerAtoms b hb' Lb hLb₁ hLb₂] at h
        cases innerAtomsEmbedding_ne_outerAtomsEmbedding _ _ h.symm
      · rw [extraAtomMap_eq_of_allOuterAtoms a ha' ha,
          extraAtomMap_eq_of_allOuterAtoms b hb' hb] at h
        cases (EmbeddingLike.apply_eq_iff_eq _).mp (Subtype.coe_injective h)
        rfl

theorem mem_iff_of_mem_innerAtoms {ξ : NearLitterBehaviour} (hξ : ξ.Lawful)
    {a : Atom} {L : Litter} (hL : ξ.LitterPresent L)
    (ha' : ¬(ξ.atomMap a).Dom) (ha : a ∈ ξ.innerAtoms L)
    {N : NearLitter} (hN : (ξ.nearLitterMap N).Dom) :
    a ∈ N ↔ N.1 = L := by
  constructor
  · intro h
    obtain ⟨N', hN', rfl⟩ := hL
    have := ha _ ⟨N', rfl⟩ _ ⟨⟨hN', rfl⟩, rfl⟩
    by_contra! hNN'
    exact ha' (hξ.dom_of_mem_inter _ hNN' hN hN' ⟨h, this.1⟩)
  · rintro rfl
    exact (ha _ ⟨N, rfl⟩ _ ⟨⟨hN, rfl⟩, rfl⟩).1

theorem extraAtomMap_mem_iff {ξ : NearLitterBehaviour} {hξ : ξ.Lawful}
    ⦃a : Atom⦄ (ha : (ξ.extraAtomMap hξ a).Dom)
    ⦃N : NearLitter⦄ (hN : (ξ.nearLitterMap N).Dom) :
    (ξ.extraAtomMap hξ a).get ha ∈ (ξ.nearLitterMap N).get hN ↔ a ∈ N := by
  by_cases ha' : (ξ.atomMap a).Dom
  · rw [extraAtomMap_eq_of_dom a ha']
    exact hξ.atom_mem_iff ha' hN
  obtain (ha | ⟨L, hL₁, hL₂⟩ | ha) := ha
  · cases ha' ha
  · rw [extraAtomMap_eq_of_innerAtoms a ha' L hL₁ hL₂,
      mem_iff_of_mem_innerAtoms hξ hL₁ ha' hL₂ hN]
    obtain ⟨N', hN', rfl⟩ := hL₁
    constructor
    · intro h
      by_contra hNN'
      have ha := (innerAtomsEmbedding hξ N'.1 ⟨N', hN', rfl⟩ ⟨a, hL₂⟩).prop.1
        _ ⟨N', rfl⟩ _ ⟨⟨hN', rfl⟩, rfl⟩
      exact (innerAtomsEmbedding hξ N'.1 ⟨N', hN', rfl⟩ ⟨a, hL₂⟩).prop.2
        (hξ.ran_of_mem_inter _ hNN' hN hN' ⟨h, ha⟩)
    · intro h
      exact (innerAtomsEmbedding hξ N'.1 ⟨N', hN', rfl⟩ ⟨a, hL₂⟩).prop.1
        _ ⟨N, rfl⟩ _ ⟨⟨hN, h⟩, rfl⟩
  · rw [extraAtomMap_eq_of_allOuterAtoms a ha' ha]
    constructor
    · intro h
      have := bannedLitter_of_mem _ _ _ h
      rw [(ξ.outerAtomsEmbedding ⟨a, ha⟩).prop] at this
      cases ξ.sandboxLitter_not_banned this
    · intro h
      obtain ⟨_, ⟨L, rfl⟩, _, ⟨hL, rfl⟩, ha⟩ := ha
      cases ha.2 ⟨_, ⟨N, rfl⟩, _, ⟨hN, rfl⟩, h⟩

theorem extraAtomMap_dom_of_mem_symmDiff {ξ : NearLitterBehaviour} (hξ : ξ.Lawful)
    {N : NearLitter} (hN : (ξ.nearLitterMap N).Dom) {a : Atom} (ha : a ∈ litterSet N.1 ∆ N) :
    (ξ.extraAtomMap hξ a).Dom := by
  by_cases ha' : (ξ.atomMap a).Dom
  · exact Or.inl ha'
  by_cases ha'' : ∃ N', (ξ.nearLitterMap N').Dom ∧ a ∈ N'
  · obtain ⟨N', hN', haN'⟩ := ha''
    refine Or.inr (Or.inl ?_)
    refine ⟨N'.1, ⟨N', hN', rfl⟩, ?_⟩
    rw [mem_innerAtoms_iff _ ⟨N', hN', rfl⟩]
    have : ∀ N'', (ξ.nearLitterMap N'').Dom ∧ N''.fst = N'.fst → a ∈ N''
    · intro N'' hN''
      by_contra haN''
      exact ha' (hξ.dom_of_mem_symmDiff a hN''.2 hN''.1 hN' (Or.inr ⟨haN', haN''⟩))
    refine ⟨?_, this⟩
    intro h
    obtain (ha | ha) := ha
    · refine ha.2 (this N ⟨hN, ?_⟩)
      rw [← ha.1, h]
    · refine ha' (hξ.dom_of_mem_inter a ?_ hN hN' ⟨ha.1, haN'⟩)
      rw [← h]
      exact Ne.symm ha.2
  · push_neg at ha''
    refine Or.inr (Or.inr ?_)
    simp only [mem_allOuterAtoms_iff]
    refine ⟨?_, ha''⟩
    obtain (ha | ha) := ha
    · rw [ha.1]
      exact ⟨N, hN, rfl⟩
    · cases ha'' N hN ha.1

theorem extraAtomMap_dom_of_mem_inter {ξ : NearLitterBehaviour} (hξ : ξ.Lawful)
    {N : NearLitter} (hN : (ξ.nearLitterMap N).Dom) {L : Litter}
    (h : N.1 ≠ L) {a : Atom} (ha₁ : a ∈ N) (ha₂ : a.1 = L) :
    (ξ.extraAtomMap hξ a).Dom := by
  by_cases ha' : (ξ.atomMap a).Dom
  · exact Or.inl ha'
  refine Or.inr (Or.inl ⟨_, ⟨N, hN, rfl⟩, ?_⟩)
  rw [mem_innerAtoms_iff _ ⟨N, hN, rfl⟩]
  constructor
  · rw [ha₂]
    exact h.symm
  · intro N' hN'
    by_contra ha''
    exact ha' (hξ.dom_of_mem_symmDiff a hN'.2 hN'.1 hN (Or.inr ⟨ha₁, ha''⟩))

def extraLitterMap' (ξ : NearLitterBehaviour) (hξ : ξ.Lawful)
    (N : NearLitter) (hN : (ξ.nearLitterMap N).Dom) : Set Atom :=
  (ξ.nearLitterMap N).get hN ∆
    ⋃ (a : Atom) (ha : a ∈ litterSet N.1 ∆ N),
      {(ξ.extraAtomMap hξ a).get (extraAtomMap_dom_of_mem_symmDiff hξ hN ha)}

theorem extraLitterMap'_subset {ξ : NearLitterBehaviour} {hξ : ξ.Lawful}
    {N₁ N₂ : NearLitter} (h : N₁.1 = N₂.1)
    (hN₁ : (ξ.nearLitterMap N₁).Dom) (hN₂ : (ξ.nearLitterMap N₂).Dom) :
    ξ.extraLitterMap' hξ N₁ hN₁ ⊆ ξ.extraLitterMap' hξ N₂ hN₂ := by
  rintro a (⟨ha₁, ha₂⟩ | ⟨ha₁, ha₂⟩)
  · simp only [mem_iUnion, mem_singleton_iff, not_exists] at ha₂
    by_cases ha₃ : a ∈ (ξ.nearLitterMap N₂).get hN₂
    · refine Or.inl ⟨ha₃, ?_⟩
      simp only [mem_iUnion, mem_singleton_iff, not_exists]
      rintro a ha rfl
      simp only [SetLike.mem_coe, extraAtomMap_mem_iff] at ha₁ ha₃
      obtain (ha | ha) := ha
      · cases ha.2 ha₃
      · refine ha₂ a (Or.inr ⟨ha₁, ?_⟩) rfl
        rw [h]
        exact ha.2
    · obtain ⟨a, ha', rfl⟩ := hξ.ran_of_mem_symmDiff a h hN₁ hN₂ (Or.inl ⟨ha₁, ha₃⟩)
      refine Or.inr ⟨?_, ha₃⟩
      simp only [mem_iUnion, mem_singleton_iff]
      simp only [SetLike.mem_coe, hξ.atom_mem_iff] at ha₁ ha₃
      have ha₄ : a.1 = N₁.1
      · by_contra ha₄
        refine ha₂ a (Or.inr ⟨ha₁, ha₄⟩) ?_
        rw [extraAtomMap_eq_of_dom]
      refine ⟨a, Or.inl ⟨ha₄.trans h, ha₃⟩, ?_⟩
      rw [extraAtomMap_eq_of_dom _ ha']
  · simp only [mem_iUnion, mem_singleton_iff] at ha₁
    obtain ⟨a, ha₁, rfl⟩ := ha₁
    rw [SetLike.mem_coe, extraAtomMap_mem_iff] at ha₂
    obtain (⟨ha₁, -⟩ | ⟨ha₁, -⟩) := ha₁
    · by_cases ha₃ : a ∈ N₂
      · refine Or.inl ⟨?_, ?_⟩
        · rw [SetLike.mem_coe, extraAtomMap_mem_iff]
          exact ha₃
        · simp only [mem_iUnion, mem_singleton_iff, not_exists]
          intro b hb hab
          cases extraAtomMap_injective _ _ hab
          obtain (hb | hb) := hb
          · cases hb.2 ha₃
          · rw [h] at ha₁
            cases hb.2 ha₁
      · refine Or.inr ⟨?_, ?_⟩
        · simp only [mem_iUnion, mem_singleton_iff]
          refine ⟨a, Or.inl ⟨?_, ha₃⟩, rfl⟩
          rw [← h]
          exact ha₁
        · rw [SetLike.mem_coe, extraAtomMap_mem_iff]
          exact ha₃
    · cases ha₂ ha₁

theorem extraLitterMap'_eq {ξ : NearLitterBehaviour} {hξ : ξ.Lawful}
    {N₁ N₂ : NearLitter} (h : N₁.1 = N₂.1)
    (hN₁ : (ξ.nearLitterMap N₁).Dom) (hN₂ : (ξ.nearLitterMap N₂).Dom) :
    ξ.extraLitterMap' hξ N₁ hN₁ = ξ.extraLitterMap' hξ N₂ hN₂ :=
  subset_antisymm (extraLitterMap'_subset h hN₁ hN₂) (extraLitterMap'_subset h.symm hN₂ hN₁)

theorem extraLitterMap'_isNearLitter {ξ : NearLitterBehaviour} (hξ : ξ.Lawful)
    {N : NearLitter} (hN : (ξ.nearLitterMap N).Dom) :
    IsNearLitter ((ξ.nearLitterMap N).get hN).1 (ξ.extraLitterMap' hξ N hN) := by
  rw [extraLitterMap']
  refine ((ξ.nearLitterMap N).get hN).2.prop.trans ?_
  erw [IsNear, symmDiff_symmDiff_cancel_left]
  refine Small.bUnion N.2.prop ?_
  intro a ha
  exact small_singleton _

theorem extraLitterMap'_disjoint {ξ : NearLitterBehaviour} {hξ : ξ.Lawful}
    {N₁ N₂ : NearLitter} (h : N₁.1 ≠ N₂.1)
    (hN₁ : (ξ.nearLitterMap N₁).Dom) (hN₂ : (ξ.nearLitterMap N₂).Dom) (a : Atom) :
    a ∉ ξ.extraLitterMap' hξ N₁ hN₁ ∩ ξ.extraLitterMap' hξ N₂ hN₂ := by
  intro h
  simp only [extraLitterMap', mem_inter_iff] at h
  obtain ⟨ha₁ | ha₁, ha₂ | ha₂⟩ := h
  · simp only [mem_diff, SetLike.mem_coe, mem_iUnion, mem_singleton_iff, not_exists] at ha₁ ha₂
    obtain ⟨a, ha, rfl⟩ := hξ.ran_of_mem_inter a h hN₁ hN₂ ⟨ha₁.1, ha₂.1⟩
    rw [hξ.atom_mem_iff] at ha₁ ha₂
    by_cases ha₃ : a.1 = N₁.1
    · refine ha₂.2 a (Or.inr ⟨ha₂.1, ?_⟩) ?_
      · rw [mem_litterSet, ha₃]
        exact h
      · rw [extraAtomMap_eq_of_dom]
    · refine ha₁.2 a (Or.inr ⟨ha₁.1, ha₃⟩) ?_
      rw [extraAtomMap_eq_of_dom]
  · simp only [mem_diff, SetLike.mem_coe, mem_iUnion, mem_singleton_iff, not_exists] at ha₁
    simp only [mem_diff, mem_iUnion, mem_singleton_iff, SetLike.mem_coe] at ha₂
    obtain ⟨⟨b, hb, rfl⟩, ha₂⟩ := ha₂
    rw [extraAtomMap_mem_iff] at ha₁ ha₂
    refine ha₁.2 b (Or.inr ⟨ha₁.1, ?_⟩) rfl
    obtain (hb | hb) := hb
    · rw [mem_litterSet, hb.1]
      exact h.symm
    · cases ha₂ hb.1
  · simp only [mem_diff, SetLike.mem_coe, mem_iUnion, mem_singleton_iff, not_exists] at ha₂
    simp only [mem_diff, mem_iUnion, mem_singleton_iff, SetLike.mem_coe] at ha₁
    obtain ⟨⟨b, hb, rfl⟩, ha₁⟩ := ha₁
    rw [extraAtomMap_mem_iff] at ha₁ ha₂
    refine ha₂.2 b (Or.inr ⟨ha₂.1, ?_⟩) rfl
    obtain (hb | hb) := hb
    · rw [mem_litterSet, hb.1]
      exact h
    · cases ha₁ hb.1
  · simp only [mem_diff, mem_iUnion, mem_singleton_iff, SetLike.mem_coe] at ha₁ ha₂
    obtain ⟨⟨b, hb, rfl⟩, ha₁⟩ := ha₁
    obtain ⟨⟨c, hc, hc'⟩, ha₂⟩ := ha₂
    cases extraAtomMap_injective _ _ hc'
    rw [extraAtomMap_mem_iff] at ha₁ ha₂
    obtain (hb | hb) := hb
    · obtain (hc | hc) := hc
      · cases h (hb.1.symm.trans hc.1)
      · cases ha₂ hc.1
    · cases ha₁ hb.1

def extraLitterMap (ξ : NearLitterBehaviour) (hξ : ξ.Lawful)
    (N : NearLitter) (hN : (ξ.nearLitterMap N).Dom) : NearLitter :=
  ⟨((ξ.nearLitterMap N).get hN).1, ξ.extraLitterMap' hξ N hN, extraLitterMap'_isNearLitter hξ hN⟩

theorem mem_extraLitterMap_iff {ξ : NearLitterBehaviour} {hξ : ξ.Lawful}
    {N : NearLitter} {hN : (ξ.nearLitterMap N).Dom} (a : Atom) :
    a ∈ ξ.extraLitterMap hξ N hN ↔ a ∈ ξ.extraLitterMap' hξ N hN :=
  Iff.rfl

theorem extraLitterMap_eq {ξ : NearLitterBehaviour} {hξ : ξ.Lawful}
    {N₁ N₂ : NearLitter} (h : N₁.1 = N₂.1)
    (hN₁ : (ξ.nearLitterMap N₁).Dom) (hN₂ : (ξ.nearLitterMap N₂).Dom) :
    ξ.extraLitterMap hξ N₁ hN₁ = ξ.extraLitterMap hξ N₂ hN₂ :=
  NearLitter.ext (extraLitterMap'_eq h hN₁ hN₂)

noncomputable def withLitters (ξ : NearLitterBehaviour) (hξ : ξ.Lawful) : NearLitterBehaviour where
  atomMap := ξ.extraAtomMap hξ
  nearLitterMap N := ⟨(ξ.nearLitterMap N).Dom ∨ (N.IsLitter ∧ ξ.LitterPresent N.1),
    fun h => h.elim'
      (ξ.nearLitterMap N).get
      (fun h => ξ.extraLitterMap hξ h.2.choose h.2.choose_spec.1)⟩
  atomMap_dom_small := ξ.extraAtomMap_dom_small hξ
  nearLitterMap_dom_small := Small.union ξ.nearLitterMap_dom_small ξ.litterPresent_small'

theorem withLitters_nearLitterMap_of_dom {ξ : NearLitterBehaviour} (hξ : ξ.Lawful)
    {N : NearLitter} (hN : (ξ.nearLitterMap N).Dom) :
    ((ξ.withLitters hξ).nearLitterMap N).get (Or.inl hN) = (ξ.nearLitterMap N).get hN := by
  unfold withLitters
  dsimp only
  rw [Or.elim'_left]

theorem withLitters_nearLitterMap_fst {ξ : NearLitterBehaviour} (hξ : ξ.Lawful)
    {N : NearLitter} (hN : (ξ.nearLitterMap N).Dom) :
    ((ξ.withLitters hξ).nearLitterMap N.1.toNearLitter).get (Or.inr ⟨⟨_⟩, N, hN, rfl⟩) =
      ξ.extraLitterMap hξ N hN := by
  by_cases hN' : (ξ.nearLitterMap N.1.toNearLitter).Dom
  · rw [withLitters_nearLitterMap_of_dom hξ hN', extraLitterMap_eq (by rfl) hN hN', extraLitterMap]
    refine NearLitter.ext ?_
    simp only [extraLitterMap', Litter.toNearLitter_fst, Litter.coe_toNearLitter,
      symmDiff_self, bot_eq_empty, mem_empty_iff_false, iUnion_of_empty, iUnion_empty,
      symmDiff_empty, NearLitter.coe_mk]
  · unfold withLitters
    dsimp only
    rw [Or.elim'_right _ _ _ hN']
    have : ξ.LitterPresent N.1 := ⟨N, hN, rfl⟩
    rw [extraLitterMap_eq this.choose_spec.2 this.choose_spec.1 hN]

theorem extraAtomMap_mem_iff' {ξ : NearLitterBehaviour} {hξ : Lawful ξ}
    {a : Atom} (ha : (ξ.extraAtomMap hξ a).Dom)
    {N : NearLitter} (hN : (ξ.nearLitterMap N).Dom) :
    (ξ.extraAtomMap hξ a).get ha ∈ ξ.extraLitterMap hξ N hN ↔ a.1 = N.1 := by
  rw [mem_extraLitterMap_iff, extraLitterMap']
  constructor
  · rintro (⟨ha₁, ha₂⟩ | ⟨ha₁, ha₂⟩)
    · rw [SetLike.mem_coe, extraAtomMap_mem_iff] at ha₁
      contrapose! ha₂
      simp only [mem_iUnion, mem_singleton_iff]
      exact ⟨a, Or.inr ⟨ha₁, ha₂⟩, rfl⟩
    · rw [SetLike.mem_coe, extraAtomMap_mem_iff] at ha₂
      simp only [mem_iUnion, mem_singleton_iff] at ha₁
      obtain ⟨b, hb, hab⟩ := ha₁
      cases extraAtomMap_injective _ _ hab
      obtain (hb | hb) := hb
      · exact hb.1
      · cases ha₂ hb.1
  · intro ha₁
    by_cases ha₂ : a ∈ N
    · refine Or.inl ⟨?_, ?_⟩
      · rw [SetLike.mem_coe, extraAtomMap_mem_iff]
        exact ha₂
      · simp only [mem_iUnion, mem_singleton_iff, not_exists]
        intro b hb hab
        cases extraAtomMap_injective _ _ hab
        obtain (hb | hb) := hb
        · cases hb.2 ha₂
        · cases hb.2 ha₁
    · refine Or.inr ⟨?_, ?_⟩
      · simp only [mem_iUnion, mem_singleton_iff]
        exact ⟨a, Or.inl ⟨ha₁, ha₂⟩, rfl⟩
      · rw [SetLike.mem_coe, extraAtomMap_mem_iff]
        exact ha₂

theorem extraAtomMap_ran_of_mem_symmDiff {ξ : NearLitterBehaviour} (hξ : ξ.Lawful)
    {N₁ N₂ : NearLitter} (hN₁ : (ξ.nearLitterMap N₁).Dom) (hN₂ : (ξ.nearLitterMap N₂).Dom)
    (hN : N₁.fst = (Litter.toNearLitter N₂.1).fst)
    {a : Atom} (ha : a ∈ ((ξ.nearLitterMap N₁).get hN₁ : Set Atom) ∆ ξ.extraLitterMap' hξ N₂ hN₂) :
    a ∈ (ξ.extraAtomMap hξ).ran := by
  obtain (⟨ha₁, ha₂⟩ | ⟨ha₁, ha₂⟩) := ha
  · contrapose! ha₂
    have ha' : a ∈ (ξ.nearLitterMap N₂).get hN₂
    · by_contra ha'
      obtain ⟨b, hb, rfl⟩ := hξ.ran_of_mem_symmDiff a (by exact hN) hN₁ hN₂ (Or.inl ⟨ha₁, ha'⟩)
      refine ha₂ ⟨b, Or.inl hb, ?_⟩
      rw [extraAtomMap_eq_of_dom]
    refine Or.inl ⟨ha', ?_⟩
    simp only [mem_iUnion, mem_singleton_iff, not_exists]
    rintro b hb rfl
    exact ha₂ ⟨b, _, rfl⟩
  · obtain (⟨ha₁, ha₃⟩ | ⟨ha₁, ha₃⟩) := ha₁
    · simp only [mem_iUnion, mem_singleton_iff, not_exists] at ha₃
      obtain ⟨b, hb, rfl⟩ := hξ.ran_of_mem_symmDiff a (by exact hN) hN₁ hN₂ (Or.inr ⟨ha₁, ha₂⟩)
      refine ⟨b, Or.inl hb, ?_⟩
      rw [extraAtomMap_eq_of_dom]
    · simp only [mem_iUnion, mem_singleton_iff] at ha₁
      obtain ⟨b, hb, rfl⟩ := ha₁
      exact ⟨_, _, rfl⟩

theorem extraAtomMap_ran_of_mem_inter {ξ : NearLitterBehaviour} (hξ : ξ.Lawful)
    {N₁ N₂ : NearLitter} (hN₁ : (ξ.nearLitterMap N₁).Dom) (hN₂ : (ξ.nearLitterMap N₂).Dom)
    (hN : N₁.fst ≠ (Litter.toNearLitter N₂.1).fst)
    {a : Atom} (ha : a ∈ ((ξ.nearLitterMap N₁).get hN₁ : Set Atom) ∩ ξ.extraLitterMap' hξ N₂ hN₂) :
    a ∈ (ξ.extraAtomMap hξ).ran := by
  obtain ⟨ha₁, ⟨ha₂, ha₃⟩ | ⟨ha₂, ha₃⟩⟩ := ha
  · simp only [mem_iUnion, mem_singleton_iff, not_exists] at ha₃
    obtain ⟨b, hb, rfl⟩ := hξ.ran_of_mem_inter a (by exact hN) hN₁ hN₂ ⟨ha₁, ha₂⟩
    refine ⟨b, Or.inl hb, ?_⟩
    rw [extraAtomMap_eq_of_dom]
  · simp only [mem_iUnion, mem_singleton_iff] at ha₂
    obtain ⟨b, hb, rfl⟩ := ha₂
    rw [SetLike.mem_coe, extraAtomMap_mem_iff] at ha₁ ha₃
    exact ⟨b, _, rfl⟩

theorem withLitters_lawful (ξ : NearLitterBehaviour) (hξ : ξ.Lawful) :
    (ξ.withLitters hξ).Lawful := by
  constructor
  case atomMap_injective => exact extraAtomMap_injective
  case atom_mem_iff =>
    rintro a ha N (hN | ⟨⟨_⟩, ⟨N, hN, hN'⟩⟩)
    · rw [withLitters_nearLitterMap_of_dom hξ hN]
      exact extraAtomMap_mem_iff ha hN
    · cases hN'
      rw [withLitters_nearLitterMap_fst hξ hN]
      exact extraAtomMap_mem_iff' ha hN
  case dom_of_mem_symmDiff =>
    rintro a N₁ N₂ h (hN₁ | ⟨⟨_⟩, ⟨N₁, -, hN₁'⟩⟩) (hN₂ | ⟨⟨_⟩, ⟨N₂, -, hN₂'⟩⟩) ha
    · exact Or.inl (hξ.dom_of_mem_symmDiff a h hN₁ hN₂ ha)
    · cases hN₂'
      refine extraAtomMap_dom_of_mem_symmDiff hξ hN₁ ?_
      rw [h]
      rw [symmDiff_comm] at ha
      exact ha
    · cases hN₁'
      refine extraAtomMap_dom_of_mem_symmDiff hξ hN₂ ?_
      rw [← h]
      exact ha
    · cases hN₁'
      cases hN₂'
      rw [Litter.toNearLitter_fst] at h
      obtain (ha | ha) := ha
      · rw [h] at ha
        cases ha.2 ha.1
      · rw [h] at ha
        cases ha.2 ha.1
  case dom_of_mem_inter =>
    rintro a N₁ N₂ h (hN₁ | ⟨⟨_⟩, ⟨N₁, -, hN₁'⟩⟩) (hN₂ | ⟨⟨_⟩, ⟨N₂, -, hN₂'⟩⟩) ha
    · exact Or.inl (hξ.dom_of_mem_inter a h hN₁ hN₂ ha)
    · cases hN₂'
      exact extraAtomMap_dom_of_mem_inter hξ hN₁ h ha.1 ha.2
    · cases hN₁'
      exact extraAtomMap_dom_of_mem_inter hξ hN₂ h.symm ha.2 ha.1
    · cases hN₁'
      cases hN₂'
      simp only [Litter.toNearLitter_fst, ne_eq] at h
      cases h (ha.1.symm.trans ha.2)
  case ran_of_mem_symmDiff =>
    rintro a N₁ N₂ h (hN₁ | ⟨⟨_⟩, ⟨N₁, hN₁, hN₁'⟩⟩) (hN₂ | ⟨⟨_⟩, ⟨N₂, hN₂, hN₂'⟩⟩) ha
    · rw [withLitters_nearLitterMap_of_dom hξ hN₁, withLitters_nearLitterMap_of_dom hξ hN₂] at ha
      obtain ⟨b, hb, rfl⟩ := hξ.ran_of_mem_symmDiff a h hN₁ hN₂ ha
      refine ⟨b, Or.inl hb, ?_⟩
      simp only [withLitters, extraAtomMap_eq_of_dom _ hb]
    · cases hN₂'
      refine extraAtomMap_ran_of_mem_symmDiff hξ hN₁ hN₂ h ?_
      rw [withLitters_nearLitterMap_of_dom hξ hN₁,
        withLitters_nearLitterMap_fst hξ hN₂] at ha
      exact ha
    · cases hN₁'
      refine extraAtomMap_ran_of_mem_symmDiff hξ hN₂ hN₁ h.symm ?_
      rw [withLitters_nearLitterMap_of_dom hξ hN₂,
        withLitters_nearLitterMap_fst hξ hN₁, symmDiff_comm] at ha
      exact ha
    · cases hN₁'
      cases hN₂'
      rw [Litter.toNearLitter_fst] at h
      simp only [h, Litter.toNearLitter_fst, symmDiff_self, bot_eq_empty, mem_empty_iff_false] at ha
  case ran_of_mem_inter =>
    rintro a N₁ N₂ h (hN₁ | ⟨⟨_⟩, ⟨N₁, hN₁, hN₁'⟩⟩) (hN₂ | ⟨⟨_⟩, ⟨N₂, hN₂, hN₂'⟩⟩) ha
    · rw [withLitters_nearLitterMap_of_dom hξ hN₁, withLitters_nearLitterMap_of_dom hξ hN₂] at ha
      obtain ⟨b, hb, rfl⟩ := hξ.ran_of_mem_inter a h hN₁ hN₂ ha
      refine ⟨b, Or.inl hb, ?_⟩
      simp only [withLitters, extraAtomMap_eq_of_dom _ hb]
    · cases hN₂'
      refine extraAtomMap_ran_of_mem_inter hξ hN₁ hN₂ h ?_
      rw [withLitters_nearLitterMap_of_dom hξ hN₁,
        withLitters_nearLitterMap_fst hξ hN₂] at ha
      exact ha
    · cases hN₁'
      refine extraAtomMap_ran_of_mem_inter hξ hN₂ hN₁ h.symm ?_
      rw [withLitters_nearLitterMap_of_dom hξ hN₂,
        withLitters_nearLitterMap_fst hξ hN₁, inter_comm] at ha
      exact ha
    · cases hN₁'
      cases hN₂'
      simp only [mem_inter_iff, SetLike.mem_coe,
        withLitters_nearLitterMap_fst hξ hN₁, withLitters_nearLitterMap_fst hξ hN₂,
        mem_extraLitterMap_iff] at ha
      cases extraLitterMap'_disjoint (by exact h) hN₁ hN₂ a ha

end NearLitterBehaviour

end ConNF
