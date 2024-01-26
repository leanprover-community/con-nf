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
  -- map_nearLitter_fst : ∀ ⦃N₁ N₂ : NearLitter⦄
  --   (hN₁ : (ξ.nearLitterMap N₁).Dom) (hN₂ : (ξ.nearLitterMap N₂).Dom),
  --   N₁.fst = N₂.fst ↔ ((ξ.nearLitterMap N₁).get hN₁).fst = ((ξ.nearLitterMap N₂).get hN₂).fst
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
  -- ran_of_mem_inter : ∀ (a : Atom) ⦃N₁ N₂ : NearLitter⦄,
  --   N₁.fst ≠ N₂.fst → (hN₁ : (ξ.nearLitterMap N₁).Dom) → (hN₂ : (ξ.nearLitterMap N₂).Dom) →
  --   a ∈ ((ξ.nearLitterMap N₁).get hN₁ : Set Atom) ∩ (ξ.nearLitterMap N₂).get hN₂ →
  --   a ∈ ξ.atomMap.ran

instance : PartialOrder NearLitterBehaviour
    where
  le ξ ξ' := ξ.atomMap ≤ ξ'.atomMap ∧ ξ.nearLitterMap ≤ ξ'.nearLitterMap
  le_refl ξ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm := by
    intro ξ ξ' h₁ h₂
    ext : 1
    exact le_antisymm h₁.1 h₂.1
    exact le_antisymm h₁.2 h₂.2

def HasLitters (ξ : NearLitterBehaviour) : Prop :=
  ∀ ⦃N : NearLitter⦄, (ξ.nearLitterMap N).Dom → (ξ.nearLitterMap N.1.toNearLitter).Dom

def action (ξ : NearLitterBehaviour) : NearLitterAction where
  atomMap := ξ.atomMap
  litterMap L := ξ.nearLitterMap L.toNearLitter
  atomMap_dom_small := ξ.atomMap_dom_small
  litterMap_dom_small := Small.preimage (fun _ _ => congr_arg Sigma.fst) (ξ.nearLitterMap_dom_small)

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
  ⋂ (N : NearLitter) (hN : (ξ.nearLitterMap N).Dom ∧ N.1 = L), (ξ.nearLitterMap N).get hN.1

@[simp]
theorem mem_innerAtomsCod_iff {ξ : NearLitterBehaviour} (L : Litter) (a : Atom) :
    a ∈ ξ.innerAtomsCod L ↔ ∀ N (hN : (ξ.nearLitterMap N).Dom ∧ N.1 = L),
    a ∈ (ξ.nearLitterMap N).get hN.1 :=
  by simp only [innerAtomsCod, mem_iInter, SetLike.mem_coe]

theorem innerAtomsCod_subset (ξ : NearLitterBehaviour)
    (N : NearLitter) (hN : (ξ.nearLitterMap N).Dom) :
    ξ.innerAtomsCod N.1 ⊆ (ξ.nearLitterMap N).get hN := by
  intro a ha
  refine ha _ ⟨N, subset_antisymm ?_ ?_⟩
  · intro a' ha'
    exact ha' _ ⟨⟨hN, rfl⟩, rfl⟩
  · rintro a' ha' _ ⟨_, rfl⟩
    exact ha'

theorem innerAtomsCod_eq {ξ : NearLitterBehaviour}
    (N : NearLitter) (hN : (ξ.nearLitterMap N).Dom) :
    ξ.innerAtomsCod N.1 = ((ξ.nearLitterMap N).get hN : Set Atom) \
      ⋃ (N' : NearLitter) (hN' : (ξ.nearLitterMap N').Dom ∧ N'.1 = N.1),
        (ξ.nearLitterMap N').get hN'.1 ∆ (ξ.nearLitterMap N).get hN := by
  refine subset_antisymm ?_ ?_
  · intro a ha
    rw [mem_innerAtomsCod_iff] at ha
    refine ⟨ha _ ⟨hN, rfl⟩, ?_⟩
    rintro ⟨_, ⟨N', rfl⟩, _, ⟨hN', rfl⟩, ha' | ha'⟩ <;> aesop
  · intro a ha
    rw [mem_innerAtomsCod_iff]
    obtain ⟨ha₁, ha₂⟩ := ha
    intro N' hN'
    contrapose! ha₂
    exact ⟨_, ⟨N', rfl⟩, _, ⟨hN', rfl⟩, Or.inr ⟨ha₁, ha₂⟩⟩

theorem innerAtomsCod_eq_aux {ξ : NearLitterBehaviour} (hξ : ξ.Lawful)
    (N : NearLitter) (hN : (ξ.nearLitterMap N).Dom) :
    Small (⋃ (N' : NearLitter) (hN' : (ξ.nearLitterMap N').Dom ∧ N'.1 = N.1),
      (ξ.nearLitterMap N').get hN'.1 ∆ (ξ.nearLitterMap N).get hN : Set Atom) := by
  refine Small.bUnion ?_ ?_
  · exact Small.mono (fun _ h => h.1) ξ.nearLitterMap_dom_small
  · intro N' hN'
    refine Small.mono ?_ (Small.pFun_image ξ.atomMap_dom_small (f := ξ.atomMap))
    intro a ha
    obtain ⟨b, hb₁, hb₂⟩ := hξ.ran_of_mem_symmDiff a hN'.2 hN'.1 hN ha
    exact ⟨b, hb₁, hb₁, hb₂⟩

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
    (ξ.extraAtomMap hξ a).get (Or.inr (Or.inr  ha')) = ξ.outerAtomsEmbedding ⟨a, ha'⟩ := by
  unfold extraAtomMap
  dsimp only
  rw [Or.elim'_right _ _ _ ha, Or.elim'_right]
  rintro ⟨L, hL₁, haL⟩
  exact innerAtoms_allOuterAtoms a hL₁ haL ha'

theorem extraAtomMap_injective {ξ : NearLitterBehaviour} {hξ : ξ.Lawful} ⦃a b : Atom⦄
    (ha : (ξ.extraAtomMap hξ a).Dom) (hb : (ξ.extraAtomMap hξ b).Dom)
    (h : (ξ.extraAtomMap hξ a).get ha = (ξ.extraAtomMap hξ b).get hb) : a = b := by
  -- by_cases ha' : (ξ.atomMap a).Dom <;> by_cases hb' : (ξ.atomMap b).Dom
  sorry

end NearLitterBehaviour

end ConNF
