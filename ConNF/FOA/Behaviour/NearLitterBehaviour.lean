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
  ran_of_mem_symmDiff : ∀ (a : Atom) ⦃N₁ N₂ : NearLitter⦄,
    N₁.fst = N₂.fst → (hN₁ : (ξ.nearLitterMap N₁).Dom) → (hN₂ : (ξ.nearLitterMap N₂).Dom) →
    a ∈ ((ξ.nearLitterMap N₁).get hN₁ : Set Atom) ∆ (ξ.nearLitterMap N₂).get hN₂ →
    a ∈ ξ.atomMap.ran

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
  ⋃ (N ∈ ξ.nearLitterMap.Dom), litterSet N.1 ∆ N

theorem extraAtoms_small (ξ : NearLitterBehaviour) : Small ξ.extraAtoms :=
  Small.bUnion ξ.nearLitterMap_dom_small (fun N _ => N.2.2)

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

noncomputable irreducible_def extraAtoms_embedding (ξ : NearLitterBehaviour) :
    ξ.extraAtoms ↪ litterSet ξ.sandboxLitter :=
  ((Cardinal.le_def _ _).mp (ξ.extraAtoms_small.le.trans (mk_litterSet _).symm.le)).some

theorem extraAtoms_embedding_fst {ξ : NearLitterBehaviour} (a : ξ.extraAtoms) :
    ¬ξ.BannedLitter (ξ.extraAtoms_embedding a).1.1 := by
  rw [(ξ.extraAtoms_embedding a).prop]
  exact ξ.sandboxLitter_not_banned

noncomputable def extraAtomMap (ξ : NearLitterBehaviour) : Atom →. Atom :=
  fun a => ⟨(ξ.atomMap a).Dom ∨ a ∈ ξ.extraAtoms,
    fun h => h.elim' (ξ.atomMap a).get (fun h => ξ.extraAtoms_embedding ⟨a, h⟩)⟩

variable {ξ : NearLitterBehaviour}

theorem extraAtomMap_eq_of_dom (a : Atom) (ha : (ξ.atomMap a).Dom) :
    (ξ.extraAtomMap a).get (Or.inl ha) = (ξ.atomMap a).get ha := by
  dsimp only [extraAtomMap]
  rw [Or.elim'_left]

theorem extraAtomMap_eq_of_not_dom (a : Atom) (ha₁ : ¬(ξ.atomMap a).Dom) (ha₂ : a ∈ ξ.extraAtoms) :
    (ξ.extraAtomMap a).get (Or.inr ha₂) = ξ.extraAtoms_embedding ⟨a, ha₂⟩ := by
  dsimp only [extraAtomMap]
  rw [Or.elim'_right _ _ _ ha₁]

theorem atomMap_eq_extraAtomMap (a b : Atom)
    (ha : (ξ.atomMap a).Dom) (hb : (ξ.extraAtomMap b).Dom)
    (h : (ξ.atomMap a).get ha = (ξ.extraAtomMap b).get hb) :
    (ξ.atomMap b).Dom := by
  by_contra hb₁
  have hb₂ := hb.elim (fun h => (hb₁ h).elim) id
  rw [extraAtomMap_eq_of_not_dom b hb₁ hb₂] at h
  have := extraAtoms_embedding_fst ⟨b, hb₂⟩
  rw [← h] at this
  exact this (BannedLitter.atomMap a ha)

/-- Works out where `N.1.toNearLitter` should be sent. -/
def litterMap' (N : NearLitter) (hN : (ξ.nearLitterMap N).Dom) : Set Atom :=
  (ξ.nearLitterMap N).get hN ∆
    {b | ∃ a, ∃ (ha : a ∈ litterSet N.1 ∆ N),
      b = (ξ.extraAtomMap a).get (Or.inr ⟨_, ⟨N, rfl⟩, _, ⟨hN, rfl⟩, ha⟩)}

theorem litterMap'_isNearLitter (N : NearLitter) (hN : (ξ.nearLitterMap N).Dom) :
    IsNearLitter ((ξ.nearLitterMap N).get hN).fst (litterMap' N hN) := by
  refine ((ξ.nearLitterMap N).get hN).snd.prop.trans ?_
  rw [IsNear, litterMap']
  erw [symmDiff_symmDiff_cancel_left]
  have : {b | ∃ a, ∃ (ha : a ∈ litterSet N.1 ∆ N),
      b = (ξ.extraAtomMap a).get (Or.inr ⟨_, ⟨N, rfl⟩, _, ⟨hN, rfl⟩, ha⟩)}
    = ⋃ (a : Atom), ⋃ (ha : a ∈ litterSet N.1 ∆ N),
      {(ξ.extraAtomMap a).get (Or.inr ⟨_, ⟨N, rfl⟩, _, ⟨hN, rfl⟩, ha⟩)} := by aesop
  rw [this]
  exact Small.bUnion N.snd.prop (fun _ _ => small_singleton _)

def litterMap (N : NearLitter) (hN : (ξ.nearLitterMap N).Dom) : NearLitter :=
  ⟨((ξ.nearLitterMap N).get hN).1, litterMap' N hN, litterMap'_isNearLitter N hN⟩

theorem litterMap'_subset (hξ : ξ.Lawful) (N₁ N₂ : NearLitter)
    (hN₁ : (ξ.nearLitterMap N₁).Dom) (hN₂ : (ξ.nearLitterMap N₂).Dom) (h : N₁.fst = N₂.fst) :
    ξ.litterMap' N₁ hN₁ ⊆ ξ.litterMap' N₂ hN₂ := by
  rintro a (⟨h₁, h₂⟩ | ⟨⟨a, h₁, rfl⟩, h₂⟩)
  · simp only [mem_setOf_eq, not_exists] at h₂
    by_cases h₃ : a ∈ (ξ.nearLitterMap N₂).get hN₂
    · refine Or.inl ⟨h₃, ?_⟩
      rintro ⟨a, ha, rfl⟩
      by_cases h₄ : (ξ.atomMap a).Dom
      · erw [extraAtomMap_eq_of_dom _ h₄, hξ.atom_mem_iff] at h₁ h₃
        obtain (ha | ha) := ha
        · cases ha.2 h₃
        · rw [← h] at ha
          cases h₂ a (Or.inr ⟨h₁, ha.2⟩) rfl
      · have ha : a ∈ ξ.extraAtoms := ⟨_, ⟨N₂, rfl⟩, _, ⟨hN₂, rfl⟩, ha⟩
        rw [extraAtomMap_eq_of_not_dom _ h₄ ha] at h₁
        exact extraAtoms_embedding_fst ⟨a, ha⟩ (bannedLitter_of_mem _ _ _ h₁)
    · refine Or.inr ⟨?_, h₃⟩
      obtain ⟨a, ha, rfl⟩ := hξ.ran_of_mem_symmDiff a h hN₁ hN₂ (Or.inl ⟨h₁, h₃⟩)
      refine ⟨a, ?_, ?_⟩
      · erw [hξ.atom_mem_iff] at h₁ h₃
        refine Or.inl ⟨?_, h₃⟩
        rw [← h]
        by_contra h₄
        refine h₂ a (Or.inr ⟨h₁, h₄⟩) ?_
        rw [extraAtomMap_eq_of_dom]
      · rw [extraAtomMap_eq_of_dom]
  · have ha : a ∈ ξ.extraAtoms := ⟨_, ⟨N₁, rfl⟩, _, ⟨hN₁, rfl⟩, h₁⟩
    by_cases h₃ : (ξ.extraAtomMap a).get (Or.inr ha) ∈ (ξ.nearLitterMap N₂).get hN₂
    · refine Or.inl ⟨h₃, ?_⟩
      simp only [mem_setOf_eq, not_exists]
      intro b hb hab
      by_cases h₄ : (ξ.atomMap a).Dom
      · rw [extraAtomMap_eq_of_dom _ h₄] at h₂ h₃ hab
        erw [hξ.atom_mem_iff] at h₂ h₃
        have h₅ := atomMap_eq_extraAtomMap a b _ _ hab
        rw [extraAtomMap_eq_of_dom _ h₅] at hab
        cases hξ.atomMap_injective _ _ hab
        obtain (h₁ | h₁) := h₁
        · obtain (hb | hb) := hb
          · cases hb.2 h₃
          · rw [h] at h₁
            cases hb.2 h₁.1
        · cases h₂ h₁.1
      · rw [extraAtomMap_eq_of_not_dom _ h₄ ha] at h₃
        exact extraAtoms_embedding_fst ⟨a, ha⟩ (bannedLitter_of_mem _ _ hN₂ h₃)
    · refine Or.inr ⟨?_, h₃⟩
      refine ⟨a, ?_, rfl⟩
      by_cases h₄ : (ξ.atomMap a).Dom
      · erw [extraAtomMap_eq_of_dom _ h₄, hξ.atom_mem_iff] at h₂ h₃
        obtain (h₁ | h₁) := h₁
        · refine Or.inl ⟨?_, h₃⟩
          rw [h] at h₁
          exact h₁.1
        · cases h₂ h₁.1
      · obtain (h₁ | h₁) := h₁
        · by_cases h₅ : a ∈ N₂
          · cases h₄ (hξ.dom_of_mem_symmDiff a h hN₁ hN₂ (Or.inr ⟨h₅, h₁.2⟩))
          · refine Or.inl ⟨?_, h₅⟩
            rw [← h]
            exact h₁.1
        · by_cases h₅ : a ∈ N₂
          · refine Or.inr ⟨h₅, ?_⟩
            rw [← h]
            exact h₁.2
          · cases h₄ (hξ.dom_of_mem_symmDiff a h hN₁ hN₂ (Or.inl ⟨h₁.1, h₅⟩))

theorem litterMap_eq (hξ : ξ.Lawful) (N₁ N₂ : NearLitter)
    (hN₁ : (ξ.nearLitterMap N₁).Dom) (hN₂ : (ξ.nearLitterMap N₂).Dom) (h : N₁.fst = N₂.fst) :
    ξ.litterMap N₁ hN₁ = ξ.litterMap N₂ hN₂ := by
  refine NearLitter.ext (subset_antisymm ?_ ?_)
  · exact litterMap'_subset hξ _ _ _ _ h
  · exact litterMap'_subset hξ _ _ _ _ h.symm

noncomputable def extendedNearLitterMap (ξ : NearLitterBehaviour) : NearLitter →. NearLitter :=
  fun N =>
    ⟨(ξ.nearLitterMap N).Dom ∨ (N.IsLitter ∧ ∃ N', (ξ.nearLitterMap N').Dom ∧ N'.1 = N.1),
      fun h => h.elim' (ξ.nearLitterMap N).get (fun h => ξ.litterMap h.2.choose h.2.choose_spec.1)⟩

noncomputable def withLitters (ξ : NearLitterBehaviour) : NearLitterBehaviour where
  atomMap := ξ.extraAtomMap
  nearLitterMap := ξ.extendedNearLitterMap
  atomMap_dom_small := sorry
  nearLitterMap_dom_small := sorry

theorem withLitters_lawful (ξ : NearLitterBehaviour) (hξ : ξ.Lawful) :
    ξ.withLitters.Lawful :=
  sorry

theorem withLitters_hasLitters (ξ : NearLitterBehaviour) (hξ : ξ.Lawful) :
    ξ.withLitters.HasLitters :=
  sorry

end NearLitterBehaviour

end ConNF
