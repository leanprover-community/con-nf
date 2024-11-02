import ConNF.Counting.SpecSame

/-!
# Coding the base type

In this file, we prove a consequence of freedom of action for `⊥`: a base support can support at
most `2 ^ #κ`-many different sets of atoms under the action of base permutations.

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}]

def addAtom' (S : BaseSupport) (a : Atom) : BaseSupport where
  atoms := Sᴬ + .singleton a
  nearLitters := Sᴺ

theorem addAtom'_atoms (S : BaseSupport) (a : Atom) :
    (addAtom' S a)ᴬ = Sᴬ + .singleton a :=
  rfl

theorem addAtom'_nearLitters (S : BaseSupport) (a : Atom) :
    (addAtom' S a)ᴺ = Sᴺ :=
  rfl

theorem addAtom'_atoms_rel (S : BaseSupport) (a : Atom) (i : κ) (b : Atom) :
    (addAtom' S a)ᴬ.rel i b ↔ Sᴬ.rel i b ∨ (b = a ∧ i = Sᴬ.bound) := by
  constructor
  · rintro (hb | ⟨_, rfl, rfl, rfl⟩)
    · exact Or.inl hb
    · refine Or.inr ⟨rfl, ?_⟩
      simp only [add_zero]
  · rintro (hb | ⟨rfl, rfl⟩)
    · exact Or.inl hb
    · refine Or.inr ⟨0, ?_, rfl, rfl⟩
      simp only [Rel.inv_apply, Function.graph_def, add_zero]

theorem addAtom'_closed (S : BaseSupport) (a : Atom) (hS : S.Closed) :
    (addAtom' S a).Closed := by
  constructor
  intro N₁ N₂ hN₁ hN₂ b hb
  rw [addAtom'_atoms, Enumeration.mem_add_iff]
  exact Or.inl (hS.interference_subset hN₁ hN₂ b hb)

def Support.ofBase (S : BaseSupport) : Support ⊥ where
  atoms :=
    Sᴬ.invImage Prod.snd (λ _ _ ↦ Prod.ext ((Path.eq_nil _).trans (Path.eq_nil _).symm))
  nearLitters :=
    Sᴺ.invImage Prod.snd (λ _ _ ↦ Prod.ext ((Path.eq_nil _).trans (Path.eq_nil _).symm))

@[simp]
theorem Support.ofBase_derivBot (S : BaseSupport) (A : ⊥ ↝ ⊥) :
    Support.ofBase S ⇘. A = S :=
  rfl

theorem InflexiblePath.elim_bot (P : InflexiblePath ⊥) : False := by
  have := le_antisymm P.A.le bot_le
  have := P.hδ.trans_eq this
  exact not_lt_bot this

variable [Level] [CoherentData]

theorem bot_preStrong (S : Support ⊥) : S.PreStrong := by
  constructor
  intro _ _ _ P
  cases P.elim_bot

def addAtom (S : BaseSupport) (a : Atom) : Support ⊥ :=
  .ofBase (addAtom' S a)

omit [Level] [CoherentData] in
theorem addAtom_derivBot (S : BaseSupport) (a : Atom) (A : ⊥ ↝ ⊥) :
    addAtom S a ⇘. A = addAtom' S a :=
  rfl

theorem addAtom_strong (S : BaseSupport) (a : Atom) (hS : S.Closed) : (addAtom S a).Strong := by
  constructor
  · exact bot_preStrong _
  · constructor
    intro A
    rw [addAtom_derivBot]
    exact addAtom'_closed S a hS

omit [Level] [CoherentData] in
@[simp]
theorem addAtom_convAtoms (S : BaseSupport) (a₁ a₂ : Atom) (A : ⊥ ↝ ⊥) :
    convAtoms (addAtom S a₁) (addAtom S a₂) A =
      (λ a₃ a₄ ↦ (a₃ = a₄ ∧ a₃ ∈ Sᴬ) ∨ (a₃ = a₁ ∧ a₄ = a₂)) := by
  ext a₃ a₄
  simp only [convAtoms, Rel.comp, addAtom_derivBot, Rel.inv_apply, addAtom'_atoms_rel]
  constructor
  · rintro ⟨i, hi₃ | hi₃, hi₄ | hi₄⟩
    · exact Or.inl ⟨Sᴬ.rel_coinjective.coinjective hi₃ hi₄, i, hi₃⟩
    · cases (Sᴬ.lt_bound i ⟨a₃, hi₃⟩).ne hi₄.2
    · cases (Sᴬ.lt_bound i ⟨a₄, hi₄⟩).ne hi₃.2
    · exact Or.inr ⟨hi₃.1, hi₄.1⟩
  · rintro (⟨rfl, i, ha⟩ | ⟨rfl, rfl⟩)
    · exact ⟨i, Or.inl ha, Or.inl ha⟩
    · exact ⟨Sᴬ.bound, Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

omit [Level] [CoherentData] in
@[simp]
theorem addAtom_convNearLitters (S : BaseSupport) (a₁ a₂ : Atom) (A : ⊥ ↝ ⊥) :
    convNearLitters (addAtom S a₁) (addAtom S a₂) A = (λ N₁ N₂ ↦ N₁ = N₂ ∧ N₁ ∈ Sᴺ) := by
  ext N₁ N₂
  constructor
  · rintro ⟨i, hi₁, hi₂⟩
    exact ⟨Sᴺ.rel_coinjective.coinjective hi₁ hi₂, i, hi₁⟩
  · rintro ⟨rfl, i, hi⟩
    exact ⟨i, hi, hi⟩

theorem addAtom_sameSpecLe {S : BaseSupport} {a₁ a₂ : Atom}
    (ha₁ : a₁ ∉ Sᴬ) (ha₂ : a₂ ∉ Sᴬ) (ha : ∀ N ∈ Sᴺ, a₁ ∈ Nᴬ ↔ a₂ ∈ Nᴬ) :
    SameSpecLE (addAtom S a₁) (addAtom S a₂) := by
  constructor
  · intro; rfl
  · intro; rfl
  · intro A
    simp only [addAtom_derivBot, Rel.dom, addAtom'_atoms_rel]
    rintro i ⟨a, hi | ⟨rfl, rfl⟩⟩
    · exact ⟨a, Or.inl hi⟩
    · exact ⟨a₂, Or.inr ⟨rfl, rfl⟩⟩
  · intro; rfl
  · intro A
    constructor
    intro b₁ b₂ c hb₁ hb₂
    rw [addAtom_convAtoms] at hb₁ hb₂
    obtain (hb₁ | hb₁) := hb₁ <;> obtain (hb₂ | hb₂) := hb₂
    · exact hb₁.1.trans hb₂.1.symm
    · cases ha₂ (hb₁.1.trans hb₂.2 ▸ hb₁.2)
    · cases ha₂ (hb₂.1.trans hb₁.2 ▸ hb₂.2)
    · exact hb₁.1.trans hb₂.1.symm
  · rintro A i j ⟨N, hi, a, haN, hj⟩
    refine ⟨N, hi, ?_⟩
    obtain (ha | ⟨j, rfl, rfl, rfl⟩) := hj
    · exact ⟨a, haN, Or.inl ha⟩
    · refine ⟨a₂, ?_, Or.inr ⟨_, rfl, rfl, rfl⟩⟩
      dsimp only
      rw [← ha]
      · exact haN
      · exact ⟨i, hi⟩
  · intro _ _ _ _ P
    cases P.elim_bot
  · intro A N₁ N₂ N₃ N₄ h₁ h₂ _ _ _ _ h
    rw [addAtom_convNearLitters] at h₁ h₂
    cases h₁.1
    cases h₂.1
    exact h
  · intro _ _ _ P
    cases P.elim_bot
  · intro _ _ _ P
    cases P.elim_bot

theorem addAtom_spec_eq_spec {S : BaseSupport} {a₁ a₂ : Atom}
    (ha₁ : a₁ ∉ Sᴬ) (ha₂ : a₂ ∉ Sᴬ) (ha : ∀ N ∈ Sᴺ, a₁ ∈ Nᴬ ↔ a₂ ∈ Nᴬ) :
    (addAtom S a₁).spec = (addAtom S a₂).spec := by
  rw [Support.spec_eq_spec_iff]
  apply sameSpec_antisymm
  · exact addAtom_sameSpecLe ha₁ ha₂ ha
  · exact addAtom_sameSpecLe ha₂ ha₁ (λ N hN ↦ (ha N hN).symm)

theorem exists_swap {S : BaseSupport} (h : S.Closed) {a₁ a₂ : Atom}
    (ha₁ : a₁ ∉ Sᴬ) (ha₂ : a₂ ∉ Sᴬ) (ha : ∀ N ∈ Sᴺ, a₁ ∈ Nᴬ ↔ a₂ ∈ Nᴬ) :
    ∃ π : BasePerm, π • S = S ∧ π • a₁ = a₂ := by
  obtain ⟨ρ, hρ⟩ := Support.exists_conv (addAtom_spec_eq_spec ha₁ ha₂ ha)
    (addAtom_strong S a₁ h) (addAtom_strong S a₂ h)
  have hρa := congr_arg (λ S ↦ (S ⇘. .nil)ᴬ) hρ
  have hρN := congr_arg (λ S ↦ (S ⇘. .nil)ᴺ) hρ
  simp only [Support.smul_derivBot, BaseSupport.smul_atoms, BaseSupport.smul_nearLitters,
    addAtom_derivBot, addAtom'_atoms, addAtom'_nearLitters, Enumeration.smul_add] at hρa hρN
  rw [Enumeration.add_inj_iff_of_bound_eq_bound (by rfl)] at hρa
  simp only [Enumeration.smul_singleton, Enumeration.singleton_injective.eq_iff] at hρa
  obtain ⟨hρa, rfl⟩ := hρa
  refine ⟨ρᵁ .nil, ?_, rfl⟩
  rw [BaseSupport.smul_eq_iff]
  constructor
  · exact Enumeration.eq_of_smul_eq hρa
  · exact Enumeration.eq_of_smul_eq hρN

open scoped Pointwise

theorem mem_iff_mem_of_supports {S : BaseSupport} (h : S.Closed) {s : Set Atom}
    (hs : ∀ π : BasePerm, π • S = S → π • s = s)
    {a₁ a₂ : Atom} (h₁ : a₁ ∉ Sᴬ) (h₂ : a₂ ∉ Sᴬ) (ha : ∀ N ∈ Sᴺ, a₁ ∈ Nᴬ ↔ a₂ ∈ Nᴬ) :
    a₁ ∈ s ↔ a₂ ∈ s := by
  obtain ⟨π, hπ, rfl⟩ := exists_swap h h₁ h₂ ha
  specialize hs π hπ
  constructor
  · intro h
    rw [← hs]
    exact Set.smul_mem_smul_set h
  · intro h
    rw [← hs] at h
    exact Set.smul_mem_smul_set_iff.mp h

structure Information : Type u where
  atoms : Set κ
  nearLitters : Set κ
  outside : Prop

def information (S : BaseSupport) (s : Set Atom) : Information where
  atoms := {i | ∃ a ∈ s, Sᴬ.rel i a}
  nearLitters := {i | ∃ N : NearLitter, ((Nᴬ ∩ s) \ Sᴬ).Nonempty ∧ Sᴺ.rel i N}
  outside := ∀ a, a ∉ Sᴬ → (∀ N ∈ Sᴺ, a ∉ Nᴬ) → a ∈ s

theorem subset_of_information_eq {S : BaseSupport} (hS : S.Closed) {s t : Set Atom}
    (hs : ∀ π : BasePerm, π • S = S → π • s = s) (ht : ∀ π : BasePerm, π • S = S → π • t = t)
    (h : information S s = information S t) : s ⊆ t := by
  intro a ha
  by_cases haS : a ∈ Sᴬ
  · obtain ⟨i, hi⟩ := haS
    have := congr_arg Information.atoms h
    dsimp only [information] at this
    rw [Set.ext_iff] at this
    obtain ⟨b, hb, hi'⟩ := (this i).mp ⟨a, ha, hi⟩
    cases Sᴬ.rel_coinjective.coinjective hi hi'
    exact hb
  by_cases haN : ∃ N ∈ Sᴺ, a ∈ Nᴬ
  · obtain ⟨N, ⟨i, hiN⟩, haN⟩ := haN
    have := congr_arg Information.nearLitters h
    dsimp only [information] at this
    rw [Set.ext_iff] at this
    obtain ⟨N₂, ⟨b, ⟨hbN, hb⟩, hbS⟩, hiN₂⟩ := (this i).mp ⟨N, ⟨a, ⟨haN, ha⟩, haS⟩, hiN⟩
    cases Sᴺ.rel_coinjective.coinjective hiN hiN₂
    rwa [mem_iff_mem_of_supports hS ht haS hbS]
    rintro N' ⟨j, hj⟩
    constructor
    · intro haN'
      by_cases hN : Nᴸ = N'ᴸ
      · by_contra hbN'
        have := hS.interference_subset ⟨i, hiN⟩ ⟨j, hj⟩ b
        rw [interference_eq_of_litter_eq hN] at this
        exact hbS (this (Or.inl ⟨hbN, hbN'⟩))
      · have := hS.interference_subset ⟨i, hiN⟩ ⟨j, hj⟩ a
        rw [interference_eq_of_litter_ne hN] at this
        cases haS (this ⟨haN, haN'⟩)
    · intro hbN'
      by_cases hN : Nᴸ = N'ᴸ
      · by_contra haN'
        have := hS.interference_subset ⟨i, hiN⟩ ⟨j, hj⟩ a
        rw [interference_eq_of_litter_eq hN] at this
        exact haS (this (Or.inl ⟨haN, haN'⟩))
      · have := hS.interference_subset ⟨i, hiN⟩ ⟨j, hj⟩ b
        rw [interference_eq_of_litter_ne hN] at this
        cases hbS (this ⟨hbN, hbN'⟩)
  · have := congr_arg Information.outside h
    dsimp only [information] at this
    rw [eq_iff_iff] at this
    push_neg at haN
    refine this.mp ?_ a haS haN
    intro b hbS hbN
    rwa [← mem_iff_mem_of_supports hS hs haS hbS]
    intro N hN
    simp only [haN N hN, hbN N hN]

theorem eq_of_information_eq {S : BaseSupport} (hS : S.Closed) {s t : Set Atom}
    (hs : ∀ π : BasePerm, π • S = S → π • s = s) (ht : ∀ π : BasePerm, π • S = S → π • t = t)
    (h : information S s = information S t) : s = t :=
  subset_antisymm (subset_of_information_eq hS hs ht h) (subset_of_information_eq hS ht hs h.symm)

theorem card_supports_le_of_closed' {S : BaseSupport} (hS : S.Closed) :
    #{s : Set Atom // ∀ π : BasePerm, π • S = S → π • s = s} ≤ #Information := by
  apply mk_le_of_injective (f := λ s ↦ information S s.val)
  rintro ⟨s, hs⟩ ⟨t, ht⟩ h
  rw [Subtype.mk_eq_mk]
  exact eq_of_information_eq hS hs ht h

def informationEquiv : Information ≃ Set κ × Set κ × Prop where
  toFun i := ⟨i.atoms, i.nearLitters, i.outside⟩
  invFun i := ⟨i.1, i.2.1, i.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Level] [CoherentData] in
theorem card_information_le :
    #Information ≤ 2 ^ #κ := by
  rw [Cardinal.eq.mpr ⟨informationEquiv⟩]
  simp only [mk_prod, mk_set, Cardinal.lift_id, Cardinal.lift_id', mk_fintype, Fintype.card_prop,
    Nat.cast_ofNat, Cardinal.lift_ofNat]
  apply mul_le_of_le
  · have := Cardinal.power_le_power_left two_ne_zero κ_isRegular.aleph0_le
    exact (cantor ℵ₀).le.trans this
  · rfl
  apply mul_le_of_le
  · have := Cardinal.power_le_power_left two_ne_zero κ_isRegular.aleph0_le
    exact (cantor ℵ₀).le.trans this
  · rfl
  · have := Cardinal.power_le_power_left two_ne_zero κ_isRegular.aleph0_le
    have htwo := nat_lt_aleph0 2
    rw [Nat.cast_ofNat] at htwo
    exact htwo.le.trans ((cantor ℵ₀).le.trans this)

theorem card_supports_le_of_closed {S : BaseSupport} (hS : S.Closed) :
    #{s : Set Atom // ∀ π : BasePerm, π • S = S → π • s = s} ≤ 2 ^ #κ :=
  le_trans (card_supports_le_of_closed' hS) card_information_le

omit [Level] [CoherentData] in
theorem BaseSupport.interference_small (S : BaseSupport) :
    Small {a : Atom | ∃ N₁ N₂, N₁ ∈ Sᴺ ∧ N₂ ∈ Sᴺ ∧ a ∈ interference N₁ N₂} := by
  have := (Support.ofBase S).interference_small
  apply (this.image Prod.snd).mono
  intro a h
  exact ⟨⟨.nil, a⟩, h, rfl⟩

theorem card_supports_le (S : BaseSupport) :
    #{s : Set Atom // ∀ π : BasePerm, π • S = S → π • s = s} ≤ 2 ^ #κ := by
  have := card_supports_le_of_closed (S := S + ⟨.ofSet _ S.interference_small, .empty⟩) ?_
  · refine le_trans (mk_le_mk_of_subset ?_) this
    intro s hs π hπ
    apply hs
    apply BaseSupport.ext
    · have := congr_arg (·ᴬ) hπ
      dsimp only at this
      rw [BaseSupport.smul_atoms, BaseSupport.add_atoms, Enumeration.smul_add,
        Enumeration.add_inj_iff_of_bound_eq_bound (by rfl)] at this
      exact this.1
    · have := congr_arg (·ᴺ) hπ
      dsimp only at this
      rw [BaseSupport.smul_nearLitters, BaseSupport.add_nearLitters, Enumeration.smul_add,
        Enumeration.add_inj_iff_of_bound_eq_bound (by rfl)] at this
      exact this.1
  · constructor
    intro N₁ N₂ hN₁ hN₂ a ha
    simp only [BaseSupport.add_nearLitters, BaseSupport.mk_nearLitters,
      Enumeration.add_empty] at hN₁ hN₂
    rw [BaseSupport.add_atoms, BaseSupport.mk_atoms, Enumeration.mem_add_iff, BaseSupport.mk_atoms,
      Enumeration.mem_ofSet_iff]
    right
    exact ⟨N₁, N₂, hN₁, hN₂, ha⟩

end ConNF
