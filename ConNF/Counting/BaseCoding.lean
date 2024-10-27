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

end ConNF
