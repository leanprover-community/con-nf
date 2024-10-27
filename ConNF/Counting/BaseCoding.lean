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

variable [Level] [CoherentData]

theorem bot_preStrong (S : Support ⊥) : S.PreStrong := by
  constructor
  intro A N _ P
  have := le_antisymm P.A.le bot_le
  have := P.hδ.trans_eq this
  cases not_lt_bot this

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

theorem addAtom_spec_eq_spec {S : BaseSupport} (hS : S.Closed) {a₁ a₂ : Atom}
    (ha₁ : a₁ ∉ Sᴬ) (ha₂ : a₂ ∉ Sᴬ) (ha : ∀ N ∈ Sᴺ, a₁ ∈ Nᴬ ↔ a₂ ∈ Nᴬ) :
    (addAtom S a₁).spec = (addAtom S a₂).spec := by
  rw [Support.spec_eq_spec_iff]
  constructor
  · intro; rfl
  · intro; rfl
  all_goals sorry

theorem exists_swap {S : BaseSupport} (h : S.Closed) {a₁ a₂ : Atom}
    (ha₁ : a₁ ∉ Sᴬ) (ha₂ : a₂ ∉ Sᴬ) (ha : ∀ N ∈ Sᴺ, a₁ ∈ Nᴬ ↔ a₂ ∈ Nᴬ) :
    ∃ π : BasePerm, π • S = S ∧ π • a₁ = a₂ := by
  obtain ⟨ρ, hρ⟩ := Support.exists_conv (addAtom_spec_eq_spec h ha₁ ha₂ ha)
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
