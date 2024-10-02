import ConNF.FOA.Inflexible
import ConNF.Counting.CodingFunction

/-!
# Specifications for supports

In this file, we define the notion of a specification for a support.

## Main declarations

* `ConNF.Spec`: Specifications for supports.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}] [Level] [CoherentData]

structure AtomCond where
  atoms : Set κ
  nearLitters : Set κ

structure FlexCond where
  nearLitters : Set κ

structure InflexCond (δ : TypeIndex) [LeLevel δ] where
  χ : CodingFunction δ
  atoms : Tree (Rel κ κ) δ
  nearLitters : Tree (Rel κ κ) δ

instance : SuperA AtomCond (Set κ) where
  superA := AtomCond.atoms

instance : SuperN AtomCond (Set κ) where
  superN := AtomCond.nearLitters

instance : SuperN FlexCond (Set κ) where
  superN := FlexCond.nearLitters

instance (δ : TypeIndex) [LeLevel δ] : SuperA (InflexCond δ) (Tree (Rel κ κ) δ) where
  superA := InflexCond.atoms

instance (δ : TypeIndex) [LeLevel δ] : SuperN (InflexCond δ) (Tree (Rel κ κ) δ) where
  superN := InflexCond.nearLitters

inductive NearLitterCond (β : TypeIndex) [LeLevel β]
  | flex : FlexCond → NearLitterCond β
  | inflex (P : InflexiblePath β) : InflexCond P.δ → NearLitterCond β

structure Spec (β : TypeIndex) [LeLevel β] where
  atoms : Tree (Enumeration AtomCond) β
  nearLitters : Tree (Enumeration (NearLitterCond β)) β

instance (β : TypeIndex) [LeLevel β] :
    SuperA (Spec β) (Tree (Enumeration AtomCond) β) where
  superA := Spec.atoms

instance (β : TypeIndex) [LeLevel β] :
    SuperN (Spec β) (Tree (Enumeration (NearLitterCond β)) β) where
  superN := Spec.nearLitters

variable {β : TypeIndex} [LeLevel β]

def nearLitterCondRelFlex (S : Support β) (A : β ↝ ⊥) :
    Rel NearLitter (NearLitterCond β) :=
  λ N c ↦ ¬Inflexible A Nᴸ ∧ c = .flex ⟨{i | ∃ N', (S ⇘. A)ᴺ.rel i N' ∧ Nᴸ = N'ᴸ}⟩

def nearLitterCondRelInflex (S : Support β) (A : β ↝ ⊥) :
    Rel NearLitter (NearLitterCond β) :=
  λ N c ↦ ∃ P : InflexiblePath β, ∃ t : Tangle P.δ, A = P.A ↘ P.hε ↘. ∧ Nᴸ = fuzz P.hδε t ∧
    c = .inflex P ⟨t.code,
      λ B ↦ (S ⇘. (P.A ↘ P.hδ ⇘ B))ᴬ.rel.comp (t.support ⇘. B)ᴬ.rel.inv,
      λ B ↦ (S ⇘. (P.A ↘ P.hδ ⇘ B))ᴺ.rel.comp (t.support ⇘. B)ᴺ.rel.inv⟩

def nearLitterCondRel (S : Support β) (A : β ↝ ⊥) :
    Rel NearLitter (NearLitterCond β) :=
  nearLitterCondRelFlex S A ⊔ nearLitterCondRelInflex S A

theorem nearLitterCondRelFlex_coinjective
     {S : Support β} {A : β ↝ ⊥} :
    (nearLitterCondRelFlex S A).Coinjective := by
  constructor
  rintro _ _ N ⟨_, rfl⟩ ⟨_, rfl⟩
  rfl

theorem nearLitterCondRelInflex_coinjective
     {S : Support β} {A : β ↝ ⊥} :
    (nearLitterCondRelInflex S A).Coinjective := by
  constructor
  rintro _ _ N ⟨P, t, hA, ht, rfl⟩ ⟨P', t', hA', ht', rfl⟩
  cases inflexiblePath_subsingleton hA hA' ht ht'
  cases fuzz_injective (ht.symm.trans ht')
  rfl

theorem flexible_of_mem_dom_nearLitterCondFlexRel
    {S : Support β} {A : β ↝ ⊥} {N : NearLitter} (h : N ∈ (nearLitterCondRelFlex S A).dom) :
    ¬Inflexible A Nᴸ := by
  obtain ⟨c, h⟩ := h
  exact h.1

theorem inflexible_of_mem_dom_nearLitterCondInflexRel
    {S : Support β} {A : β ↝ ⊥} {N : NearLitter} (h : N ∈ (nearLitterCondRelInflex S A).dom) :
    Inflexible A Nᴸ := by
  obtain ⟨c, P, t, hA, ht, _⟩ := h
  exact ⟨P, t, hA, ht⟩

theorem nearLitterCondRel_dom_disjoint {S : Support β} {A : β ↝ ⊥} :
    Disjoint (nearLitterCondRelFlex S A).dom (nearLitterCondRelInflex S A).dom := by
  rw [Set.disjoint_iff_forall_ne]
  rintro N hN₁ _ hN₂ rfl
  exact flexible_of_mem_dom_nearLitterCondFlexRel hN₁
    (inflexible_of_mem_dom_nearLitterCondInflexRel hN₂)

theorem nearLitterCondRel_coinjective (S : Support β) (A : β ↝ ⊥) :
    (nearLitterCondRel S A).Coinjective :=
  Rel.sup_coinjective
    nearLitterCondRelFlex_coinjective
    nearLitterCondRelInflex_coinjective
    nearLitterCondRel_dom_disjoint

theorem nearLitterCondRel_cosurjective (S : Support β) (A : β ↝ ⊥) :
    (nearLitterCondRel S A).Cosurjective := by
  constructor
  intro N
  obtain (⟨P, t, hA, ht⟩ | hN) := inflexible_cases A Nᴸ
  · exact ⟨_, Or.inr ⟨P, t, hA, ht, rfl⟩⟩
  · exact ⟨_, Or.inl ⟨hN, rfl⟩⟩

def Support.spec (S : Support β) : Spec β where
  atoms A := (S ⇘. A)ᴬ.image
    (λ a ↦ ⟨{i | (S ⇘. A)ᴬ.rel i a}, {i | ∃ N, (S ⇘. A)ᴺ.rel i N ∧ a ∈ Nᴬ}⟩)
  nearLitters A := (S ⇘. A)ᴺ.comp
    (nearLitterCondRel S A) (nearLitterCondRel_coinjective S A)

theorem Support.spec_atoms_dom (S : Support β) (A : β ↝ ⊥) :
    (S.specᴬ A).rel.dom = (S ⇘. A)ᴬ.rel.dom := by
  ext i
  constructor
  · rintro ⟨c, a, h, _⟩
    exact ⟨a, h⟩
  · rintro ⟨a, h⟩
    exact ⟨_, a, h, rfl⟩

theorem Support.spec_nearLitters_dom (S : Support β) (A : β ↝ ⊥) :
    (S.specᴺ A).rel.dom = (S ⇘. A)ᴺ.rel.dom := by
  ext i
  constructor
  · rintro ⟨c, a, h, _⟩
    exact ⟨a, h⟩
  · rintro ⟨N, h⟩
    obtain ⟨c, hc⟩ := (nearLitterCondRel_cosurjective S A).cosurjective N
    exact ⟨c, N, h, hc⟩

def convAtoms (S T : Support β) (A : β ↝ ⊥) : Rel Atom Atom :=
  (S ⇘. A)ᴬ.rel.inv.comp (T ⇘. A)ᴬ.rel

def convNearLitters (S T : Support β) (A : β ↝ ⊥) :
    Rel NearLitter NearLitter :=
  (S ⇘. A)ᴺ.rel.inv.comp (T ⇘. A)ᴺ.rel

@[simp]
theorem convAtoms_inv (S T : Support β) (A : β ↝ ⊥) :
    (convAtoms S T A).inv = convAtoms T S A := by
  ext a b
  simp only [Rel.inv, flip, convAtoms, Rel.comp]
  tauto

@[simp]
theorem convNearLitters_inv (S T : Support β) (A : β ↝ ⊥) :
    (convNearLitters S T A).inv = convNearLitters T S A := by
  ext a b
  simp only [Rel.inv, flip, convNearLitters, Rel.comp]
  tauto

def atomMemRel (S : Support β) (A : β ↝ ⊥) : Rel κ κ :=
  (S ⇘. A)ᴺ.rel.comp (Rel.comp (λ N a ↦ a ∈ Nᴬ) (S ⇘. A)ᴬ.rel.inv)

structure SameSpec (S T : Support β) : Prop where
(atoms_dom_eq : ∀ A, (S ⇘. A)ᴬ.rel.dom = (T ⇘. A)ᴬ.rel.dom)
(nearLitters_dom_eq : ∀ A, (S ⇘. A)ᴺ.rel.dom = (T ⇘. A)ᴺ.rel.dom)
(convAtoms_oneOne : ∀ A, (convAtoms S T A).OneOne)
(atomMemRel_eq : ∀ A, atomMemRel S A = atomMemRel T A)
(inflexible_iff : ∀ {A N₁ N₂}, convNearLitters S T A N₁ N₂ →
  ∀ P : InflexiblePath β, ∀ t : Tangle P.δ, A = P.A ↘ P.hε ↘. →
  ((∃ ρ : AllPerm P.δ, N₁ᴸ = fuzz P.hδε (ρ • t)) ↔
  (∃ ρ : AllPerm P.δ, N₂ᴸ = fuzz P.hδε (ρ • t))))
(litter_eq_iff_of_flexible : ∀ {A N₁ N₂ N₃ N₄},
  convNearLitters S T A N₁ N₂ → convNearLitters S T A N₃ N₄ →
  ¬Inflexible A N₁ᴸ → ¬Inflexible A N₂ᴸ → (N₁ᴸ = N₃ᴸ ↔ N₂ᴸ = N₄ᴸ))
(convAtoms_of_inflexible : ∀ A, ∀ N₁ N₂ : NearLitter,
  ∀ P : InflexiblePath β, ∀ t : Tangle P.δ, ∀ ρ : AllPerm P.δ,
  A = P.A ↘ P.hε ↘. ∧ N₁ᴸ = fuzz P.hδε t → N₂ᴸ = fuzz P.hδε (ρ • t) →
  ∀ B : P.δ ↝ ⊥,
    convAtoms (S ⇘ (P.A ↘ P.hδ)) (T ⇘ (P.A ↘ P.hδ)) B ⊓ (λ a _ ↦ a ∈ (t.support ⇘. B)ᴬ) ≤
      (λ a b ↦ b = ρᵁ ⇘. B • a))
(convNearLitters_of_inflexible : ∀ A, ∀ N₁ N₂ : NearLitter,
  ∀ P : InflexiblePath β, ∀ t : Tangle P.δ, ∀ ρ : AllPerm P.δ,
  A = P.A ↘ P.hε ↘. ∧ N₁ᴸ = fuzz P.hδε t → N₂ᴸ = fuzz P.hδε (ρ • t) →
  ∀ B : P.δ ↝ ⊥,
    convNearLitters (S ⇘ (P.A ↘ P.hδ)) (T ⇘ (P.A ↘ P.hδ)) B ⊓ (λ a _ ↦ a ∈ (t.support ⇘. B)ᴺ) ≤
      (λ N₁ N₂ ↦ N₂ = ρᵁ ⇘. B • N₁))

/-- A variant of `SameSpec` in which most equalities have been turned into one-directional
implications. It can sometimes be easier to prove this in generality than to prove `SameSpec`
directly. -/
structure SameSpecLE (S T : Support β) : Prop where
(atoms_dom_subset : ∀ A, (S ⇘. A)ᴬ.rel.dom ⊆ (T ⇘. A)ᴬ.rel.dom)
(nearLitters_dom_subset : ∀ A, (S ⇘. A)ᴺ.rel.dom ⊆ (T ⇘. A)ᴺ.rel.dom)
(convAtoms_injective : ∀ A, (convAtoms S T A).Injective)
(atomMemRel_le : ∀ A, atomMemRel S A ≤ atomMemRel T A)
(inflexible_of_inflexible : ∀ {A N₁ N₂}, convNearLitters S T A N₁ N₂ →
  ∀ P : InflexiblePath β, ∀ t : Tangle P.δ, A = P.A ↘ P.hε ↘. →
  N₁ᴸ = fuzz P.hδε t → ∃ ρ : AllPerm P.δ, N₂ᴸ = fuzz P.hδε (ρ • t))
(litter_eq_of_flexible : ∀ {A N₁ N₂ N₃ N₄},
  convNearLitters S T A N₁ N₂ → convNearLitters S T A N₃ N₄ →
  ¬Inflexible A N₁ᴸ → ¬Inflexible A N₂ᴸ → (N₁ᴸ = N₃ᴸ → N₂ᴸ = N₄ᴸ))
(convAtoms_of_inflexible : ∀ A, ∀ N₁ N₂ : NearLitter,
  ∀ P : InflexiblePath β, ∀ t : Tangle P.δ, ∀ ρ : AllPerm P.δ,
  A = P.A ↘ P.hε ↘. ∧ N₁ᴸ = fuzz P.hδε t → N₂ᴸ = fuzz P.hδε (ρ • t) →
  ∀ B : P.δ ↝ ⊥,
    convAtoms (S ⇘ (P.A ↘ P.hδ)) (T ⇘ (P.A ↘ P.hδ)) B ⊓ (λ a _ ↦ a ∈ (t.support ⇘. B)ᴬ) ≤
      (λ a b ↦ b = ρᵁ ⇘. B • a))
(convNearLitters_of_inflexible : ∀ A, ∀ N₁ N₂ : NearLitter,
  ∀ P : InflexiblePath β, ∀ t : Tangle P.δ, ∀ ρ : AllPerm P.δ,
  A = P.A ↘ P.hε ↘. ∧ N₁ᴸ = fuzz P.hδε t → N₂ᴸ = fuzz P.hδε (ρ • t) →
  ∀ B : P.δ ↝ ⊥,
    convNearLitters (S ⇘ (P.A ↘ P.hδ)) (T ⇘ (P.A ↘ P.hδ)) B ⊓ (λ a _ ↦ a ∈ (t.support ⇘. B)ᴺ) ≤
      (λ N₁ N₂ ↦ N₂ = ρᵁ ⇘. B • N₁))

theorem sameSpec_antisymm {S T : Support β} (h₁ : SameSpecLE S T) (h₂ : SameSpecLE T S) :
    SameSpec S T where
  atoms_dom_eq A := subset_antisymm (h₁.atoms_dom_subset A) (h₂.atoms_dom_subset A)
  nearLitters_dom_eq A := subset_antisymm (h₁.nearLitters_dom_subset A) (h₂.nearLitters_dom_subset A)
  convAtoms_oneOne A := ⟨h₁.convAtoms_injective A,
    Rel.inv_injective_iff.mp (convAtoms_inv S T A ▸ h₂.convAtoms_injective A)⟩
  atomMemRel_eq A := le_antisymm (h₁.atomMemRel_le A) (h₂.atomMemRel_le A)
  inflexible_iff h P t hA := by
    constructor
    · rintro ⟨ρ, ht⟩
      obtain ⟨ρ', ht'⟩ := h₁.inflexible_of_inflexible h P (ρ • t) hA ht
      use ρ' * ρ
      rw [ht', mul_smul]
    · rintro ⟨ρ, ht⟩
      obtain ⟨ρ', ht'⟩ := h₂.inflexible_of_inflexible (convNearLitters_inv T S _ ▸ h) P (ρ • t) hA ht
      use ρ' * ρ
      rw [ht', mul_smul]
  litter_eq_iff_of_flexible hN₁ hN₂ hN₁' hN₂' := ⟨h₁.litter_eq_of_flexible hN₁ hN₂ hN₁' hN₂',
    h₂.litter_eq_of_flexible
      (convNearLitters_inv S T _ ▸ hN₁) (convNearLitters_inv S T _ ▸ hN₂) hN₂' hN₁'⟩
  convAtoms_of_inflexible := h₁.convAtoms_of_inflexible
  convNearLitters_of_inflexible := h₁.convNearLitters_of_inflexible

namespace Support

variable {S T : Support β}

theorem atoms_dom_subset_of_spec_eq_spec (h : S.spec = T.spec) (A : β ↝ ⊥) :
    (S ⇘. A)ᴬ.rel.dom ⊆ (T ⇘. A)ᴬ.rel.dom := by
  rw [← spec_atoms_dom, ← spec_atoms_dom, h]

theorem nearLitters_dom_subset_of_spec_eq_spec (h : S.spec = T.spec) (A : β ↝ ⊥) :
    (S ⇘. A)ᴺ.rel.dom ⊆ (T ⇘. A)ᴺ.rel.dom := by
  rw [← spec_nearLitters_dom, ← spec_nearLitters_dom, h]

theorem sameSpecLe_of_spec_eq_spec (h : S.spec = T.spec) :
    SameSpecLE S T where
  atoms_dom_subset := atoms_dom_subset_of_spec_eq_spec h
  nearLitters_dom_subset := nearLitters_dom_subset_of_spec_eq_spec h
  convAtoms_injective := sorry
  atomMemRel_le := sorry
  inflexible_of_inflexible := sorry
  litter_eq_of_flexible := sorry
  convAtoms_of_inflexible := sorry
  convNearLitters_of_inflexible := sorry

theorem spec_eq_spec_iff (S T : Support β) :
    S.spec = T.spec ↔ SameSpec S T := by
  constructor
  · intro h
    exact sameSpec_antisymm (sameSpecLe_of_spec_eq_spec h) (sameSpecLe_of_spec_eq_spec h.symm)
  · sorry

end Support

end ConNF
