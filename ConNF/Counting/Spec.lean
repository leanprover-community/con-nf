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

@[ext]
theorem Spec.ext {σ τ : Spec β} (h₁ : ∀ A, σᴬ A = τᴬ A) (h₂ : ∀ A, σᴺ A = τᴺ A) : σ = τ := by
  obtain ⟨σa, σN⟩ := σ
  obtain ⟨τa, τN⟩ := τ
  rw [mk.injEq]
  constructor
  · funext A
    exact h₁ A
  · funext A
    exact h₂ A

instance : LE (Spec β) where
  le σ τ := ∀ A,
    (σᴬ A).bound = (τᴬ A).bound ∧ (σᴬ A).rel ≤ (τᴬ A).rel ∧
    (σᴺ A).bound = (τᴺ A).bound ∧ (σᴺ A).rel ≤ (τᴺ A).rel

instance : PartialOrder (Spec β) where
  le_refl σ A := ⟨rfl, le_rfl, rfl, le_rfl⟩
  le_trans σ τ υ h₁ h₂ A := ⟨(h₁ A).1.trans (h₂ A).1, (h₁ A).2.1.trans (h₂ A).2.1,
    (h₁ A).2.2.1.trans (h₂ A).2.2.1, (h₁ A).2.2.2.trans (h₂ A).2.2.2⟩
  le_antisymm σ τ h₁ h₂ := Spec.ext
    (λ A ↦ Enumeration.ext (h₁ A).1 (le_antisymm (h₁ A).2.1 (h₂ A).2.1))
    (λ A ↦ Enumeration.ext (h₁ A).2.2.1 (le_antisymm (h₁ A).2.2.2 (h₂ A).2.2.2))

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

theorem nearLitterCondRel_inflex {S : Support β} {A : β ↝ ⊥} {N : NearLitter}
    {P : InflexiblePath β} {χ : CodingFunction P.δ} {ta tn : Tree (Rel κ κ) P.δ} :
    nearLitterCondRel S A N (.inflex P ⟨χ, ta, tn⟩) →
    ∃ t : Tangle P.δ, A = P.A ↘ P.hε ↘. ∧ Nᴸ = fuzz P.hδε t ∧ χ = t.code ∧
      (ta = λ B ↦ (S ⇘. (P.A ↘ P.hδ ⇘ B))ᴬ.rel.comp (t.support ⇘. B)ᴬ.rel.inv) ∧
      (tn = λ B ↦ (S ⇘. (P.A ↘ P.hδ ⇘ B))ᴺ.rel.comp (t.support ⇘. B)ᴺ.rel.inv) := by
  rintro (⟨_, h⟩ | ⟨P', t, hA, ht, h⟩)
  · cases h
  · rw [NearLitterCond.inflex.injEq] at h
    cases h.1
    rw [heq_eq_eq, InflexCond.mk.injEq] at h
    exact ⟨t, hA, ht, h.2⟩

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

theorem Support.spec_atoms (S : Support β) (A : β ↝ ⊥) :
    S.specᴬ A = (S ⇘. A)ᴬ.image
      (λ a ↦ ⟨{i | (S ⇘. A)ᴬ.rel i a}, {i | ∃ N, (S ⇘. A)ᴺ.rel i N ∧ a ∈ Nᴬ}⟩) :=
  rfl

theorem Support.spec_nearLitters (S : Support β) (A : β ↝ ⊥) :
    S.specᴺ A = (S ⇘. A)ᴺ.comp
      (nearLitterCondRel S A) (nearLitterCondRel_coinjective S A) :=
  rfl

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

omit [Level] [CoherentData] [LeLevel β] in
@[simp]
theorem convAtoms_inv (S T : Support β) (A : β ↝ ⊥) :
    (convAtoms S T A).inv = convAtoms T S A := by
  ext a b
  simp only [Rel.inv, flip, convAtoms, Rel.comp]
  tauto

omit [Level] [CoherentData] [LeLevel β] in
@[simp]
theorem convNearLitters_inv (S T : Support β) (A : β ↝ ⊥) :
    (convNearLitters S T A).inv = convNearLitters T S A := by
  ext a b
  simp only [Rel.inv, flip, convNearLitters, Rel.comp]
  tauto

omit [Level] [CoherentData] [LeLevel β] in
theorem convAtoms_dom_subset (S T : Support β) (A : β ↝ ⊥) :
    (convAtoms S T A).dom ⊆ (S ⇘. A)ᴬ := by
  rintro a ⟨b, i, ha, -⟩
  exact ⟨i, ha⟩

omit [Level] [CoherentData] [LeLevel β] in
theorem convNearLitters_dom_subset (S T : Support β) (A : β ↝ ⊥) :
    (convNearLitters S T A).dom ⊆ (S ⇘. A)ᴺ := by
  rintro N ⟨N', i, hN, -⟩
  exact ⟨i, hN⟩

def atomMemRel (S : Support β) (A : β ↝ ⊥) : Rel κ κ :=
  (S ⇘. A)ᴺ.rel.comp (Rel.comp (λ N a ↦ a ∈ Nᴬ) (S ⇘. A)ᴬ.rel.inv)

structure SameSpec (S T : Support β) : Prop where
(atoms_bound_eq : ∀ A, (S ⇘. A)ᴬ.bound = (T ⇘. A)ᴬ.bound)
(nearLitters_bound_eq : ∀ A, (S ⇘. A)ᴺ.bound = (T ⇘. A)ᴺ.bound)
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
  ¬Inflexible A N₁ᴸ → ¬Inflexible A N₂ᴸ → ¬Inflexible A N₃ᴸ → ¬Inflexible A N₄ᴸ →
  (N₁ᴸ = N₃ᴸ ↔ N₂ᴸ = N₄ᴸ))
(atoms_iff_of_inflexible : ∀ A, ∀ N₁ N₂ : NearLitter,
  ∀ P : InflexiblePath β, ∀ t : Tangle P.δ, ∀ ρ : AllPerm P.δ,
  A = P.A ↘ P.hε ↘. → N₁ᴸ = fuzz P.hδε t → N₂ᴸ = fuzz P.hδε (ρ • t) →
  convNearLitters S T A N₁ N₂ → ∀ B : P.δ ↝ ⊥, ∀ a ∈ (t.support ⇘. B)ᴬ,
  ∀ i, (S ⇘. (P.A ↘ P.hδ ⇘ B))ᴬ.rel i a ↔ (T ⇘. (P.A ↘ P.hδ ⇘ B))ᴬ.rel i (ρᵁ B • a))
(nearLitters_iff_of_inflexible : ∀ A, ∀ N₁ N₂ : NearLitter,
  ∀ P : InflexiblePath β, ∀ t : Tangle P.δ, ∀ ρ : AllPerm P.δ,
  A = P.A ↘ P.hε ↘. → N₁ᴸ = fuzz P.hδε t → N₂ᴸ = fuzz P.hδε (ρ • t) →
  convNearLitters S T A N₁ N₂ → ∀ B : P.δ ↝ ⊥, ∀ N ∈ (t.support ⇘. B)ᴺ,
  ∀ i, (S ⇘. (P.A ↘ P.hδ ⇘ B))ᴺ.rel i N ↔ (T ⇘. (P.A ↘ P.hδ ⇘ B))ᴺ.rel i (ρᵁ B • N))

/-- A variant of `SameSpec` in which most equalities have been turned into one-directional
implications. It can sometimes be easier to prove this in generality than to prove `SameSpec`
directly. -/
structure SameSpecLE (S T : Support β) : Prop where
(atoms_bound_eq : ∀ A, (S ⇘. A)ᴬ.bound = (T ⇘. A)ᴬ.bound)
(nearLitters_bound_eq : ∀ A, (S ⇘. A)ᴺ.bound = (T ⇘. A)ᴺ.bound)
(atoms_dom_subset : ∀ A, (S ⇘. A)ᴬ.rel.dom ⊆ (T ⇘. A)ᴬ.rel.dom)
(nearLitters_dom_subset : ∀ A, (S ⇘. A)ᴺ.rel.dom ⊆ (T ⇘. A)ᴺ.rel.dom)
(convAtoms_injective : ∀ A, (convAtoms S T A).Injective)
(atomMemRel_le : ∀ A, atomMemRel S A ≤ atomMemRel T A)
(inflexible_of_inflexible : ∀ {A N₁ N₂}, convNearLitters S T A N₁ N₂ →
  ∀ P : InflexiblePath β, ∀ t : Tangle P.δ, A = P.A ↘ P.hε ↘. →
  N₁ᴸ = fuzz P.hδε t → ∃ ρ : AllPerm P.δ, N₂ᴸ = fuzz P.hδε (ρ • t))
(litter_eq_of_flexible : ∀ {A N₁ N₂ N₃ N₄},
  convNearLitters S T A N₁ N₂ → convNearLitters S T A N₃ N₄ →
  ¬Inflexible A N₁ᴸ → ¬Inflexible A N₂ᴸ → ¬Inflexible A N₃ᴸ → ¬Inflexible A N₄ᴸ →
  N₁ᴸ = N₃ᴸ → N₂ᴸ = N₄ᴸ)
(atoms_of_inflexible : ∀ A, ∀ N₁ N₂ : NearLitter,
  ∀ P : InflexiblePath β, ∀ t : Tangle P.δ, ∀ ρ : AllPerm P.δ,
  A = P.A ↘ P.hε ↘. → N₁ᴸ = fuzz P.hδε t → N₂ᴸ = fuzz P.hδε (ρ • t) →
  convNearLitters S T A N₁ N₂ → ∀ B : P.δ ↝ ⊥, ∀ a ∈ (t.support ⇘. B)ᴬ,
  ∀ i, (S ⇘. (P.A ↘ P.hδ ⇘ B))ᴬ.rel i a → (T ⇘. (P.A ↘ P.hδ ⇘ B))ᴬ.rel i (ρᵁ B • a))
(nearLitters_of_inflexible : ∀ A, ∀ N₁ N₂ : NearLitter,
  ∀ P : InflexiblePath β, ∀ t : Tangle P.δ, ∀ ρ : AllPerm P.δ,
  A = P.A ↘ P.hε ↘. → N₁ᴸ = fuzz P.hδε t → N₂ᴸ = fuzz P.hδε (ρ • t) →
  convNearLitters S T A N₁ N₂ → ∀ B : P.δ ↝ ⊥, ∀ N ∈ (t.support ⇘. B)ᴺ,
  ∀ i, (S ⇘. (P.A ↘ P.hδ ⇘ B))ᴺ.rel i N → (T ⇘. (P.A ↘ P.hδ ⇘ B))ᴺ.rel i (ρᵁ B • N))

theorem SameSpec.atoms_dom_of_dom {S T : Support β} (h : SameSpec S T) {A : β ↝ ⊥}
    {i : κ} {a : Atom} (ha : (S ⇘. A)ᴬ.rel i a) :
    ∃ b, (T ⇘. A)ᴬ.rel i b := by
  have hdom := h.atoms_dom_eq A
  rw [Set.ext_iff] at hdom
  exact (hdom i).mp ⟨a, ha⟩

theorem SameSpec.nearLitters_dom_of_dom {S T : Support β} (h : SameSpec S T) {A : β ↝ ⊥}
    {i : κ} {N₁ : NearLitter} (hN₁ : (S ⇘. A)ᴺ.rel i N₁) :
    ∃ N₂, (T ⇘. A)ᴺ.rel i N₂ := by
  have hdom := h.nearLitters_dom_eq A
  rw [Set.ext_iff] at hdom
  exact (hdom i).mp ⟨N₁, hN₁⟩

theorem SameSpec.inflexible_iff' {S T : Support β} (h : SameSpec S T) {A : β ↝ ⊥}
    {N₁ N₂ : NearLitter} (h' : convNearLitters S T A N₁ N₂) :
    Inflexible A N₁ᴸ ↔ Inflexible A N₂ᴸ := by
  constructor
  · rintro ⟨P, t, hA, ht⟩
    have := (h.inflexible_iff h' P t hA).mp ⟨1, by rwa [one_smul]⟩
    obtain ⟨ρ, hρ⟩ := this
    exact ⟨P, ρ • t, hA, hρ⟩
  · rintro ⟨P, t, hA, ht⟩
    have := (h.inflexible_iff h' P t hA).mpr ⟨1, by rwa [one_smul]⟩
    obtain ⟨ρ, hρ⟩ := this
    exact ⟨P, ρ • t, hA, hρ⟩

theorem sameSpec_antisymm {S T : Support β} (h₁ : SameSpecLE S T) (h₂ : SameSpecLE T S) :
    SameSpec S T where
  atoms_bound_eq := h₁.atoms_bound_eq
  nearLitters_bound_eq := h₁.nearLitters_bound_eq
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
  litter_eq_iff_of_flexible hN₁ hN₂ hN₁' hN₂' hN₃' hN₄' := by
    refine ⟨h₁.litter_eq_of_flexible hN₁ hN₂ hN₁' hN₂' hN₃' hN₄', ?_⟩
    have := h₂.litter_eq_of_flexible
      (convNearLitters_inv T S _ ▸ hN₁) (convNearLitters_inv T S _ ▸ hN₂)
    apply this <;> assumption
  atoms_iff_of_inflexible := by
    intro A N₁ N₂ P t ρ hA hN₁ hN₂ hN B a ha i
    constructor
    · exact h₁.atoms_of_inflexible A N₁ N₂ P t ρ hA hN₁ hN₂ hN B a ha i
    · intro hi
      have := h₂.atoms_of_inflexible A N₂ N₁ P (ρ • t) ρ⁻¹ hA hN₂ ?_ ?_ B (ρᵁ B • a) ?_ i hi
      · rwa [allPermForget_inv, Tree.inv_apply, inv_smul_smul] at this
      · rwa [inv_smul_smul]
      · rwa [← convNearLitters_inv]
      · rwa [Tangle.smul_support, Support.smul_derivBot, BaseSupport.smul_atoms,
          Enumeration.mem_smul, inv_smul_smul]
  nearLitters_iff_of_inflexible := by
    intro A N₁ N₂ P t ρ hA hN₁ hN₂ hN B N' hN' i
    constructor
    · exact h₁.nearLitters_of_inflexible A N₁ N₂ P t ρ hA hN₁ hN₂ hN B N' hN' i
    · intro hi
      have := h₂.nearLitters_of_inflexible A N₂ N₁ P (ρ • t) ρ⁻¹ hA hN₂
          ?_ ?_ B (ρᵁ B • N') ?_ i hi
      · rwa [allPermForget_inv, Tree.inv_apply, inv_smul_smul] at this
      · rwa [inv_smul_smul]
      · rwa [← convNearLitters_inv]
      · rwa [Tangle.smul_support, Support.smul_derivBot, BaseSupport.smul_nearLitters,
          Enumeration.mem_smul, inv_smul_smul]

theorem sameSpec_comm {S T : Support β} (h : SameSpec S T) : SameSpec T S where
  atoms_bound_eq A := (h.atoms_bound_eq A).symm
  nearLitters_bound_eq A := (h.nearLitters_bound_eq A).symm
  atoms_dom_eq A := (h.atoms_dom_eq A).symm
  nearLitters_dom_eq A := (h.nearLitters_dom_eq A).symm
  convAtoms_oneOne A := convAtoms_inv S T A ▸ (h.convAtoms_oneOne A).inv
  atomMemRel_eq A := (h.atomMemRel_eq A).symm
  inflexible_iff := by
    intro A N₁ N₂ h' P t hA
    have := h.inflexible_iff (convNearLitters_inv S T A ▸ h') P t hA
    exact this.symm
  litter_eq_iff_of_flexible := by
    intro A N₁ N₂ N₃ N₄ h₁₂ h₃₄ h₁ h₂ h₃ h₄
    have := h.litter_eq_iff_of_flexible
      (convNearLitters_inv S T A ▸ h₁₂) (convNearLitters_inv S T A ▸ h₃₄)
    exact (this h₂ h₁ h₄ h₃).symm
  atoms_iff_of_inflexible := by
    intro A N₁ N₂ P t ρ hA h₁ h₂ h₁₂ B a ha i
    have := h.atoms_iff_of_inflexible A N₂ N₁ P (ρ • t) ρ⁻¹ hA h₂ ?_ ?_ B (ρᵁ B • a) ?_ i
    · simp only [allPermForget_inv, Tree.inv_apply, inv_smul_smul] at this
      exact this.symm
    · rwa [inv_smul_smul]
    · rwa [← convNearLitters_inv]
    · rwa [Tangle.smul_support, Support.smul_derivBot, BaseSupport.smul_atoms,
        Enumeration.mem_smul, inv_smul_smul]
  nearLitters_iff_of_inflexible := by
    intro A N₁ N₂ P t ρ hA h₁ h₂ h₁₂ B N hN i
    have := h.nearLitters_iff_of_inflexible A N₂ N₁ P (ρ • t) ρ⁻¹ hA h₂ ?_ ?_ B (ρᵁ B • N) ?_ i
    · simp only [allPermForget_inv, Tree.inv_apply, inv_smul_smul] at this
      exact this.symm
    · rwa [inv_smul_smul]
    · rwa [← convNearLitters_inv]
    · rwa [Tangle.smul_support, Support.smul_derivBot, BaseSupport.smul_nearLitters,
        Enumeration.mem_smul, inv_smul_smul]

namespace Support

variable {S T : Support β}

theorem atoms_eq_of_spec_eq_spec (h : S.spec = T.spec) (A : β ↝ ⊥) :
    (S ⇘. A)ᴬ.image
      (λ a ↦ (⟨{i | (S ⇘. A)ᴬ.rel i a}, {i | ∃ N, (S ⇘. A)ᴺ.rel i N ∧ a ∈ Nᴬ}⟩ : AtomCond)) =
    (T ⇘. A)ᴬ.image
      (λ a ↦ ⟨{i | (T ⇘. A)ᴬ.rel i a}, {i | ∃ N, (T ⇘. A)ᴺ.rel i N ∧ a ∈ Nᴬ}⟩) :=
  congr_fun (congr_arg (·ᴬ) h) A

theorem nearLitters_eq_of_spec_eq_spec (h : S.spec = T.spec) (A : β ↝ ⊥) :
    (S ⇘. A)ᴺ.comp
      (nearLitterCondRel S A) (nearLitterCondRel_coinjective S A) =
    (T ⇘. A)ᴺ.comp
      (nearLitterCondRel T A) (nearLitterCondRel_coinjective T A) :=
  congr_fun (congr_arg (·ᴺ) h) A

theorem convAtoms_of_spec_eq_spec (h : S.spec = T.spec) {A : β ↝ ⊥} {a b : Atom} :
    convAtoms S T A a b →
    (∀ i, (S ⇘. A)ᴬ.rel i a ↔ (T ⇘. A)ᴬ.rel i b) ∧
    (∀ i, (∃ N, (S ⇘. A)ᴺ.rel i N ∧ a ∈ Nᴬ) ↔ (∃ N, (T ⇘. A)ᴺ.rel i N ∧ b ∈ Nᴬ)) := by
  rintro ⟨i, ha, hb⟩
  have := atoms_eq_of_spec_eq_spec h A
  rw [Enumeration.ext_iff] at this
  have := (iff_of_eq <| congr_fun₂ this.2 i _).mp ⟨a, ha, rfl⟩
  obtain ⟨c, hc₁, hc₂⟩ := this
  rw [AtomCond.mk.injEq] at hc₂
  cases (T ⇘. A)ᴬ.rel_coinjective.coinjective hb hc₁
  rw [Set.ext_iff, Set.ext_iff] at hc₂
  exact ⟨λ x ↦ (hc₂.1 x).symm, λ x ↦ (hc₂.2 x).symm⟩

theorem convNearLitters_of_spec_eq_spec (h : S.spec = T.spec) {A : β ↝ ⊥} {N₁ N₂ : NearLitter} :
    convNearLitters S T A N₁ N₂ →
    ∃ c, nearLitterCondRel S A N₁ c ∧ nearLitterCondRel T A N₂ c := by
  rintro ⟨i, hN₁, hN₂⟩
  obtain ⟨c, hc⟩ := (nearLitterCondRel_cosurjective S A).cosurjective N₁
  have := nearLitters_eq_of_spec_eq_spec h A
  rw [Enumeration.ext_iff] at this
  have := (iff_of_eq <| congr_fun₂ this.2 i c).mp ⟨N₁, hN₁, hc⟩
  obtain ⟨N₃, h₁, h₂⟩ := this
  cases (T ⇘. A)ᴺ.rel_coinjective.coinjective hN₂ h₁
  cases this
  exact ⟨c, hc, h₂⟩

theorem atoms_bound_eq_of_spec_eq_spec (h : S.spec = T.spec) (A : β ↝ ⊥) :
    (S ⇘. A)ᴬ.bound = (T ⇘. A)ᴬ.bound := by
  have := congr_arg Enumeration.bound (congr_fun (congr_arg (·ᴬ) h) A)
  exact this

theorem nearLitters_bound_eq_of_spec_eq_spec (h : S.spec = T.spec) (A : β ↝ ⊥) :
    (S ⇘. A)ᴺ.bound = (T ⇘. A)ᴺ.bound := by
  have := congr_arg Enumeration.bound (congr_fun (congr_arg (·ᴺ) h) A)
  exact this

theorem atoms_dom_subset_of_spec_eq_spec (h : S.spec = T.spec) (A : β ↝ ⊥) :
    (S ⇘. A)ᴬ.rel.dom ⊆ (T ⇘. A)ᴬ.rel.dom := by
  rw [← spec_atoms_dom, ← spec_atoms_dom, h]

theorem nearLitters_dom_subset_of_spec_eq_spec (h : S.spec = T.spec) (A : β ↝ ⊥) :
    (S ⇘. A)ᴺ.rel.dom ⊆ (T ⇘. A)ᴺ.rel.dom := by
  rw [← spec_nearLitters_dom, ← spec_nearLitters_dom, h]

theorem convAtoms_injective_of_spec_eq_spec (h : S.spec = T.spec) (A : β ↝ ⊥) :
    (convAtoms S T A).Injective := by
  constructor
  rintro a₁ a₂ b h₁ ⟨i, hai, hbi⟩
  rw [← (convAtoms_of_spec_eq_spec h h₁).1] at hbi
  exact (S ⇘. A)ᴬ.rel_coinjective.coinjective hbi hai

theorem atomMemRel_le_of_spec_eq_spec (h : S.spec = T.spec) (A : β ↝ ⊥) :
    atomMemRel S A ≤ atomMemRel T A := by
  rintro i j ⟨N, h₁, a, h₂, haS⟩
  obtain ⟨b, hbT⟩ := atoms_dom_subset_of_spec_eq_spec h A ⟨a, haS⟩
  obtain ⟨N', h₁', h₂'⟩ := ((convAtoms_of_spec_eq_spec h ⟨j, haS, hbT⟩).2 i).mp ⟨N, h₁, h₂⟩
  exact ⟨N', h₁', b, h₂', hbT⟩

theorem inflexible_of_inflexible_of_spec_eq_spec (h : S.spec = T.spec) {A : β ↝ ⊥}
    {N₁ N₂ : NearLitter} :
    convNearLitters S T A N₁ N₂ → ∀ (P : InflexiblePath β) (t : Tangle P.δ),
      A = P.A ↘ P.hε ↘. → N₁ᴸ = fuzz P.hδε t → ∃ ρ : AllPerm P.δ, N₂ᴸ = fuzz P.hδε (ρ • t) := by
  intro hN P t hA ht
  obtain ⟨c, hN₁, hN₂⟩ := convNearLitters_of_spec_eq_spec h hN
  obtain (⟨hN₁, _⟩ | ⟨P', t', hA', ht', rfl⟩) := hN₁
  · cases hN₁ ⟨P, t, hA, ht⟩
  cases inflexiblePath_subsingleton hA hA' ht ht'
  cases fuzz_injective (ht.symm.trans ht')
  clear hA' ht'
  obtain ⟨t', -, ht', hχ, h₁, h₂⟩ := nearLitterCondRel_inflex hN₂
  rw [Tangle.code_eq_code_iff] at hχ
  obtain ⟨ρ, rfl⟩ := hχ
  exact ⟨ρ, ht'⟩

theorem litter_eq_of_flexible_of_spec_eq_spec (h : S.spec = T.spec) {A : β ↝ ⊥}
    {N₁ N₂ N₃ N₄ : NearLitter} :
    convNearLitters S T A N₁ N₂ → convNearLitters S T A N₃ N₄ →
    ¬Inflexible A N₁ᴸ → ¬Inflexible A N₂ᴸ → ¬Inflexible A N₃ᴸ → ¬Inflexible A N₄ᴸ →
    N₁ᴸ = N₃ᴸ → N₂ᴸ = N₄ᴸ := by
  intro h₁₂ h₃₄ h₁ h₂ _ _ h₁₃
  obtain ⟨c, hN₁, hN₂⟩ := convNearLitters_of_spec_eq_spec h h₁₂
  obtain (⟨-, rfl⟩ | hN₁) := hN₁
  swap
  · cases h₁ (inflexible_of_mem_dom_nearLitterCondInflexRel ⟨c, hN₁⟩)
  obtain (⟨-, h⟩ | hN₂) := hN₂
  swap
  · cases h₂ (inflexible_of_mem_dom_nearLitterCondInflexRel ⟨_, hN₂⟩)
  rw [NearLitterCond.flex.injEq, FlexCond.mk.injEq, Set.ext_iff] at h
  obtain ⟨i, hi₁, hi₂⟩ := h₃₄
  obtain ⟨N', hN'₁, hN'₂⟩ := (h i).mp ⟨N₃, hi₁, h₁₃⟩
  cases (T ⇘. A)ᴺ.rel_coinjective.coinjective hi₂ hN'₁
  exact hN'₂

theorem atoms_of_inflexible_of_spec_eq_spec (h : S.spec = T.spec) (A : β ↝ ⊥)
    (N₁ N₂ : NearLitter) (P : InflexiblePath β) (t : Tangle P.δ) (ρ : AllPerm P.δ) :
    A = P.A ↘ P.hε ↘. → N₁ᴸ = fuzz P.hδε t → N₂ᴸ = fuzz P.hδε (ρ • t) →
    convNearLitters S T A N₁ N₂ → ∀ (B : P.δ ↝ ⊥), ∀ a ∈ (t.support ⇘. B)ᴬ,
    ∀ i, (S ⇘. (P.A ↘ P.hδ ⇘ B))ᴬ.rel i a → (T ⇘. (P.A ↘ P.hδ ⇘ B))ᴬ.rel i (ρᵁ B • a) := by
  rintro hA ht₁ ht₂ hN B a ⟨j, hj⟩ i h'
  obtain ⟨c, h₁, h₂⟩ := convNearLitters_of_spec_eq_spec h hN
  obtain (⟨h₁, -⟩ | ⟨P', t', hA', ht', rfl⟩) := h₁
  · cases h₁ ⟨P, t, hA, ht₁⟩
  cases inflexiblePath_subsingleton hA hA' ht₁ ht'
  cases fuzz_injective (ht₁.symm.trans ht')
  clear hA' ht'
  obtain ⟨t', -, hN₂, -, hBa, hBN⟩ := nearLitterCondRel_inflex h₂
  cases fuzz_injective (ht₂.symm.trans hN₂)
  simp only [Tangle.smul_support, smul_derivBot, BaseSupport.smul_atoms,
    BaseSupport.smul_nearLitters] at hBa
  conv at hBa =>
    rw [funext_iff]; intro
    rw [funext_iff]; intro
    rw [funext_iff]; intro
    rw [eq_iff_iff]
  obtain ⟨b, hb₁, hb₂⟩ := (hBa B i j).mp ⟨a, h', hj⟩
  cases (t.support ⇘. B)ᴬ.rel_coinjective.coinjective hj hb₂
  rwa [smul_inv_smul]

theorem nearLitters_of_inflexible_of_spec_eq_spec (h : S.spec = T.spec) (A : β ↝ ⊥)
    (N₁ N₂ : NearLitter) (P : InflexiblePath β) (t : Tangle P.δ) (ρ : AllPerm P.δ) :
    A = P.A ↘ P.hε ↘. → N₁ᴸ = fuzz P.hδε t → N₂ᴸ = fuzz P.hδε (ρ • t) →
    convNearLitters S T A N₁ N₂ → ∀ (B : P.δ ↝ ⊥), ∀ N ∈ (t.support ⇘. B)ᴺ,
    ∀ i, (S ⇘. (P.A ↘ P.hδ ⇘ B))ᴺ.rel i N → (T ⇘. (P.A ↘ P.hδ ⇘ B))ᴺ.rel i (ρᵁ B • N) := by
  rintro hA ht₁ ht₂ hN B N ⟨j, hj⟩ i h'
  obtain ⟨c, h₁, h₂⟩ := convNearLitters_of_spec_eq_spec h hN
  obtain (⟨h₁, -⟩ | ⟨P', t', hA', ht', rfl⟩) := h₁
  · cases h₁ ⟨P, t, hA, ht₁⟩
  cases inflexiblePath_subsingleton hA hA' ht₁ ht'
  cases fuzz_injective (ht₁.symm.trans ht')
  clear hA' ht'
  obtain ⟨t', -, hN₂, -, hBa, hBN⟩ := nearLitterCondRel_inflex h₂
  cases fuzz_injective (ht₂.symm.trans hN₂)
  simp only [Tangle.smul_support, smul_derivBot, BaseSupport.smul_nearLitters,
    BaseSupport.smul_nearLitters] at hBN
  conv at hBN =>
    rw [funext_iff]; intro
    rw [funext_iff]; intro
    rw [funext_iff]; intro
    rw [eq_iff_iff]
  obtain ⟨b, hb₁, hb₂⟩ := (hBN B i j).mp ⟨N, h', hj⟩
  cases (t.support ⇘. B)ᴺ.rel_coinjective.coinjective hj hb₂
  rwa [smul_inv_smul]

theorem sameSpecLe_of_spec_eq_spec (h : S.spec = T.spec) :
    SameSpecLE S T where
  atoms_bound_eq := atoms_bound_eq_of_spec_eq_spec h
  nearLitters_bound_eq := nearLitters_bound_eq_of_spec_eq_spec h
  atoms_dom_subset := atoms_dom_subset_of_spec_eq_spec h
  nearLitters_dom_subset := nearLitters_dom_subset_of_spec_eq_spec h
  convAtoms_injective := convAtoms_injective_of_spec_eq_spec h
  atomMemRel_le := atomMemRel_le_of_spec_eq_spec h
  inflexible_of_inflexible := inflexible_of_inflexible_of_spec_eq_spec h
  litter_eq_of_flexible := litter_eq_of_flexible_of_spec_eq_spec h
  atoms_of_inflexible := atoms_of_inflexible_of_spec_eq_spec h
  nearLitters_of_inflexible := nearLitters_of_inflexible_of_spec_eq_spec h

theorem atoms_subset_of_sameSpec (h : SameSpec S T) {A : β ↝ ⊥} {i : κ} {a b : Atom}
    (ha : (S ⇘. A)ᴬ.rel i a) (hb : (T ⇘. A)ᴬ.rel i b) :
    {i | (T ⇘. A)ᴬ.rel i b} ⊆ {i | (S ⇘. A)ᴬ.rel i a} := by
  intro j hj
  rw [Set.mem_setOf_eq] at hj
  obtain ⟨c, hc⟩ := (sameSpec_comm h).atoms_dom_of_dom hj
  cases (h.convAtoms_oneOne A).injective ⟨i, ha, hb⟩ ⟨j, hc, hj⟩
  exact hc

theorem nearLitters_subset_of_sameSpec (h : SameSpec S T) {A : β ↝ ⊥} {i : κ} {a b : Atom}
    (ha : (S ⇘. A)ᴬ.rel i a) (hb : (T ⇘. A)ᴬ.rel i b) :
    {i | ∃ N, (T ⇘. A)ᴺ.rel i N ∧ b ∈ Nᴬ} ⊆ {i | ∃ N, (S ⇘. A)ᴺ.rel i N ∧ a ∈ Nᴬ} := by
  intro j hj
  obtain ⟨N, hN₁, hN₂⟩ := hj
  obtain ⟨N', hN'⟩ := (sameSpec_comm h).nearLitters_dom_of_dom hN₁
  refine ⟨N', hN', ?_⟩
  have := h.atomMemRel_eq A
  rw [atomMemRel, atomMemRel] at this
  conv at this =>
    rw [funext_iff]; intro
    rw [funext_iff]; intro
    rw [eq_iff_iff]
  obtain ⟨N'', hN'', c, hc₁, hc₂⟩ := (this j i).mpr ⟨N, hN₁, b, hN₂, hb⟩
  cases (S ⇘. A)ᴺ.rel_coinjective.coinjective hN' hN''
  cases (S ⇘. A)ᴬ.rel_coinjective.coinjective ha hc₂
  exact hc₁

theorem nearLitterCondRelFlex_of_convNearLitters_aux (h : SameSpec S T) {A : β ↝ ⊥}
    {N₁ N₂ : NearLitter} (hN : convNearLitters S T A N₁ N₂)
    (hN₁i : ¬Inflexible A N₁ᴸ) (hN₂i : ¬Inflexible A N₂ᴸ) (i : κ) :
    (∃ N₃, (S ⇘. A)ᴺ.rel i N₃ ∧ N₁ᴸ = N₃ᴸ) → ∃ N₃, (T ⇘. A)ᴺ.rel i N₃ ∧ N₂ᴸ = N₃ᴸ := by
  rintro ⟨N₃, hN₃, hN₃'⟩
  obtain ⟨N₄, hN₄⟩ := h.nearLitters_dom_of_dom hN₃
  refine ⟨N₄, hN₄, ?_⟩
  rw [← h.litter_eq_iff_of_flexible hN ⟨i, hN₃, hN₄⟩ hN₁i hN₂i]
  · exact hN₃'
  · rwa [← hN₃']
  · apply (h.inflexible_iff' ⟨i, hN₃, hN₄⟩).mpr.mt
    rwa [← hN₃']

theorem nearLitterCondRelFlex_of_convNearLitters (h : SameSpec S T) {A : β ↝ ⊥}
    {N₁ N₂ : NearLitter} (hN : convNearLitters S T A N₁ N₂)
    (hN₁i : ¬Inflexible A N₁ᴸ) (hN₂i : ¬Inflexible A N₂ᴸ) :
    nearLitterCondRelFlex T A N₂ (.flex ⟨{i | ∃ N₃, (S ⇘. A)ᴺ.rel i N₃ ∧ N₁ᴸ = N₃ᴸ}⟩) := by
  use hN₂i
  rw [NearLitterCond.flex.injEq, FlexCond.mk.injEq]
  ext i
  constructor
  · exact nearLitterCondRelFlex_of_convNearLitters_aux h hN hN₁i hN₂i i
  · refine nearLitterCondRelFlex_of_convNearLitters_aux (sameSpec_comm h) ?_ hN₂i hN₁i i
    rwa [← convNearLitters_inv]

theorem nearLitterCondRelInflex_of_convNearLitters (h : SameSpec S T) {A : β ↝ ⊥}
    {N₁ N₂ : NearLitter} (hN : convNearLitters S T A N₁ N₂)
    (P : InflexiblePath β) (t : Tangle P.δ) (ρ : AllPerm P.δ)
    (hA : A = P.A ↘ P.hε ↘.) (hN₁ : N₁ᴸ = fuzz P.hδε t) (hN₂ : N₂ᴸ = fuzz P.hδε (ρ • t)) :
    nearLitterCondRelInflex T A N₂
      (.inflex P ⟨t.code,
        λ B ↦ (S ⇘. (P.A ↘ P.hδ ⇘ B))ᴬ.rel.comp (t.support ⇘. B)ᴬ.rel.inv,
        λ B ↦ (S ⇘. (P.A ↘ P.hδ ⇘ B))ᴺ.rel.comp (t.support ⇘. B)ᴺ.rel.inv⟩) := by
  refine ⟨P, ρ • t, hA, hN₂, ?_⟩
  rw [NearLitterCond.inflex.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  rw [InflexCond.mk.injEq]
  refine ⟨(t.smul_code ρ).symm, ?_, ?_⟩
  · funext B i j
    rw [eq_iff_iff]
    have := h.atoms_iff_of_inflexible A N₁ N₂ P t ρ hA hN₁ hN₂ hN B
    constructor
    · rintro ⟨a, ha₁, ha₂⟩
      have := (this a ⟨j, ha₂⟩ i).mp ha₁
      refine ⟨ρᵁ B • a, this, ?_⟩
      rwa [Tangle.smul_support, smul_derivBot, BaseSupport.smul_atoms, Rel.inv_apply,
        Enumeration.smul_rel, inv_smul_smul]
    · rintro ⟨a, ha₁, ha₂⟩
      have := (this ((ρᵁ B)⁻¹ • a) ⟨j, ha₂⟩ i).mpr ?_
      · exact ⟨(ρᵁ B)⁻¹ • a, this, ha₂⟩
      · rwa [smul_inv_smul]
  · funext B i j
    rw [eq_iff_iff]
    have := h.nearLitters_iff_of_inflexible A N₁ N₂ P t ρ hA hN₁ hN₂ hN B
    constructor
    · rintro ⟨N', hN'₁, hN'₂⟩
      have := (this N' ⟨j, hN'₂⟩ i).mp hN'₁
      refine ⟨ρᵁ B • N', this, ?_⟩
      rwa [Tangle.smul_support, smul_derivBot, BaseSupport.smul_nearLitters, Rel.inv_apply,
        Enumeration.smul_rel, inv_smul_smul]
    · rintro ⟨N', hN'₁, hN'₂⟩
      have := (this ((ρᵁ B)⁻¹ • N') ⟨j, hN'₂⟩ i).mpr ?_
      · exact ⟨(ρᵁ B)⁻¹ • N', this, hN'₂⟩
      · rwa [smul_inv_smul]

theorem spec_le_spec_of_sameSpec (h : SameSpec S T) :
    S.spec ≤ T.spec := by
  intro A
  simp only [spec_atoms, spec_nearLitters]
  refine ⟨h.atoms_bound_eq A, ?_, h.nearLitters_bound_eq A, ?_⟩
  · rintro i _ ⟨a, ha, rfl⟩
    obtain ⟨b, hb⟩ := h.atoms_dom_of_dom ha
    refine ⟨b, hb, ?_⟩
    rw [AtomCond.mk.injEq]
    constructor
    · apply subset_antisymm
      exact atoms_subset_of_sameSpec h ha hb
      exact atoms_subset_of_sameSpec (sameSpec_comm h) hb ha
    · apply subset_antisymm
      exact nearLitters_subset_of_sameSpec h ha hb
      exact nearLitters_subset_of_sameSpec (sameSpec_comm h) hb ha
  · rintro i c ⟨N₁, hN₁, hN'⟩
    obtain ⟨N₂, hN₂⟩ := h.nearLitters_dom_of_dom hN₁
    obtain ⟨hN₁i, rfl⟩ | ⟨P, t, hA, ht, rfl⟩ := hN'
    · have hN₂i := (h.inflexible_iff' ⟨i, hN₁, hN₂⟩).mpr.mt hN₁i
      refine ⟨N₂, hN₂, Or.inl ?_⟩
      exact nearLitterCondRelFlex_of_convNearLitters h ⟨i, hN₁, hN₂⟩ hN₁i hN₂i
    · have hN₂i := (h.inflexible_iff ⟨i, hN₁, hN₂⟩ P t hA).mp ⟨1, by rwa [one_smul]⟩
      obtain ⟨ρ, hρ⟩ := hN₂i
      refine ⟨N₂, hN₂, Or.inr ?_⟩
      exact nearLitterCondRelInflex_of_convNearLitters h ⟨i, hN₁, hN₂⟩ P t ρ hA ht hρ

theorem spec_eq_spec_iff (S T : Support β) :
    S.spec = T.spec ↔ SameSpec S T := by
  constructor
  · intro h
    exact sameSpec_antisymm (sameSpecLe_of_spec_eq_spec h) (sameSpecLe_of_spec_eq_spec h.symm)
  · intro h
    apply le_antisymm
    exact spec_le_spec_of_sameSpec h
    exact spec_le_spec_of_sameSpec (sameSpec_comm h)

end Support

end ConNF
