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
(convAtoms_of_inflexible : ∀ A, ∀ N₁ N₂ : NearLitter,
  ∀ P : InflexiblePath β, ∀ t : Tangle P.δ, ∀ ρ : AllPerm P.δ,
  A = P.A ↘ P.hε ↘. → N₁ᴸ = fuzz P.hδε t → N₂ᴸ = fuzz P.hδε (ρ • t) →
  convNearLitters S T A N₁ N₂ → ∀ B : P.δ ↝ ⊥,
    convAtoms (S ⇘ (P.A ↘ P.hδ)) (T ⇘ (P.A ↘ P.hδ)) B ⊓ (λ a _ ↦ a ∈ (t.support ⇘. B)ᴬ) ≤
      (λ a b ↦ b = ρᵁ ⇘. B • a))
(convNearLitters_of_inflexible : ∀ A, ∀ N₁ N₂ : NearLitter,
  ∀ P : InflexiblePath β, ∀ t : Tangle P.δ, ∀ ρ : AllPerm P.δ,
  A = P.A ↘ P.hε ↘. → N₁ᴸ = fuzz P.hδε t → N₂ᴸ = fuzz P.hδε (ρ • t) →
  convNearLitters S T A N₁ N₂ → ∀ B : P.δ ↝ ⊥,
    convNearLitters (S ⇘ (P.A ↘ P.hδ)) (T ⇘ (P.A ↘ P.hδ)) B ⊓ (λ a _ ↦ a ∈ (t.support ⇘. B)ᴺ) ≤
      (λ N₁ N₂ ↦ N₂ = ρᵁ ⇘. B • N₁))

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
(convAtoms_of_inflexible : ∀ A, ∀ N₁ N₂ : NearLitter,
  ∀ P : InflexiblePath β, ∀ t : Tangle P.δ, ∀ ρ : AllPerm P.δ,
  A = P.A ↘ P.hε ↘. → N₁ᴸ = fuzz P.hδε t → N₂ᴸ = fuzz P.hδε (ρ • t) →
  convNearLitters S T A N₁ N₂ → ∀ B : P.δ ↝ ⊥,
    convAtoms (S ⇘ (P.A ↘ P.hδ)) (T ⇘ (P.A ↘ P.hδ)) B ⊓ (λ a _ ↦ a ∈ (t.support ⇘. B)ᴬ) ≤
      (λ a b ↦ b = ρᵁ ⇘. B • a))
(convNearLitters_of_inflexible : ∀ A, ∀ N₁ N₂ : NearLitter,
  ∀ P : InflexiblePath β, ∀ t : Tangle P.δ, ∀ ρ : AllPerm P.δ,
  A = P.A ↘ P.hε ↘. → N₁ᴸ = fuzz P.hδε t → N₂ᴸ = fuzz P.hδε (ρ • t) →
  convNearLitters S T A N₁ N₂ → ∀ B : P.δ ↝ ⊥,
    convNearLitters (S ⇘ (P.A ↘ P.hδ)) (T ⇘ (P.A ↘ P.hδ)) B ⊓ (λ a _ ↦ a ∈ (t.support ⇘. B)ᴺ) ≤
      (λ N₁ N₂ ↦ N₂ = ρᵁ ⇘. B • N₁))

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
  convAtoms_of_inflexible := h₁.convAtoms_of_inflexible
  convNearLitters_of_inflexible := h₁.convNearLitters_of_inflexible

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

theorem convAtoms_of_inflexible_of_spec_eq_spec (h : S.spec = T.spec) (A : β ↝ ⊥)
    (N₁ N₂ : NearLitter) (P : InflexiblePath β) (t : Tangle P.δ) (ρ : AllPerm P.δ) :
    A = P.A ↘ P.hε ↘. → N₁ᴸ = fuzz P.hδε t → N₂ᴸ = fuzz P.hδε (ρ • t) →
    convNearLitters S T A N₁ N₂ → ∀ (B : P.δ ↝ ⊥),
      (convAtoms (S ⇘ (P.A ↘ P.hδ)) (T ⇘ (P.A ↘ P.hδ)) B ⊓ λ a _ ↦ a ∈ (t.support ⇘. B)ᴬ) ≤
      λ a b ↦ b = ρᵁ ⇘. B • a := by
  rintro hA ht₁ ht₂ hN B a b ⟨hab, ha⟩
  obtain ⟨c, h₁, h₂⟩ := convNearLitters_of_spec_eq_spec h hN
  obtain (⟨h₁, -⟩ | ⟨P', t', hA', ht', rfl⟩) := h₁
  · cases h₁ ⟨P, t, hA, ht₁⟩
  cases inflexiblePath_subsingleton hA hA' ht₁ ht'
  cases fuzz_injective (ht₁.symm.trans ht')
  clear hA' ht'
  obtain ⟨t', -, hN₂, -, hBa, hBN⟩ := nearLitterCondRel_inflex h₂
  cases fuzz_injective (ht₂.symm.trans hN₂)
  obtain ⟨i, hi₁, hi₂⟩ := hab
  obtain ⟨j, hj⟩ := ha
  obtain ⟨b', hb'₁, hb'₂⟩ := (iff_of_eq <| congr_fun₃ hBa B i j).mp ⟨a, hi₁, hj⟩
  cases (Enumeration.rel_coinjective _).coinjective hi₂ hb'₁
  rw [Tangle.smul_support, smul_derivBot, BaseSupport.smul_atoms] at hb'₂
  cases (t.support ⇘. B)ᴬ.rel_coinjective.coinjective hj hb'₂
  rw [Tree.botDeriv_eq, smul_inv_smul]

theorem convNearLitters_of_inflexible_of_spec_eq_spec (h : S.spec = T.spec) (A : β ↝ ⊥)
    (N₁ N₂ : NearLitter) (P : InflexiblePath β) (t : Tangle P.δ) (ρ : AllPerm P.δ) :
    A = P.A ↘ P.hε ↘. → N₁ᴸ = fuzz P.hδε t → N₂ᴸ = fuzz P.hδε (ρ • t) →
    convNearLitters S T A N₁ N₂ → ∀ (B : P.δ ↝ ⊥),
      (convNearLitters (S ⇘ (P.A ↘ P.hδ)) (T ⇘ (P.A ↘ P.hδ)) B ⊓ λ N _ ↦ N ∈ (t.support ⇘. B)ᴺ) ≤
      λ N₁' N₂' ↦ N₂' = ρᵁ ⇘. B • N₁' := by
  rintro hA ht₁ ht₂ hN B N₁' N₂' ⟨hab, ha⟩
  obtain ⟨c, h₁, h₂⟩ := convNearLitters_of_spec_eq_spec h hN
  obtain (⟨h₁, -⟩ | ⟨P', t', hA', ht', rfl⟩) := h₁
  · cases h₁ ⟨P, t, hA, ht₁⟩
  cases inflexiblePath_subsingleton hA hA' ht₁ ht'
  cases fuzz_injective (ht₁.symm.trans ht')
  clear hA' ht'
  obtain ⟨t', -, hN₂, -, hBa, hBN⟩ := nearLitterCondRel_inflex h₂
  cases fuzz_injective (ht₂.symm.trans hN₂)
  obtain ⟨i, hi₁, hi₂⟩ := hab
  obtain ⟨j, hj⟩ := ha
  obtain ⟨N₃', hN'₁, hN'₂⟩ := (iff_of_eq <| congr_fun₃ hBN B i j).mp ⟨N₁', hi₁, hj⟩
  cases (Enumeration.rel_coinjective _).coinjective hi₂ hN'₁
  rw [Tangle.smul_support, smul_derivBot, BaseSupport.smul_nearLitters] at hN'₂
  cases (t.support ⇘. B)ᴺ.rel_coinjective.coinjective hj hN'₂
  rw [Tree.botDeriv_eq, smul_inv_smul]

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
  convAtoms_of_inflexible := convAtoms_of_inflexible_of_spec_eq_spec h
  convNearLitters_of_inflexible := convNearLitters_of_inflexible_of_spec_eq_spec h

theorem atoms_eq_of_sameSpec (h : SameSpec S T) {A : β ↝ ⊥} {i : κ} {a b : Atom}
    (ha : (S ⇘. A)ᴬ.rel i a) (hb : (T ⇘. A)ᴬ.rel i b) :
    {i | (T ⇘. A)ᴬ.rel i b} = {i | (S ⇘. A)ᴬ.rel i a} := by
  ext j : 1
  constructor
  · intro hj
    rw [Set.mem_setOf_eq] at hj
    have hdom := h.atoms_dom_eq A
    rw [Set.ext_iff] at hdom
    obtain ⟨c, hc⟩ := (hdom j).mpr ⟨b, hj⟩
    cases (h.convAtoms_oneOne A).injective ⟨i, ha, hb⟩ ⟨j, hc, hj⟩
    exact hc
  · sorry

theorem spec_le_spec_of_sameSpec (h : SameSpec S T) :
    S.spec ≤ T.spec := by
  intro A
  simp only [spec_atoms, spec_nearLitters]
  refine ⟨h.atoms_bound_eq A, ?_, h.nearLitters_bound_eq A, ?_⟩
  · rintro i _ ⟨a, ha, rfl⟩
    have hdom := h.atoms_dom_eq A
    rw [Set.ext_iff] at hdom
    obtain ⟨b, hb⟩ := (hdom i).mp ⟨a, ha⟩
    refine ⟨b, hb, ?_⟩
    rw [AtomCond.mk.injEq]
    exact ⟨atoms_eq_of_sameSpec h ha hb, sorry⟩
  · sorry

theorem spec_eq_spec_iff (S T : Support β) :
    S.spec = T.spec ↔ SameSpec S T := by
  constructor
  · intro h
    exact sameSpec_antisymm (sameSpecLe_of_spec_eq_spec h) (sameSpecLe_of_spec_eq_spec h.symm)
  · sorry

end Support

end ConNF
