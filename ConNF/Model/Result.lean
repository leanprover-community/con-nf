import ConNF.Model.Union

namespace ConNF

noncomputable local instance : Params := minimalParams

variable {α β γ δ ε ζ : Λ} (hβ : β < α) (hγ : γ < β) (hδ : δ < γ) (hε : ε < δ) (hζ : ζ < ε)

theorem ext (t₁ t₂ : TSet α) :
    (∀ s, s ∈[hβ] t₁ ↔ s ∈[hβ] t₂) → t₁ = t₂ :=
  TangleData.TSet.ext hβ t₁ t₂

theorem inter {t₁ t₂ : TSet α} :
    ∃ t, ∀ s, s ∈[hβ] t ↔ s ∈[hβ] t₁ ∧ s ∈[hβ] t₂ := by
  refine ⟨t₁.inter hβ t₂, ?_⟩
  simp only [TangleData.TSet.inter, TangleData.TSet.mem_mk_iff, Set.mem_setOf_eq, implies_true]

theorem compl {t : TSet α} :
    ∃ t', ∀ s, s ∈[hβ] t' ↔ ¬s ∈[hβ] t := by
  refine ⟨t.compl hβ, ?_⟩
  simp only [TangleData.TSet.compl, TangleData.TSet.mem_mk_iff, Set.mem_setOf_eq, implies_true]

theorem mem_singleton_iff (t : TSet β) (s : TSet β) :
    s ∈[hβ] .singleton hβ t ↔ s = t :=
  TangleData.TSet.mem_singleton_iff hβ t s

theorem mem_up_iff (t₁ t₂ : TSet β) (s : TSet β) :
    s ∈[hβ] .up hβ t₁ t₂ ↔ s = t₁ ∨ s = t₂ :=
  TangleData.TSet.mem_up_iff hβ t₁ t₂ s

theorem mem_op_iff (t₁ t₂ : TSet γ) (s : TSet β) :
    s ∈[hβ] .op hβ hγ t₁ t₂ ↔ s = .singleton hγ t₁ ∨ s = .up hγ t₁ t₂ :=
  TangleData.TSet.mem_op_iff hβ hγ t₁ t₂ s

theorem singletonImage (t : TSet β) :
    ∃ t', ∀ a b,
      .op hγ hδ (.singleton hε a) (.singleton hε b) ∈[hβ] t' ↔ .op hδ hε a b ∈[hγ] t := by
  refine ⟨t.singletonImage hβ hγ hδ hε, ?_⟩
  intro a b
  simp only [TangleData.TSet.singletonImage, TangleData.TSet.mem_mk_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a', b', h₁, h₂⟩
    have := op_injective _ _ _ _ _ _ h₂
    cases singleton_injective' _ _ _ this.1
    cases singleton_injective' _ _ _ this.2
    exact h₁
  · intro h
    exact ⟨a, b, h, rfl⟩

theorem insertion2 (t : TSet γ) :
    ∃ t', ∀ a b c, .op hγ hδ (.singleton hε (.singleton hζ a)) (.op hε hζ b c) ∈[hβ] t' ↔
      .op hε hζ a c ∈[hδ] t := by
  refine ⟨t.insertion2 hβ hγ hδ hε hζ, ?_⟩
  intro a b c
  simp only [TangleData.TSet.insertion2, TangleData.TSet.mem_mk_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a', b', c', h₁, h₂⟩
    have := op_injective _ _ _ _ _ _ h₂
    cases singleton_injective' _ _ _ (singleton_injective' _ _ _  this.1)
    obtain ⟨rfl, rfl⟩ := op_injective _ _ _ _ _ _ this.2
    exact h₁
  · intro h
    exact ⟨a, b, c, h, rfl⟩

theorem insertion3 (t : TSet γ) :
    ∃ t', ∀ a b c, .op hγ hδ (.singleton hε (.singleton hζ a)) (.op hε hζ b c) ∈[hβ] t' ↔
      .op hε hζ a b ∈[hδ] t := by
  refine ⟨t.insertion3 hβ hγ hδ hε hζ, ?_⟩
  intro a b c
  simp only [TangleData.TSet.insertion3, TangleData.TSet.mem_mk_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a', b', c', h₁, h₂⟩
    have := op_injective _ _ _ _ _ _ h₂
    cases singleton_injective' _ _ _ (singleton_injective' _ _ _  this.1)
    obtain ⟨rfl, rfl⟩ := op_injective _ _ _ _ _ _ this.2
    exact h₁
  · intro h
    exact ⟨a, b, c, h, rfl⟩

theorem cross (t : TSet γ) :
    ∃ t', ∀ a, a ∈[hβ] t' ↔ ∃ b c, a = .op hγ hδ b c ∧ c ∈[hδ] t := by
  refine ⟨t.cross hβ hγ hδ, ?_⟩
  intro a
  simp only [TangleData.TSet.cross, TangleData.TSet.mem_mk_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a', b', h, rfl⟩
    exact ⟨a', b', rfl, h⟩
  · rintro ⟨b, c, rfl, h⟩
    exact ⟨b, c, h, rfl⟩

theorem typeLower (t : TSet α) :
    ∃ t', ∀ a, a ∈[hε] t' ↔ ∀ b, .op hγ hδ b (.singleton hε a) ∈[hβ] t := by
  refine ⟨.mk hε {a | ∀ b : TSet δ, .op hγ hδ b (.singleton hε a) ∈[hβ] t} ?_, ?_⟩
  · refine symmetric_of_image_singleton_symmetric hδ hε ?_ ?_
    refine symmetric_of_image_singleton_symmetric hγ hδ ?_ ?_
    refine symmetric_of_image_singleton_symmetric hβ hγ ?_ ?_
    convert t.typeLower'_supported hβ hγ hδ hε using 1
    aesop
  · simp only [TangleData.TSet.mem_mk_iff, Set.mem_setOf_eq, implies_true]

theorem converse (t : TSet α) :
    ∃ t', ∀ a b, .op hγ hδ a b ∈[hβ] t' ↔ .op hγ hδ b a ∈[hβ] t := by
  refine ⟨t.converse hβ hγ hδ, ?_⟩
  intro a b
  simp only [TangleData.TSet.converse, TangleData.TSet.mem_mk_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a', b', h₁, h₂⟩
    obtain ⟨rfl, rfl⟩ := op_injective _ _ _ _ _ _ h₂
    exact h₁
  · intro h
    exact ⟨b, a, h, rfl⟩

theorem cardinalOne :
    ∃ t, ∀ a, a ∈[hβ] t ↔ ∃ b, ∀ c, c ∈[hγ] a ↔ c = b := by
  refine ⟨TangleData.TSet.cardinalOne hβ hγ, ?_⟩
  intro a
  simp only [TangleData.TSet.cardinalOne, TangleData.TSet.mem_mk_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    intro b
    rw [TangleData.TSet.mem_singleton_iff]
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    refine ext hγ _ _ ?_
    intro c
    rw [hb, TangleData.TSet.mem_singleton_iff]

theorem subset :
    ∃ t, ∀ a b, .op hγ hδ a b ∈[hβ] t ↔ ∀ c, c ∈[hε] a → c ∈[hε] b := by
  refine ⟨TangleData.TSet.subset hβ hγ hδ hε, ?_⟩
  intro a b
  simp only [TangleData.TSet.subset, TangleData.TSet.mem_mk_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a', b', h₁, h₂⟩
    obtain ⟨rfl, rfl⟩ := op_injective _ _ _ _ _ _ h₂
    exact h₁
  · intro h
    exact ⟨a, b, h, rfl⟩

end ConNF
