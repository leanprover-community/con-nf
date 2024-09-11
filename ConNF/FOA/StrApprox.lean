import ConNF.Setup.CoherentData
import ConNF.FOA.BaseApprox

/-!
# Structural approximations

In this file, we define structural approximations, which are trees of base approximations.

## Main declarations

* `ConNF.StrApprox`: The type of structural approximations.
* `ConNF.InflexiblePath`: A pair of paths starting at `β` that describe a particular way to use
    a `fuzz` map.
* `ConNF.Inflexible`: A litter is said to be inflexible along a path if it can be obtained by
    applying a `fuzz` map along this path.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}] {β : TypeIndex}

abbrev StrApprox : TypeIndex → Type u :=
  Tree BaseApprox

namespace StrApprox

section addOrbit

open scoped Classical in
def addOrbit (ψ : StrApprox β) (A : β ↝ ⊥) (f : ℤ → Litter)
    (hf : ∀ m n k, f m = f n → f (m + k) = f (n + k)) (hfψ : ∀ n, f n ∉ (ψ A)ᴸ.dom) : StrApprox β :=
  λ B ↦ if h : A = B then (ψ B).addOrbit f hf (h ▸ hfψ) else ψ B

variable {ψ : StrApprox β} {A : β ↝ ⊥} {f : ℤ → Litter}
    {hf : ∀ m n k, f m = f n → f (m + k) = f (n + k)} {hfψ : ∀ n, f n ∉ (ψ A)ᴸ.dom}

theorem addOrbit_apply :
    ψ.addOrbit A f hf hfψ A = (ψ A).addOrbit f hf hfψ := by
  rw [addOrbit, dif_pos]
  rfl

theorem addOrbit_apply_ne (B : β ↝ ⊥) (hB : A ≠ B) :
    ψ.addOrbit A f hf hfψ B = ψ B := by
  rw [addOrbit, dif_neg hB]

theorem le_addOrbit :
    ψ ≤ ψ.addOrbit A f hf hfψ := by
  intro B
  by_cases hB : A = B
  · cases hB
    rw [addOrbit_apply]
    exact BaseApprox.le_addOrbit
  · rw [addOrbit_apply_ne B hB]

end addOrbit

instance : SMul (StrApprox β) (Support β) where
  smul ψ S := ⟨Sᴬ.comp (Enumeration.relWithPath λ A ↦ (ψ A)ᴬ)
      (Enumeration.relWithPath_coinjective λ A ↦ (ψ A).atoms_permutative.toCoinjective),
    Sᴺ.comp (Enumeration.relWithPath λ A ↦ (ψ A)ᴺ)
      (Enumeration.relWithPath_coinjective λ A ↦ (ψ A).nearLitters_permutative.toCoinjective)⟩

@[simp]
theorem smul_support_derivBot (ψ : StrApprox β) (S : Support β) (A : β ↝ ⊥) :
    (ψ • S) ⇘. A = ψ A • (S ⇘. A) := by
  ext : 2; rfl; swap; rfl
  all_goals
  · ext i a
    constructor
    · rintro ⟨⟨B, b⟩, h₁, h₂⟩
      cases h₂.1
      exact ⟨b, h₁, h₂.2⟩
    · rintro ⟨b, h₁, h₂⟩
      exact ⟨⟨A, b⟩, h₁, rfl, h₂⟩

theorem smul_support_eq_smul_iff (ψ : StrApprox β) (S : Support β) (π : StrPerm β) :
    ψ • S = π • S ↔ ∀ A,
      (∀ a ∈ (S ⇘. A)ᴬ, (ψ A)ᴬ a (π A • a)) ∧ (∀ N ∈ (S ⇘. A)ᴺ, (ψ A)ᴺ N (π A • N)) := by
  simp only [Support.ext_iff, smul_support_derivBot, Support.smul_derivBot,
    BaseApprox.smul_support_eq_smul_iff]

theorem smul_support_smul_eq_iff (ψ : StrApprox β) (S : Support β) (π : StrPerm β) :
    ψ • π • S = S ↔ ∀ A,
      (∀ a ∈ ((π • S) ⇘. A)ᴬ, (ψ A)ᴬ a (π⁻¹ A • a)) ∧
      (∀ N ∈ ((π • S) ⇘. A)ᴺ, (ψ A)ᴺ N (π⁻¹ A • N)) := by
  have := smul_support_eq_smul_iff ψ (π • S) π⁻¹
  rw [inv_smul_smul] at this
  rw [this]

/-- An upper bound for a chain of approximations. -/
def upperBound (c : Set (StrApprox β)) (hc : IsChain (· ≤ ·) c) : StrApprox β :=
  λ A ↦ BaseApprox.upperBound ((· A) '' c) (hc.image _ _ (λ _ _ h ↦ h A))

theorem le_upperBound (c : Set (StrApprox β)) (hc : IsChain (· ≤ ·) c) :
    ∀ ψ ∈ c, ψ ≤ upperBound c hc :=
  λ ψ hψ _ ↦ BaseApprox.le_upperBound _ _ _ ⟨ψ, hψ, rfl⟩

theorem exists_isMax (ψ : StrApprox β) : ∃ χ ≥ ψ, IsMax χ := by
  have := zorn_le₀ {χ | ψ ≤ χ} ?_
  · obtain ⟨χ, hχ₁, hχ₂⟩ := this
    refine ⟨χ, hχ₁, ?_⟩
    intro χ' h
    exact hχ₂ (hχ₁.trans h) h
  · intro c hc₁ hc₂
    obtain rfl | hc₃ := c.eq_empty_or_nonempty
    · refine ⟨ψ, ?_, ?_⟩
      · exact le_refl ψ
      · simp only [Set.mem_empty_iff_false, false_implies, implies_true]
    · obtain ⟨ψ', hψ'⟩ := hc₃
      exact ⟨upperBound c hc₂, (hc₁ hψ').trans (le_upperBound c hc₂ ψ' hψ'), le_upperBound c hc₂⟩

end StrApprox

@[ext]
structure InflexiblePath (β : TypeIndex) where
  γ : TypeIndex
  δ : TypeIndex
  ε : Λ
  hδ : δ < γ
  hε : ε < γ
  hδε : δ ≠ ε
  A : β ↝ γ

instance {β β' : TypeIndex} : Coderivative (InflexiblePath β) (InflexiblePath β') β' β where
  coderiv P B := ⟨P.γ, P.δ, P.ε, P.hδ, P.hε, P.hδε, B ⇘ P.A⟩

@[simp]
theorem InflexiblePath.coderiv_A {β β' : TypeIndex} (P : InflexiblePath β) (B : β' ↝ β) :
    (P ⇗ B).A = B ⇘ P.A :=
  rfl

variable [Level] [CoherentData]

instance [LeLevel β] (P : InflexiblePath β) : LeLevel P.γ :=
  ⟨P.A.le.trans LeLevel.elim⟩

instance [LeLevel β] (P : InflexiblePath β) : LtLevel P.δ :=
  ⟨P.hδ.trans_le LeLevel.elim⟩

instance [LeLevel β] (P : InflexiblePath β) : LtLevel P.ε :=
  ⟨P.hε.trans_le LeLevel.elim⟩

def Inflexible [LeLevel β] (A : β ↝ ⊥) (L : Litter) : Prop :=
  ∃ P : InflexiblePath β, ∃ t, A = P.A ↘ P.hε ↘. ∧ L = fuzz P.hδε t

theorem inflexible_iff [LeLevel β] (A : β ↝ ⊥) (L : Litter) :
    Inflexible A L ↔ ∃ P : InflexiblePath β, ∃ t, A = P.A ↘ P.hε ↘. ∧ L = fuzz P.hδε t :=
  Iff.rfl

theorem not_inflexible_iff [LeLevel β] (A : β ↝ ⊥) (L : Litter) :
    ¬Inflexible A L ↔ ∀ P : InflexiblePath β, ∀ t, A = P.A ↘ P.hε ↘. → L ≠ fuzz P.hδε t := by
  rw [inflexible_iff]
  push_neg
  rfl

theorem inflexible_deriv [LeLevel β] {A : β ↝ ⊥} {L : Litter} (h : Inflexible A L)
    {β' : TypeIndex} [LeLevel β'] (B : β' ↝ β) :
    Inflexible (B ⇘ A) L := by
  obtain ⟨P, t, hA, ht⟩ := h
  refine ⟨P ⇗ B, t, ?_, ht⟩
  rw [hA]
  rfl

theorem inflexible_cases [LeLevel β] (A : β ↝ ⊥) (L : Litter) :
    (∃ P : InflexiblePath β, ∃ t, A = P.A ↘ P.hε ↘. ∧ L = fuzz P.hδε t) ∨ ¬Inflexible A L :=
  Classical.em _

theorem inflexiblePath_subsingleton [LeLevel β] {A : β ↝ ⊥} {L : Litter}
    {P₁ P₂ : InflexiblePath β} {t₁ : Tangle P₁.δ} {t₂ : Tangle P₂.δ}
    (hP₁ : A = P₁.A ↘ P₁.hε ↘.) (hP₂ : A = P₂.A ↘ P₂.hε ↘.)
    (ht₁ : L = fuzz P₁.hδε t₁) (ht₂ : L = fuzz P₂.hδε t₂) :
    P₁ = P₂ := by
  subst hP₁
  subst ht₁
  have := fuzz_β_eq ht₂ -- δ₁ = δ₂
  obtain ⟨γ₁, δ₁, ε₁, _, _, _, A₁⟩ := P₁
  obtain ⟨γ₂, δ₂, ε₂, _, _, _, A₂⟩ := P₂
  cases this
  cases Path.sderivBot_index_injective hP₂ -- ε₁ = ε₂
  cases Path.sderiv_index_injective (Path.sderivBot_path_injective hP₂) -- γ₁ = γ₂
  cases Path.sderiv_path_injective (Path.sderivBot_path_injective hP₂) -- A₁ = A₂
  rfl

namespace StrApprox

/-- `ψ` is defined coherently at `(A, L₁, L₂)` (or could be defined coherently at this triple). -/
structure CoherentAt [LeLevel β]
    (ψ : StrApprox β) (A : β ↝ ⊥) (L₁ L₂ : Litter) : Prop where
  inflexible (P : InflexiblePath β) (t : Tangle P.δ)
    (hA : A = P.A ↘ P.hε ↘.) (ht : L₁ = fuzz P.hδε t) :
    ∃ ρ : AllPerm P.δ, ψ ⇘ P.A ↘ P.hδ • t.support = ρᵁ • t.support ∧ L₂ = fuzz P.hδε (ρ • t)
  flexible (h : ¬Inflexible A L₁) : ¬Inflexible A L₂

theorem coherentAt_inflexible [LeLevel β] {ψ : StrApprox β} {A : β ↝ ⊥} {L₁ L₂ : Litter}
    {P : InflexiblePath β} {t : Tangle P.δ} (hA : A = P.A ↘ P.hε ↘.) (ht : L₁ = fuzz P.hδε t) :
    ψ.CoherentAt A L₁ L₂ ↔ ∃ ρ : AllPerm P.δ,
      ψ ⇘ P.A ↘ P.hδ • t.support = ρᵁ • t.support ∧ L₂ = fuzz P.hδε (ρ • t) := by
  constructor
  · intro h
    exact h.inflexible P t hA ht
  · intro h
    constructor
    · intro P' t' hA' ht'
      cases inflexiblePath_subsingleton hA hA' ht ht'
      cases fuzz_injective (ht.symm.trans ht')
      exact h
    · intro h'
      cases h' ⟨P, t, hA, ht⟩

theorem smul_eq_of_coherentAt_inflexible [LeLevel β] {ψ : StrApprox β} {A : β ↝ ⊥} {L₁ L₂ : Litter}
    {P : InflexiblePath β} {t : Tangle P.δ} (hA : A = P.A ↘ P.hε ↘.) (ht : L₁ = fuzz P.hδε t)
    (h : ψ.CoherentAt A L₁ L₂) :
    ∀ ρ : AllPerm P.δ, ψ ⇘ P.A ↘ P.hδ • t.support = ρᵁ • t.support → L₂ = fuzz P.hδε (ρ • t) := by
  intro ρ₁ hρ₁
  rw [coherentAt_inflexible hA ht] at h
  obtain ⟨ρ₂, hρ₂, rfl⟩ := h
  congr 1
  apply t.smul_eq_smul
  rw [← hρ₁, ← hρ₂]

theorem coherentAt_flexible [LeLevel β] {ψ : StrApprox β} {A : β ↝ ⊥} {L₁ L₂ : Litter}
    (hL : ¬Inflexible A L₁) :
    ψ.CoherentAt A L₁ L₂ ↔ ¬Inflexible A L₂ := by
  constructor
  · intro h
    exact h.flexible hL
  · intro h
    constructor
    · intro P t hA ht
      cases hL ⟨P, t, hA, ht⟩
    · intro
      exact h

theorem coherentAt_inflexible' [LeLevel β] {ψ : StrApprox β} {A : β ↝ ⊥} {L₁ L₂ : Litter}
    {P : InflexiblePath β} {t : Tangle P.δ} (hA : A = P.A ↘ P.hε ↘.) (ht : L₂ = fuzz P.hδε t) :
    ψ.CoherentAt A L₁ L₂ ↔ ∃ ρ : AllPerm P.δ,
      ψ ⇘ P.A ↘ P.hδ • ρᵁ • t.support = t.support ∧ L₁ = fuzz P.hδε (ρ • t) := by
  constructor
  · intro h
    obtain (⟨P', t', hA', ht'⟩ | hL) := inflexible_cases A L₁
    · obtain ⟨ρ, h₁, h₂⟩ := h.inflexible P' t' hA' ht'
      cases inflexiblePath_subsingleton hA hA' ht h₂
      cases fuzz_injective <| ht.symm.trans h₂
      use ρ⁻¹
      rw [inv_smul_smul, Tangle.smul_support, ht', allPermForget_inv, inv_smul_smul, h₁]
      exact ⟨rfl, rfl⟩
    · rw [coherentAt_flexible hL] at h
      cases h ⟨P, t, hA, ht⟩
  · intro h
    obtain ⟨ρ, h₁, h₂⟩ := h
    constructor
    · intro P' t' hA' ht'
      cases inflexiblePath_subsingleton hA hA' h₂ ht'
      cases fuzz_injective <| h₂.symm.trans ht'
      refine ⟨ρ⁻¹, ?_, ?_⟩
      · rwa [Tangle.smul_support, allPermForget_inv, inv_smul_smul]
      · rwa [inv_smul_smul]
    · intro h
      cases h ⟨P, ρ • t, hA, h₂⟩

theorem smul_eq_of_coherentAt_inflexible' [LeLevel β] {ψ : StrApprox β} {A : β ↝ ⊥} {L₁ L₂ : Litter}
    {P : InflexiblePath β} {t : Tangle P.δ} (hA : A = P.A ↘ P.hε ↘.) (ht : L₂ = fuzz P.hδε t)
    (h : ψ.CoherentAt A L₁ L₂) :
    ∀ ρ : AllPerm P.δ, ψ ⇘ P.A ↘ P.hδ • ρᵁ • t.support = t.support → L₁ = fuzz P.hδε (ρ • t) := by
  intro ρ₁ hρ₁
  rw [coherentAt_inflexible' hA ht] at h
  obtain ⟨ρ₂, hρ₂, rfl⟩ := h
  congr 1
  apply t.smul_eq_smul
  rw [smul_support_smul_eq_iff] at hρ₁ hρ₂
  ext B : 1
  rw [Support.smul_derivBot, Support.smul_derivBot, BaseSupport.smul_eq_smul_iff]
  constructor
  · rintro a ha
    have h₁ := (hρ₁ B).1 (ρ₁ᵁ B • a) ?_
    have h₂ := (hρ₂ B).1 (ρ₂ᵁ B • a) ?_
    · rw [Tree.inv_apply, inv_smul_smul] at h₁ h₂
      exact (BaseApprox.atoms_permutative _).injective h₂ h₁
    · rwa [Support.smul_derivBot, BaseSupport.smul_atoms, Enumeration.mem_smul_iff, inv_smul_smul]
    · rwa [Support.smul_derivBot, BaseSupport.smul_atoms, Enumeration.mem_smul_iff, inv_smul_smul]
  · rintro N hN
    have h₁ := (hρ₁ B).2 (ρ₁ᵁ B • N) ?_
    have h₂ := (hρ₂ B).2 (ρ₂ᵁ B • N) ?_
    · rw [Tree.inv_apply, inv_smul_smul] at h₁ h₂
      exact (BaseApprox.nearLitters_permutative _).injective h₂ h₁
    · rwa [Support.smul_derivBot, BaseSupport.smul_nearLitters,
        Enumeration.mem_smul_iff, inv_smul_smul]
    · rwa [Support.smul_derivBot, BaseSupport.smul_nearLitters,
        Enumeration.mem_smul_iff, inv_smul_smul]

theorem CoherentAt.mono [LeLevel β] {ψ χ : StrApprox β} {A : β ↝ ⊥} {L₁ L₂ : Litter}
    (h : ψ.CoherentAt A L₁ L₂) (hψχ : ψ ≤ χ) : χ.CoherentAt A L₁ L₂ := by
  obtain (⟨P, t, hA, hL⟩ | hL) := inflexible_cases A L₁
  · rw [coherentAt_inflexible hA hL] at h ⊢
    obtain ⟨ρ, hρ₁, hρ₂⟩ := h
    refine ⟨ρ, ?_, hρ₂⟩
    rw [smul_support_eq_smul_iff] at hρ₁ ⊢
    simp only [Tree.sderiv_apply, Tree.deriv_apply] at hρ₁ ⊢
    intro B
    constructor
    · intro a ha
      apply BaseApprox.atoms_le_of_le (hψχ (P.A ⇘ (B ↗ P.hδ)))
      exact (hρ₁ B).1 a ha
    · intro a ha
      apply BaseApprox.nearLitters_le_of_le (hψχ (P.A ⇘ (B ↗ P.hδ)))
      exact (hρ₁ B).2 a ha
  · rwa [coherentAt_flexible hL] at h ⊢

def Coherent [LeLevel β] (ψ : StrApprox β) : Prop :=
  ∀ A L₁ L₂, (ψ A)ᴸ L₁ L₂ → ψ.CoherentAt A L₁ L₂

theorem addOrbit_coherent [LeLevel β] {ψ : StrApprox β} {A : β ↝ ⊥} {f : ℤ → Litter}
    {hf : ∀ m n k, f m = f n → f (m + k) = f (n + k)} {hfψ : ∀ n, f n ∉ (ψ A)ᴸ.dom}
    (hψ : ψ.Coherent) (hfc : ∀ n, ψ.CoherentAt A (f n) (f (n + 1))) :
    (ψ.addOrbit A f hf hfψ).Coherent := by
  intro B L₁ L₂
  by_cases hB : A = B
  · subst hB
    rw [addOrbit_apply, BaseApprox.addOrbit_litters]
    rintro (hL | ⟨n, rfl, rfl⟩)
    · exact (hψ A L₁ L₂ hL).mono le_addOrbit
    · exact (hfc n).mono le_addOrbit
  · rw [addOrbit_apply_ne B hB]
    intro hL
    exact (hψ B L₁ L₂ hL).mono le_addOrbit

theorem Coherent.comp [LeLevel β] {ψ : StrApprox β} (hψ : ψ.Coherent)
    {γ : TypeIndex} [LeLevel γ] (A : β ↝ γ) :
    Coherent (ψ ⇘ A) := by
  intro B L₁ L₂ h
  specialize hψ (A ⇘ B) L₁ L₂ h
  constructor
  · intro P t hA ht
    have := hψ.inflexible (P ⇗ A) t ?_ ht
    · obtain ⟨ρ, hρ₁, hρ₂⟩ := this
      refine ⟨ρ, ?_, hρ₂⟩
      rwa [InflexiblePath.coderiv_A, ← Tree.deriv_deriv] at hρ₁
    · rw [hA]
      rfl
  · intro hL₁ hL₂
    obtain (hL₁' | hL₁') := inflexible_cases (A ⇘ B) L₁
    · obtain ⟨P, t, rfl, ht⟩ := hL₂
      obtain ⟨P', t', hA', ht'⟩ := hL₁'
      suffices P' = P ⇗ A by
        cases this
        cases hL₁ ⟨P, t', rfl, ht'⟩
      rw [coherentAt_inflexible hA' ht'] at hψ
      obtain ⟨ρ, hρ₁, hρ₂⟩ := hψ
      rw [Path.deriv_sderivBot, Path.deriv_sderiv] at hA'
      exact inflexiblePath_subsingleton hA' rfl hρ₂ ht
    · cases hψ.flexible hL₁' (inflexible_deriv hL₂ A)

end StrApprox

end ConNF
