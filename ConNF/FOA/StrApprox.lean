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

variable [Level.{u}] [CoherentData]

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

end StrApprox

end ConNF
