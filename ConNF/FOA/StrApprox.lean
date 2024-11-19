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

/-- An upper bound for a chain of approximations. -/
def upperBound (c : Set (StrApprox β)) (hc : IsChain (· ≤ ·) c) : StrApprox β :=
  λ A ↦ BaseApprox.upperBound ((· A) '' c) (hc.image _ _ _ (λ _ _ h ↦ h A))

theorem le_upperBound (c : Set (StrApprox β)) (hc : IsChain (· ≤ ·) c) :
    ∀ ψ ∈ c, ψ ≤ upperBound c hc :=
  λ ψ hψ _ ↦ BaseApprox.le_upperBound _ _ _ ⟨ψ, hψ, rfl⟩

theorem upperBound_exceptions (c : Set (StrApprox β)) (hc : IsChain (· ≤ ·) c)
    (A : β ↝ ⊥) (a₁ a₂ : Atom) :
    (upperBound c hc A).exceptions a₁ a₂ ↔ ∃ ψ ∈ c, (ψ A).exceptions a₁ a₂ := by
  simp only [upperBound, BaseApprox.upperBound]
  rw [Rel.biSup_apply_iff]
  simp only [Set.mem_image, exists_exists_and_eq_and]

theorem upperBound_litters (c : Set (StrApprox β)) (hc : IsChain (· ≤ ·) c)
    (A : β ↝ ⊥) (L₁ L₂ : Litter) :
    (upperBound c hc A)ᴸ L₁ L₂ ↔ ∃ ψ ∈ c, (ψ A)ᴸ L₁ L₂ := by
  simp only [upperBound, BaseApprox.upperBound, BaseApprox.mk_litters]
  rw [Rel.biSup_apply_iff]
  simp only [Set.mem_image, exists_exists_and_eq_and]

theorem upperBound_typical (c : Set (StrApprox β)) (hc : IsChain (· ≤ ·) c)
    (A : β ↝ ⊥) (a₁ a₂ : Atom) :
    (upperBound c hc A).typical a₁ a₂ ↔ ∃ ψ ∈ c, (ψ A).typical a₁ a₂ := by
  simp only [BaseApprox.typical_iff, upperBound_litters]
  constructor
  · rintro ⟨⟨ψ, hψ, ha⟩, i, h⟩
    refine ⟨ψ, hψ, ha, i, ?_⟩
    rw [BaseApprox.sublitter_eq_of_le (le_upperBound c hc ψ hψ A),
      BaseApprox.sublitter_eq_of_le (le_upperBound c hc ψ hψ A)]
    exact h
  · rintro ⟨ψ, hψ, ha, i, h⟩
    refine ⟨⟨ψ, hψ, ha⟩, i, ?_⟩
    rw [BaseApprox.sublitter_eq_of_le (le_upperBound c hc ψ hψ A),
      BaseApprox.sublitter_eq_of_le (le_upperBound c hc ψ hψ A)] at h
    exact h

theorem upperBound_atoms (c : Set (StrApprox β)) (hc : IsChain (· ≤ ·) c)
    (A : β ↝ ⊥) (a₁ a₂ : Atom) :
    (upperBound c hc A)ᴬ a₁ a₂ ↔ ∃ ψ ∈ c, (ψ A)ᴬ a₁ a₂ := by
  simp only [BaseApprox.atoms_def, Rel.sup_apply, upperBound_exceptions, upperBound_typical]
  constructor
  · rintro (⟨ψ, hψ, h⟩ | ⟨ψ, hψ, h⟩)
    · exact ⟨ψ, hψ, Or.inl h⟩
    · exact ⟨ψ, hψ, Or.inr h⟩
  · rintro ⟨ψ, hψ, h | h⟩
    · exact Or.inl ⟨ψ, hψ, h⟩
    · exact Or.inr ⟨ψ, hψ, h⟩

/-! TODO: Many of the previous lemmas are not actually needed! -/

def Total (ψ : StrApprox β) : Prop :=
  ∀ A, (ψ A).Total

theorem Total.deriv {ψ : StrApprox β} (hψ : ψ.Total) {γ : TypeIndex} (A : β ↝ γ) :
    Total (ψ ⇘ A) :=
  λ B L ↦ hψ (A ⇘ B) L

theorem smul_support_eq_smul_mono
    {ξ χ : StrApprox β} {S : Support β} {π : StrPerm β}
    (hξ : ξ • S = π • S) (hξχ : ξ ≤ χ) :
    χ • S = π • S := by
  rw [smul_support_eq_smul_iff] at hξ ⊢
  intro A
  constructor
  · intro a ha
    exact BaseApprox.atoms_le_of_le (hξχ A) _ _ ((hξ A).1 a ha)
  · intro N hN
    exact BaseApprox.nearLitters_le_of_le (hξχ A) _ _ ((hξ A).2 N hN)

variable [Level] [CoherentData]

theorem coherentAt_mono [LeLevel β] {ψ χ : StrApprox β} {A : β ↝ ⊥} {L₁ L₂ : Litter}
    (h : CoherentAt ψ A L₁ L₂) (hψχ : ψ ≤ χ) : CoherentAt χ A L₁ L₂ := by
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
  ∀ A L₁ L₂, (ψ A)ᴸ L₁ L₂ → CoherentAt ψ A L₁ L₂

theorem addOrbit_coherent [LeLevel β] {ψ : StrApprox β} {A : β ↝ ⊥} {f : ℤ → Litter}
    {hf : ∀ m n k, f m = f n → f (m + k) = f (n + k)} {hfψ : ∀ n, f n ∉ (ψ A)ᴸ.dom}
    (hψ : ψ.Coherent) (hfc : ∀ n, CoherentAt ψ A (f n) (f (n + 1))) :
    (ψ.addOrbit A f hf hfψ).Coherent := by
  intro B L₁ L₂
  by_cases hB : A = B
  · subst hB
    rw [addOrbit_apply, BaseApprox.addOrbit_litters]
    rintro (hL | ⟨n, rfl, rfl⟩)
    · exact coherentAt_mono (hψ A L₁ L₂ hL) le_addOrbit
    · exact coherentAt_mono (hfc n) le_addOrbit
  · rw [addOrbit_apply_ne B hB]
    intro hL
    exact coherentAt_mono (hψ B L₁ L₂ hL) le_addOrbit

theorem Coherent.deriv [LeLevel β] {ψ : StrApprox β} (hψ : ψ.Coherent)
    {γ : TypeIndex} [LeLevel γ] (A : β ↝ γ) :
    Coherent (ψ ⇘ A) :=
  λ B L₁ L₂ h ↦ (hψ (A ⇘ B) L₁ L₂ h).deriv

theorem upperBound_coherent [LeLevel β] (c : Set (StrApprox β)) (hc₁ : IsChain (· ≤ ·) c)
    (hc₂ : ∀ ψ ∈ c, ψ.Coherent) :
    (upperBound c hc₁).Coherent := by
  intro A L₁ L₂ hL
  rw [upperBound_litters] at hL
  obtain ⟨ψ, hψ, hL⟩ := hL
  specialize hc₂ ψ hψ A L₁ L₂ hL
  constructor
  · intro P t hA ht
    obtain ⟨ρ, hρ₁, hρ₂⟩ := hc₂.inflexible P t hA ht
    refine ⟨ρ, ?_, hρ₂⟩
    apply smul_support_eq_smul_mono hρ₁
    intro
    exact le_upperBound c hc₁ ψ hψ _
  · exact hc₂.flexible

theorem exists_maximal_coherent [LeLevel β] (ψ : StrApprox β) (hψ : ψ.Coherent) :
    ∃ χ ≥ ψ, Maximal {χ | χ.Coherent} χ := by
  have := zorn_le₀ {χ | ψ ≤ χ ∧ χ.Coherent} ?_
  · obtain ⟨χ, hχ₁, hχ₂⟩ := this
    refine ⟨χ, hχ₁.1, hχ₁.2, ?_⟩
    intro χ' h₁ h₂
    exact hχ₂ ⟨hχ₁.1.trans h₂, h₁⟩ h₂
  · intro c hc₁ hc₂
    obtain rfl | hc₃ := c.eq_empty_or_nonempty
    · refine ⟨ψ, ?_, ?_⟩
      · exact ⟨le_refl ψ, hψ⟩
      · simp only [Set.mem_empty_iff_false, false_implies, implies_true]
    · obtain ⟨ψ', hψ'⟩ := hc₃
      refine ⟨upperBound c hc₂, ?_, le_upperBound c hc₂⟩
      refine ⟨?_, upperBound_coherent c hc₂ (λ χ hχ ↦ (hc₁ hχ).2)⟩
      exact ((hc₁ hψ').1).trans (le_upperBound c hc₂ ψ' hψ')

end StrApprox

end ConNF
