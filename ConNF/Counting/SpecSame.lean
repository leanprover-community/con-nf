import ConNF.FOA.StrActionFOA
import ConNF.Counting.Strong
import ConNF.Counting.Spec

/-!
# Supports with the same specification

In this file, we show that two strong supports with the same specification are related by
an allowable permutation.

## Main declarations

* `ConNF.exists_allPerm_of_spec_eq_spec`: Two strong supports with the same specification are
  related by an allowable permutation.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}] [Level] [CoherentData] {β : TypeIndex} [LeLevel β] {S T : Support β}

namespace Support

theorem atom_mem_of_mem_of_spec_eq_spec (hST : S.spec = T.spec)
    {a₁ a₂ : Atom} {N₁ N₂ : NearLitter} {A : β ↝ ⊥}
    (ha : convAtoms S T A a₁ a₂) (hN : convNearLitters S T A N₁ N₂) (haN : a₁ ∈ N₁ᴬ) :
    a₂ ∈ N₂ᴬ := by
  rw [spec_eq_spec_iff] at hST
  obtain ⟨i, ha₁, ha₂⟩ := ha
  obtain ⟨j, hN₁, hN₂⟩ := hN
  obtain ⟨N₃, hN₃, a₃, haN', ha₃⟩ :=
    (iff_of_eq (congr_fun₂ (hST.atomMemRel_eq A) j i)).mp ⟨N₁, hN₁, a₁, haN, ha₁⟩
  cases (T ⇘. A)ᴬ.rel_coinjective.coinjective ha₂ ha₃
  cases (T ⇘. A)ᴺ.rel_coinjective.coinjective hN₂ hN₃
  exact haN'

theorem atom_mem_iff_mem_of_spec_eq_spec (hST : S.spec = T.spec)
    {a₁ a₂ : Atom} {N₁ N₂ : NearLitter} {A : β ↝ ⊥}
    (ha : convAtoms S T A a₁ a₂) (hN : convNearLitters S T A N₁ N₂) :
    a₁ ∈ N₁ᴬ ↔ a₂ ∈ N₂ᴬ :=
  ⟨atom_mem_of_mem_of_spec_eq_spec hST ha hN,
    atom_mem_of_mem_of_spec_eq_spec hST.symm
      (convAtoms_inv T S A ▸ ha) (convNearLitters_inv S T A ▸ hN)⟩

theorem litter_eq_litter_of_convNearLitters_of_spec_eq_spec (hST : S.spec = T.spec) (hT : T.Strong)
    {N₁ N₂ N₃ N₄ : NearLitter} {A : β ↝ ⊥}
    (hN₁₃ : convNearLitters S T A N₁ N₃) (hN₂₄ : convNearLitters S T A N₂ N₄) (hN₁₂ : N₁ᴸ = N₂ᴸ) :
    N₃ᴸ = N₄ᴸ := by
  rw [spec_eq_spec_iff] at hST
  obtain (⟨P, t, hA, ht⟩ | hN₁) := inflexible_cases A N₁ᴸ
  · have := (hST.inflexible_iff hN₁₃ P t hA).mp ⟨1, ?_⟩
    swap
    · rwa [one_smul]
    obtain ⟨ρ₁, hρ₁⟩ := this
    have := (hST.inflexible_iff hN₂₄ P t hA).mp ⟨1, ?_⟩
    swap
    · rwa [one_smul, ← hN₁₂]
    obtain ⟨ρ₂, hρ₂⟩ := this
    suffices ρ₁ • t = ρ₂ • t by
      rwa [this, ← hρ₂] at hρ₁
    apply Tangle.smul_eq_smul
    apply ext
    intro B
    apply BaseSupport.ext
    · simp only [smul_derivBot, BaseSupport.smul_atoms]
      apply Enumeration.ext
      · rfl
      ext i a
      constructor
      · intro ha
        have h₁ := hST.atoms_iff_of_inflexible A N₁ N₃ P t ρ₁ hA ht hρ₁ hN₁₃ B
          ((ρ₁ᵁ B)⁻¹ • a) ⟨i, ha⟩
        have h₂ := hST.atoms_iff_of_inflexible A N₂ N₄ P t ρ₂ hA (hN₁₂ ▸ ht) hρ₂ hN₂₄ B
          ((ρ₁ᵁ B)⁻¹ • a) ⟨i, ha⟩
        have ⟨j, _, hjT⟩ := hN₁₃
        obtain ⟨k, hk⟩ := (hT.support_le ⟨j, hjT⟩ P (ρ₁ • t) hA hρ₁ B).1 a ⟨i, ha⟩
        simp_rw [smul_inv_smul] at h₁
        have := (T ⇘. _)ᴬ.rel_coinjective.coinjective hk ((h₂ k).mp ((h₁ k).mpr hk))
        rw [← inv_smul_eq_iff] at this
        dsimp only at this
        simp only [Enumeration.smul_rel] at ha ⊢
        rwa [this]
      · intro ha
        have h₁ := hST.atoms_iff_of_inflexible A N₁ N₃ P t ρ₁ hA ht hρ₁ hN₁₃ B
          ((ρ₂ᵁ B)⁻¹ • a) ⟨i, ha⟩
        have h₂ := hST.atoms_iff_of_inflexible A N₂ N₄ P t ρ₂ hA (hN₁₂ ▸ ht) hρ₂ hN₂₄ B
          ((ρ₂ᵁ B)⁻¹ • a) ⟨i, ha⟩
        have ⟨j, _, hjT⟩ := hN₂₄
        obtain ⟨k, hk⟩ := (hT.support_le ⟨j, hjT⟩ P (ρ₂ • t) hA hρ₂ B).1 a ⟨i, ha⟩
        simp_rw [smul_inv_smul] at h₂
        have := (T ⇘. _)ᴬ.rel_coinjective.coinjective hk ((h₁ k).mp ((h₂ k).mpr hk))
        rw [← inv_smul_eq_iff] at this
        dsimp only at this
        simp only [Enumeration.smul_rel] at ha ⊢
        rwa [this]
    · simp only [smul_derivBot, BaseSupport.smul_nearLitters]
      apply Enumeration.ext
      · rfl
      ext i N
      constructor
      · intro hN
        have h₁ := hST.nearLitters_iff_of_inflexible A N₁ N₃ P t ρ₁ hA ht hρ₁ hN₁₃ B
          ((ρ₁ᵁ B)⁻¹ • N) ⟨i, hN⟩
        have h₂ := hST.nearLitters_iff_of_inflexible A N₂ N₄ P t ρ₂ hA (hN₁₂ ▸ ht) hρ₂ hN₂₄ B
          ((ρ₁ᵁ B)⁻¹ • N) ⟨i, hN⟩
        have ⟨j, _, hjT⟩ := hN₁₃
        obtain ⟨k, hk⟩ := (hT.support_le ⟨j, hjT⟩ P (ρ₁ • t) hA hρ₁ B).2 N ⟨i, hN⟩
        simp_rw [smul_inv_smul] at h₁
        have := (T ⇘. _)ᴺ.rel_coinjective.coinjective hk ((h₂ k).mp ((h₁ k).mpr hk))
        rw [← inv_smul_eq_iff] at this
        dsimp only at this
        simp only [Enumeration.smul_rel] at hN ⊢
        rwa [this]
      · intro hN
        have h₁ := hST.nearLitters_iff_of_inflexible A N₁ N₃ P t ρ₁ hA ht hρ₁ hN₁₃ B
          ((ρ₂ᵁ B)⁻¹ • N) ⟨i, hN⟩
        have h₂ := hST.nearLitters_iff_of_inflexible A N₂ N₄ P t ρ₂ hA (hN₁₂ ▸ ht) hρ₂ hN₂₄ B
          ((ρ₂ᵁ B)⁻¹ • N) ⟨i, hN⟩
        have ⟨j, _, hjT⟩ := hN₂₄
        obtain ⟨k, hk⟩ := (hT.support_le ⟨j, hjT⟩ P (ρ₂ • t) hA hρ₂ B).2 N ⟨i, hN⟩
        simp_rw [smul_inv_smul] at h₂
        have := (T ⇘. _)ᴺ.rel_coinjective.coinjective hk ((h₁ k).mp ((h₂ k).mpr hk))
        rw [← inv_smul_eq_iff] at this
        dsimp only at this
        simp only [Enumeration.smul_rel] at hN ⊢
        rwa [this]
  · have hN₂ : ¬Inflexible A N₂ᴸ := hN₁₂ ▸ hN₁
    have hN₃ := (hST.inflexible_iff' hN₁₃).mpr.mt hN₁
    have hN₄ := (hST.inflexible_iff' hN₂₄).mpr.mt hN₂
    exact (hST.litter_eq_iff_of_flexible hN₁₃ hN₂₄ hN₁ hN₃ hN₂ hN₄).mp hN₁₂

-- TODO: Fix blueprint: we need both that T is strong and that S is strong.
theorem litter_eq_litter_iff_of_convNearLitters_of_spec_eq_spec (hST : S.spec = T.spec)
    (hS : S.Strong) (hT : T.Strong) {N₁ N₂ N₃ N₄ : NearLitter} {A : β ↝ ⊥}
    (hN₁₃ : convNearLitters S T A N₁ N₃) (hN₂₄ : convNearLitters S T A N₂ N₄) :
    N₁ᴸ = N₂ᴸ ↔ N₃ᴸ = N₄ᴸ :=
  ⟨litter_eq_litter_of_convNearLitters_of_spec_eq_spec hST hT hN₁₃ hN₂₄,
    litter_eq_litter_of_convNearLitters_of_spec_eq_spec hST.symm hS
      (convNearLitters_inv S T A ▸ hN₁₃) (convNearLitters_inv T S A ▸ hN₂₄)⟩

theorem interference_subset_convAtoms_dom (hST : S.spec = T.spec) (hS : S.Strong)
    {N₁ N₂ : NearLitter} {A : β ↝ ⊥}
    (hN₁ : N₁ ∈ (convNearLitters S T A).dom) (hN₂ : N₂ ∈ (convNearLitters S T A).dom) :
    interference N₁ N₂ ⊆ (convAtoms S T A).dom := by
  intro a ha
  obtain ⟨N₃, i, hiS, hiT⟩ := hN₁
  obtain ⟨N₄, j, hjS, hjT⟩ := hN₂
  obtain ⟨k, hkS⟩ := hS.interference_subset ⟨i, hiS⟩ ⟨j, hjS⟩ a ha
  rw [spec_eq_spec_iff] at hST
  obtain ⟨a', hkT⟩ := hST.atoms_dom_of_dom hkS
  exact ⟨a', k, hkS, hkT⟩

theorem interference_subset_convAtoms_codom (hST : S.spec = T.spec) (hT : T.Strong)
    {N₁ N₂ : NearLitter} {A : β ↝ ⊥}
    (hN₁ : N₁ ∈ (convNearLitters S T A).codom) (hN₂ : N₂ ∈ (convNearLitters S T A).codom) :
    interference N₁ N₂ ⊆ (convAtoms S T A).codom := by
  intro a ha
  obtain ⟨N₃, i, hiS, hiT⟩ := hN₁
  obtain ⟨N₄, j, hjS, hjT⟩ := hN₂
  obtain ⟨k, hkT⟩ := hT.interference_subset ⟨i, hiT⟩ ⟨j, hjT⟩ a ha
  rw [spec_eq_spec_iff] at hST
  obtain ⟨a', hkS⟩ := (sameSpec_comm hST).atoms_dom_of_dom hkT
  exact ⟨a', k, hkS, hkT⟩

def convDeriv (hST : S.spec = T.spec) (hS : S.Strong) (hT : T.Strong) (A : β ↝ ⊥) : BaseAction where
  atoms := convAtoms S T A
  nearLitters := convNearLitters S T A
  atoms_dom_small' := by
    apply Small.mono (convAtoms_dom_subset S T A)
    exact (S ⇘. A)ᴬ.coe_small
  nearLitters_dom_small' := by
    apply Small.mono (convNearLitters_dom_subset S T A)
    exact (S ⇘. A)ᴺ.coe_small
  atoms_oneOne' := by
    rw [spec_eq_spec_iff] at hST
    exact hST.convAtoms_oneOne A
  mem_iff_mem' := by
    rintro a₁ a₂ N₁ N₂ ⟨i, hiS, hiT⟩ ⟨j, hjS, hjT⟩
    rw [spec_eq_spec_iff] at hST
    constructor
    · intro ha
      obtain ⟨N₃, hN₃T, a₃, haN₃, ha₃T⟩ := (iff_of_eq (congr_fun₂ (hST.atomMemRel_eq A) j i)).mp
        ⟨N₁, hjS, a₁, ha, hiS⟩
      cases (T ⇘. A)ᴬ.rel_coinjective.coinjective hiT ha₃T
      cases (T ⇘. A)ᴺ.rel_coinjective.coinjective hjT hN₃T
      exact haN₃
    · intro ha
      obtain ⟨N₃, hN₃S, a₃, haN₃, ha₃S⟩ := (iff_of_eq (congr_fun₂ (hST.atomMemRel_eq A) j i)).mpr
        ⟨N₂, hjT, a₂, ha, hiT⟩
      cases (S ⇘. A)ᴬ.rel_coinjective.coinjective hiS ha₃S
      cases (S ⇘. A)ᴺ.rel_coinjective.coinjective hjS hN₃S
      exact haN₃
  litter_eq_litter_iff' := litter_eq_litter_iff_of_convNearLitters_of_spec_eq_spec hST hS hT
  interference_subset_dom' := interference_subset_convAtoms_dom hST hS
  interference_subset_codom' := interference_subset_convAtoms_codom hST hT

abbrev conv (hST : S.spec = T.spec) (hS : S.Strong) (hT : T.Strong) : StrAction β :=
  convDeriv hST hS hT

end Support

end ConNF
