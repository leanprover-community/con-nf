import ConNF.FOA.StrActionFOA
import ConNF.Counting.Strong
import ConNF.Counting.Spec

/-!
# Supports with the same specification

In this file, we show that two strong supports with the same specification are related by
an allowable permutation.

## Main declarations

* `ConNF.exists_conv`: Two strong supports with the same specification are related by an allowable
  permutation.
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
  · have := (hST.inflexible_iff hN₁₃ P t hA).mp ⟨1, by rwa [one_smul]⟩
    obtain ⟨ρ₁, hρ₁⟩ := this
    have := (hST.inflexible_iff hN₂₄ P t hA).mp ⟨1, by rwa [one_smul, ← hN₁₂]⟩
    obtain ⟨ρ₂, hρ₂⟩ := this
    suffices ρ₁ • t = ρ₂ • t by
      rwa [this, ← hρ₂] at hρ₁
    apply Tangle.smul_eq_smul
    rw [smul_eq_smul_iff]
    intro B
    constructor
    · rintro a ⟨i, ha⟩
      have h₁ := hST.atoms_iff_of_inflexible A N₁ N₃ P t ρ₁ hA ht hρ₁ hN₁₃ B a ⟨i, ha⟩
      have h₂ := hST.atoms_iff_of_inflexible A N₂ N₄ P t ρ₂ hA (hN₁₂ ▸ ht) hρ₂ hN₂₄ B a ⟨i, ha⟩
      have ⟨j, _, hjT⟩ := hN₁₃
      have := (hT.support_le ⟨j, hjT⟩ P (ρ₁ • t) hA hρ₁ B).1 (ρ₁ᵁ B • a) ⟨i, ?_⟩
      swap
      · rwa [Tangle.smul_support, smul_derivBot, BaseSupport.smul_atoms, Enumeration.smul_rel,
          inv_smul_smul]
      obtain ⟨k, hk⟩ := this
      exact (T ⇘. _)ᴬ.rel_coinjective.coinjective hk ((h₂ k).mp ((h₁ k).mpr hk))
    · rintro N ⟨i, hN⟩
      have h₁ := hST.nearLitters_iff_of_inflexible A N₁ N₃ P t ρ₁
        hA ht hρ₁ hN₁₃ B N ⟨i, hN⟩
      have h₂ := hST.nearLitters_iff_of_inflexible A N₂ N₄ P t ρ₂
        hA (hN₁₂ ▸ ht) hρ₂ hN₂₄ B N ⟨i, hN⟩
      have ⟨j, _, hjT⟩ := hN₁₃
      have := (hT.support_le ⟨j, hjT⟩ P (ρ₁ • t) hA hρ₁ B).2 (ρ₁ᵁ B • N) ⟨i, ?_⟩
      swap
      · rwa [Tangle.smul_support, smul_derivBot, BaseSupport.smul_nearLitters, Enumeration.smul_rel,
          inv_smul_smul]
      obtain ⟨k, hk⟩ := this
      exact (T ⇘. _)ᴺ.rel_coinjective.coinjective hk ((h₂ k).mp ((h₁ k).mpr hk))
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

theorem conv_coherentAt (hST : S.spec = T.spec) (hS : S.Strong) (hT : T.Strong)
    {A : β ↝ ⊥} {N₁ N₂ : NearLitter} (hN : convNearLitters S T A N₁ N₂) :
    CoherentAt (conv hST hS hT) A N₁ᴸ N₂ᴸ := by
  rw [spec_eq_spec_iff] at hST
  constructor
  case inflexible =>
    intro P t hA ht
    obtain ⟨ρ, hρ⟩ := (hST.inflexible_iff hN P t hA).mp ⟨1, by rwa [one_smul]⟩
    refine ⟨ρ, ?_, hρ⟩
    rw [smul_support_eq_smul_iff]
    intro B
    constructor
    · rintro a ⟨i, hi⟩
      obtain ⟨j, hjS, hjT⟩ := hN
      have := (hT.support_le ⟨j, hjT⟩ P (ρ • t) hA hρ B).1 (ρᵁ B • a) ⟨i, ?_⟩
      swap
      · rwa [Tangle.smul_support, smul_derivBot, BaseSupport.smul_atoms,
          Enumeration.smul_rel, inv_smul_smul]
      obtain ⟨k, hk⟩ := this
      simp only [Tree.sderiv_apply, Tree.deriv_apply, Path.deriv_scoderiv]
      have := (hST.atoms_iff_of_inflexible A N₁ N₂ P t ρ hA ht hρ
          ⟨j, hjS, hjT⟩ B a ⟨i, hi⟩ k).mpr hk
      exact ⟨k, this, hk⟩
    · rintro N ⟨i, hi⟩
      obtain ⟨j, hjS, hjT⟩ := hN
      have := (hT.support_le ⟨j, hjT⟩ P (ρ • t) hA hρ B).2 (ρᵁ B • N) ⟨i, ?_⟩
      swap
      · rwa [Tangle.smul_support, smul_derivBot, BaseSupport.smul_nearLitters,
          Enumeration.smul_rel, inv_smul_smul]
      obtain ⟨k, hk⟩ := this
      simp only [Tree.sderiv_apply, Tree.deriv_apply, Path.deriv_scoderiv]
      have := (hST.nearLitters_iff_of_inflexible A N₁ N₂ P t ρ hA ht hρ
          ⟨j, hjS, hjT⟩ B N ⟨i, hi⟩ k).mpr hk
      exact ⟨k, this, hk⟩
  case flexible =>
    intro hN₁
    rwa [← hST.inflexible_iff' hN]

theorem conv_coherent (hST : S.spec = T.spec) (hS : S.Strong) (hT : T.Strong) :
    (conv hST hS hT).Coherent := by
  rintro A L₁ L₂ ⟨i, hiS, hiT⟩
  exact conv_coherentAt hST hS hT ⟨i, hiS, hiT⟩

theorem exists_conv (hST : S.spec = T.spec) (hS : S.Strong) (hT : T.Strong) :
    ∃ ρ : AllPerm β, ρᵁ • S = T := by
  obtain ⟨ρ, hρ⟩ := StrAction.freedomOfAction (conv hST hS hT) (conv_coherent hST hS hT)
  rw [spec_eq_spec_iff] at hST
  use ρ
  apply ext
  intro A
  apply BaseSupport.ext
  · apply Enumeration.ext
    · exact hST.atoms_bound_eq A
    ext i a
    constructor
    · intro ha
      obtain ⟨b, hb⟩ := hST.atoms_dom_of_dom ha
      cases (hρ A).1 ((ρᵁ A)⁻¹ • a) b ⟨i, ha, hb⟩
      rwa [smul_inv_smul] at hb
    · intro ha
      obtain ⟨b, hb⟩ := (sameSpec_comm hST).atoms_dom_of_dom ha
      cases (hρ A).1 b a ⟨i, hb, ha⟩
      rwa [smul_derivBot, BaseSupport.smul_atoms, Enumeration.smul_rel, inv_smul_smul]
  · apply Enumeration.ext
    · exact hST.nearLitters_bound_eq A
    ext i a
    constructor
    · intro ha
      obtain ⟨b, hb⟩ := hST.nearLitters_dom_of_dom ha
      cases (hρ A).2 ((ρᵁ A)⁻¹ • a) b ⟨i, ha, hb⟩
      rwa [smul_inv_smul] at hb
    · intro ha
      obtain ⟨b, hb⟩ := (sameSpec_comm hST).nearLitters_dom_of_dom ha
      cases (hρ A).2 b a ⟨i, hb, ha⟩
      rwa [smul_derivBot, BaseSupport.smul_nearLitters, Enumeration.smul_rel, inv_smul_smul]

end Support

end ConNF
