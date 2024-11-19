import ConNF.Counting.Spec

/-!
# Action on specifications

In this file, we prove that the specification of a support is invariant under the action
of allowable permutations.

## Main declarations

* `ConNF.Support.smul_spec`: The specification of a support is invariant under the action
of allowable permutations.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}] [Level] [CoherentData] {β : TypeIndex} [LeLevel β]
  (S : Support β) (ρ : AllPerm β)

namespace Support

theorem convAtoms_smul_iff_left (A : β ↝ ⊥) (a₁ a₂ : Atom) :
    convAtoms S (ρᵁ • S) A a₁ a₂ ↔ a₁ ∈ (S ⇘. A)ᴬ ∧ a₂ = ρᵁ A • a₁ := by
  constructor
  · rintro ⟨i, hi₁, hi₂⟩
    use ⟨i, hi₁⟩
    have := (S ⇘. A)ᴬ.rel_coinjective.coinjective hi₁ hi₂
    exact inv_smul_eq_iff.mp this.symm
  · rintro ⟨⟨i, hi⟩, rfl⟩
    refine ⟨i, hi, ?_⟩
    rwa [smul_derivBot, BaseSupport.smul_atoms, Enumeration.smul_rel, inv_smul_smul]

theorem convNearLitters_smul_iff_left (A : β ↝ ⊥) (N₁ N₂ : NearLitter) :
    convNearLitters S (ρᵁ • S) A N₁ N₂ ↔ N₁ ∈ (S ⇘. A)ᴺ ∧ N₂ = ρᵁ A • N₁ := by
  constructor
  · rintro ⟨i, hi₁, hi₂⟩
    use ⟨i, hi₁⟩
    have := (S ⇘. A)ᴺ.rel_coinjective.coinjective hi₁ hi₂
    exact inv_smul_eq_iff.mp this.symm
  · rintro ⟨⟨i, hi⟩, rfl⟩
    refine ⟨i, hi, ?_⟩
    rwa [smul_derivBot, BaseSupport.smul_nearLitters, Enumeration.smul_rel, inv_smul_smul]

theorem smul_convAtoms_injective (A : β ↝ ⊥) :
    (convAtoms S (ρᵁ • S) A).Injective := by
  constructor
  intro a₁ a₂ b h₁ h₂
  rw [convAtoms_smul_iff_left] at h₁ h₂
  have := h₁.2.symm.trans h₂.2
  rwa [smul_left_cancel_iff] at this

theorem atomMemRel_smul_le (A : β ↝ ⊥) :
    atomMemRel S A ≤ atomMemRel (ρᵁ • S) A := by
  rintro i j ⟨N, hNS, a, haN, haj⟩
  refine ⟨ρᵁ A • N, ?_, ρᵁ A • a, ?_, ?_⟩
  · rwa [smul_derivBot, BaseSupport.smul_nearLitters, Enumeration.smul_rel, inv_smul_smul]
  · simp only [BasePerm.smul_nearLitter_atoms, Set.smul_mem_smul_set_iff]
    exact haN
  · rwa [smul_derivBot, BaseSupport.smul_atoms, Rel.inv_apply, Enumeration.smul_rel,
      inv_smul_smul]

theorem inflexible_of_inflexible_smul {A : β ↝ ⊥} {N₁ N₂ : NearLitter}
    (h : convNearLitters S (ρᵁ • S) A N₁ N₂)
    (P : InflexiblePath β) (t : Tangle P.δ) (hA : A = P.A ↘ P.hε ↘.) (hN₁ : N₁ᴸ = fuzz P.hδε t) :
    ∃ ρ' : AllPerm P.δ, N₂ᴸ = fuzz P.hδε (ρ' • t) := by
  use ρ ⇘ P.A ↘ P.hδ
  rw [convNearLitters_smul_iff_left] at h
  rw [h.2, BasePerm.smul_nearLitter_litter, hN₁, hA, ← smul_fuzz P.hδ P.hε, allPermDeriv_forget]
  rfl

theorem litter_eq_of_flexible_smul {A : β ↝ ⊥} {N₁ N₂ N₃ N₄ : NearLitter}
    (h₁₂ : convNearLitters S (ρᵁ • S) A N₁ N₂) (h₃₄ : convNearLitters S (ρᵁ • S) A N₃ N₄)
    (h₁₃ : N₁ᴸ = N₃ᴸ) :
    N₂ᴸ = N₄ᴸ := by
  rw [convNearLitters_smul_iff_left] at h₁₂ h₃₄
  rw [h₁₂.2, h₃₄.2, BasePerm.smul_nearLitter_litter, BasePerm.smul_nearLitter_litter, h₁₃]

theorem convNearLitters_fuzz (A : β ↝ ⊥) (N₁ N₂ : NearLitter)
    (P : InflexiblePath β) (t : Tangle P.δ) (ρ' : AllPerm P.δ)
    (hA : A = P.A ↘ P.hε ↘.) (hN₁ : N₁ᴸ = fuzz P.hδε t) (hN₂ : N₂ᴸ = fuzz P.hδε (ρ' • t))
    (hN : convNearLitters S (ρᵁ • S) A N₁ N₂) :
    ρ' • t = ρ ⇘ P.A ↘ P.hδ • t := by
  rw [convNearLitters_smul_iff_left] at hN
  rw [hN.2, BasePerm.smul_nearLitter_litter, hN₁, hA,
    show ρᵁ (P.A ↘ P.hε ↘.) = (ρᵁ ⇘ P.A) ↘ P.hε ↘. from rfl,
    ← allPermDeriv_forget, smul_fuzz P.hδ] at hN₂
  exact (fuzz_injective hN₂).symm

theorem atoms_of_inflexible_smul (A : β ↝ ⊥) (N₁ N₂ : NearLitter)
    (P : InflexiblePath β) (t : Tangle P.δ) (ρ' : AllPerm P.δ)
    (hA : A = P.A ↘ P.hε ↘.) (hN₁ : N₁ᴸ = fuzz P.hδε t) (hN₂ : N₂ᴸ = fuzz P.hδε (ρ' • t))
    (hN : convNearLitters S (ρᵁ • S) A N₁ N₂) (B : P.δ ↝ ⊥)
    (a : Atom) (ha : a ∈ (t.support ⇘. B)ᴬ)
    (i : κ) (hiS : (S ⇘. (P.A ↘ P.hδ ⇘ B))ᴬ.rel i a) :
    ((ρᵁ • S) ⇘. (P.A ↘ P.hδ ⇘ B))ᴬ.rel i (ρ'ᵁ B • a) := by
  have := convNearLitters_fuzz S ρ A N₁ N₂ P t ρ' hA hN₁ hN₂ hN
  rw [Tangle.smul_atom_eq_of_mem_support this ha]
  rwa [smul_derivBot, BaseSupport.smul_atoms, allPermSderiv_forget, allPermDeriv_forget,
    Tree.sderiv_apply, Tree.deriv_apply, Path.deriv_scoderiv, Enumeration.smul_rel, inv_smul_smul]

theorem nearLitters_of_inflexible_smul (A : β ↝ ⊥) (N₁ N₂ : NearLitter)
    (P : InflexiblePath β) (t : Tangle P.δ) (ρ' : AllPerm P.δ)
    (hA : A = P.A ↘ P.hε ↘.) (hN₁ : N₁ᴸ = fuzz P.hδε t) (hN₂ : N₂ᴸ = fuzz P.hδε (ρ' • t))
    (hN : convNearLitters S (ρᵁ • S) A N₁ N₂) (B : P.δ ↝ ⊥)
    (N : NearLitter) (ha : N ∈ (t.support ⇘. B)ᴺ)
    (i : κ) (hiS : (S ⇘. (P.A ↘ P.hδ ⇘ B))ᴺ.rel i N) :
    ((ρᵁ • S) ⇘. (P.A ↘ P.hδ ⇘ B))ᴺ.rel i (ρ'ᵁ B • N) := by
  have := convNearLitters_fuzz S ρ A N₁ N₂ P t ρ' hA hN₁ hN₂ hN
  rw [Tangle.smul_nearLitter_eq_of_mem_support this ha]
  rwa [smul_derivBot, BaseSupport.smul_nearLitters, allPermSderiv_forget, allPermDeriv_forget,
    Tree.sderiv_apply, Tree.deriv_apply, Path.deriv_scoderiv, Enumeration.smul_rel, inv_smul_smul]

@[simp]
theorem sameSpecLe_smul :
    SameSpecLE S (ρᵁ • S) := by
  constructor
  case atoms_bound_eq => intro; rfl
  case nearLitters_bound_eq => intro; rfl
  case atoms_dom_subset =>
    intro
    rw [smul_derivBot, BaseSupport.smul_atoms, Enumeration.smul_rel_dom]
  case nearLitters_dom_subset =>
    intro
    rw [smul_derivBot, BaseSupport.smul_nearLitters, Enumeration.smul_rel_dom]
  case convAtoms_injective => exact S.smul_convAtoms_injective ρ
  case atomMemRel_le => exact S.atomMemRel_smul_le ρ
  case inflexible_of_inflexible => exact S.inflexible_of_inflexible_smul ρ
  case litter_eq_of_flexible =>
    intros
    apply S.litter_eq_of_flexible_smul ρ <;> assumption
  case atoms_of_inflexible => exact S.atoms_of_inflexible_smul ρ
  case nearLitters_of_inflexible => exact S.nearLitters_of_inflexible_smul ρ

@[simp]
theorem smul_spec :
    (ρᵁ • S).spec = S.spec := by
  rw [spec_eq_spec_iff]
  apply sameSpec_antisymm
  · have := (ρᵁ • S).sameSpecLe_smul ρ⁻¹
    rwa [allPermForget_inv, inv_smul_smul] at this
  · exact S.sameSpecLe_smul ρ

end Support

end ConNF
