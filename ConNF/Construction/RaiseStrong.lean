import ConNF.Construction.Externalise

/-!
# New file

In this file...

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}] {β γ : Λ} {hγ : (γ : TypeIndex) < β}

namespace Support

theorem not_mem_strongbotDeriv (S : Support γ) (N : NearLitter) :
    N ∉ (S ↗ hγ ⇘. (Path.nil ↘.))ᴺ := by
  rintro ⟨i, ⟨A, N'⟩, h₁, h₂⟩
  simp only [Prod.mk.injEq] at h₂
  cases A
  case sderiv δ A hδ _ =>
    simp only [Path.deriv_sderiv] at h₂
    cases A
    case nil => cases h₂.1
    case sderiv ζ A hζ _ =>
      simp only [Path.deriv_sderiv] at h₂
      cases h₂.1

variable [Level] [LtLevel β]

theorem not_mem_strong_botDeriv (S : Support γ) (N : NearLitter) :
    N ∉ ((S ↗ hγ).strong ⇘. (Path.nil ↘.))ᴺ := by
  rintro h
  rw [strong, close_nearLitters, preStrong_nearLitters, Enumeration.mem_add_iff] at h
  obtain h | h := h
  · exact not_mem_strongbotDeriv S N h
  · rw [mem_constrainsNearLitters_nearLitters] at h
    obtain ⟨B, N', hN', h⟩ := h
    cases h using Relation.ReflTransGen.head_induction_on
    case refl => exact not_mem_strongbotDeriv S N hN'
    case head x hx₁ hx₂ _ =>
      obtain ⟨⟨γ, δ, ε, hδ, hε, hδε, A⟩, t, B, hB, hN, ht⟩ := hx₂
      simp only at hB
      cases B
      case nil =>
        cases hB
        obtain ⟨C, N''⟩ := x
        simp only at ht
        cases ht.1
        change _ ∈ t.supportᴺ at hN
        rw [t.support_supports.2 rfl] at hN
        obtain ⟨i, hN⟩ := hN
        cases hN
      case sderiv δ B hδ _ _ =>
        cases B
        case nil => cases hB
        case sderiv ζ B hζ _ _ => cases hB

theorem raise_preStrong (S : Support γ) (hγ : (γ : TypeIndex) < β) :
    ((S ↗ hγ).strong ↗ LtLevel.elim).PreStrong := by
  constructor
  rintro A N hN ⟨γ, δ, ε, hδ, hε, hδε, A⟩ t rfl ht
  dsimp only at hN ⊢
  obtain ⟨i, hi⟩ := hN
  rw [← derivBot_nearLitters, ← scoderiv_nearLitters,
    Enumeration.derivBot_rel, Enumeration.scoderiv_rel] at hi
  obtain ⟨B, hB₁, hB₂⟩ := hi
  change A ↘ _ ↘ _ = _ at hB₁
  cases B
  case sderiv ζ B hζ' _ =>
    rw [← Path.coderiv_deriv] at hB₁
    cases Path.sderiv_index_injective hB₁
    rw [Path.sderiv_left_inj] at hB₁
    cases B
    case nil =>
      cases A
      case nil =>
        cases hB₁
        cases not_mem_strong_botDeriv S N ⟨i, hB₂⟩
      case sderiv ζ A hζ _ _ => cases hB₁
    case sderiv ζ B hζ _ _ =>
      rw [← Path.coderiv_deriv] at hB₁
      cases Path.sderiv_index_injective hB₁
      rw [Path.sderiv_left_inj] at hB₁
      cases hB₁
      simp only [Path.botSderiv_coe_eq] at hB₂
      rw [Path.coderiv_deriv, scoderiv_deriv_eq]
      exact (S ↗ hγ).strong_strong.support_le ⟨i, hB₂⟩ ⟨γ, δ, ε, hδ, hε, hδε, B⟩ t rfl ht

theorem raise_strong (S : Support γ) (hγ : (γ : TypeIndex) < β) :
    ((S ↗ hγ).strong ↗ LtLevel.elim).Strong :=
  ⟨S.raise_preStrong hγ, (S ↗ hγ).strong_strong.scoderiv LtLevel.elim⟩

theorem raise_preStrong' (S : Support α) (hS : S.Strong) (T : Support γ) (ρ : AllPerm β)
    (hγ : (γ : TypeIndex) < β)
    (hρ : ρᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim) :
    (S + (ρᵁ • ((T ↗ hγ).strong +
      (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim).PreStrong := by
  sorry

theorem raise_closed' (S : Support α) (hS : S.Strong) (T : Support γ) (ρ : AllPerm β)
    (hγ : (γ : TypeIndex) < β)
    (hρ : ρᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim) :
    (S + (ρᵁ • ((T ↗ hγ).strong +
      (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim).Closed := by
  constructor
  intro A
  constructor
  intro N₁ N₂ hN₁ hN₂ a ha
  simp only [add_derivBot, BaseSupport.add_nearLitters, Enumeration.mem_add_iff,
    BaseSupport.add_atoms] at hN₁ hN₂ ⊢
  obtain hN₁ | hN₁ := hN₁
  · obtain hN₂ | hN₂ := hN₂
    · exact Or.inl ((hS.closed A).interference_subset hN₁ hN₂ a ha)
    · obtain ⟨B, rfl⟩ := eq_of_nearLitter_mem_scoderiv_botDeriv hN₂
      simp only [smul_add, scoderiv_botDeriv_eq, add_derivBot, smul_derivBot,
        BaseSupport.add_nearLitters, BaseSupport.smul_nearLitters, Enumeration.mem_add_iff,
        Enumeration.mem_smul, BaseSupport.add_atoms, BaseSupport.smul_atoms] at hN₁ hN₂ ⊢
      refine Or.inr (Or.inr ?_)
      rw [mem_interferenceSupport_atoms]
      refine ⟨(ρᵁ B)⁻¹ • N₁, ?_, (ρᵁ B)⁻¹ • N₂, ?_, ?_⟩
      · simp only [add_derivBot, BaseSupport.add_nearLitters, Enumeration.mem_add_iff]
        rw [← Enumeration.mem_smul, ← BaseSupport.smul_nearLitters, ← smul_derivBot, hρ]
        exact Or.inl hN₁
      · simp only [add_derivBot, BaseSupport.add_nearLitters, Enumeration.mem_add_iff]
        simp only [interferenceSupport_nearLitters, Enumeration.not_mem_empty, or_false] at hN₂
        exact Or.inr hN₂
      · rw [← BasePerm.smul_interference]
        exact Set.smul_mem_smul_set ha
  · obtain ⟨B, rfl⟩ := eq_of_nearLitter_mem_scoderiv_botDeriv hN₁
    simp only [smul_add, scoderiv_botDeriv_eq, add_derivBot, smul_derivBot,
      BaseSupport.add_nearLitters, BaseSupport.smul_nearLitters, Enumeration.mem_add_iff,
      Enumeration.mem_smul, BaseSupport.add_atoms, BaseSupport.smul_atoms] at hN₁ hN₂ ⊢
    refine Or.inr (Or.inr ?_)
    rw [mem_interferenceSupport_atoms]
    refine ⟨(ρᵁ B)⁻¹ • N₁, ?_, (ρᵁ B)⁻¹ • N₂, ?_, ?_⟩
    · simp only [add_derivBot, BaseSupport.add_nearLitters, Enumeration.mem_add_iff]
      simp only [interferenceSupport_nearLitters, Enumeration.not_mem_empty, or_false] at hN₁
      exact Or.inr hN₁
    · simp only [add_derivBot, BaseSupport.add_nearLitters, Enumeration.mem_add_iff]
      simp only [interferenceSupport_nearLitters, Enumeration.not_mem_empty, or_false] at hN₂
      obtain hN₂ | hN₂ := hN₂
      · rw [← Enumeration.mem_smul, ← BaseSupport.smul_nearLitters, ← smul_derivBot, hρ]
        exact Or.inl hN₂
      · exact Or.inr hN₂
    · rw [← BasePerm.smul_interference]
      exact Set.smul_mem_smul_set ha

theorem raise_strong' (S : Support α) (hS : S.Strong) (T : Support γ) (ρ : AllPerm β)
    (hγ : (γ : TypeIndex) < β)
    (hρ : ρᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim) :
    (S + (ρᵁ • ((T ↗ hγ).strong +
      (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim).Strong := by
  sorry

theorem convAtoms_injective_of_fixes {S : Support α} (hS : S.Strong) {T : Support γ}
    {ρ₁ ρ₂ : AllPerm β} {hγ : (γ : TypeIndex) < β}
    (hρ₁ : ρ₁ᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim)
    (hρ₂ : ρ₂ᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim)
    (A : ↑α ↝ ⊥) :
    (convAtoms
      (S + (ρ₁ᵁ • ((T ↗ hγ).strong + (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗
        LtLevel.elim)
      (S + (ρ₂ᵁ • ((T ↗ hγ).strong + (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗
        LtLevel.elim) A).Injective := by
  constructor
  rintro a₁ a₂ a₃ ⟨i, hi₁, hi₂⟩ ⟨j, hj₁, hj₂⟩
  sorry

theorem sameSpecLe_of_fixes (S : Support α) (hS : S.Strong) (T : Support γ) (ρ₁ ρ₂ : AllPerm β)
    (hγ : (γ : TypeIndex) < β)
    (hρ₁ : ρ₁ᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim)
    (hρ₂ : ρ₂ᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim) :
    SameSpecLE
    (S + (ρ₁ᵁ • ((T ↗ hγ).strong +
      (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim)
    (S + (ρ₂ᵁ • ((T ↗ hγ).strong +
      (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim) := by
  constructor
  case atoms_bound_eq => intro; rfl
  case nearLitters_bound_eq => intro; rfl
  case atoms_dom_subset =>
    simp only [add_derivBot, BaseSupport.add_atoms, Enumeration.add_rel_dom,
      Set.union_subset_iff, Set.subset_union_left, true_and]
    rintro A _ ⟨i, ⟨a, ⟨A, a⟩, h₁, h₂⟩, rfl⟩
    cases h₂
    right
    apply Set.mem_image_of_mem
    refine ⟨ρ₂ᵁ A • (ρ₁ᵁ A)⁻¹ • a, ⟨A, ρ₂ᵁ A • (ρ₁ᵁ A)⁻¹ • a⟩, ?_, rfl⟩
    rw [smul_atoms, Enumeration.smulPath_rel] at h₁ ⊢
    simp only [inv_smul_smul]
    exact h₁
  case nearLitters_dom_subset =>
    simp only [add_derivBot, BaseSupport.add_nearLitters, Enumeration.add_rel_dom,
      Set.union_subset_iff, Set.subset_union_left, true_and]
    rintro A _ ⟨i, ⟨N, ⟨A, N⟩, h₁, h₂⟩, rfl⟩
    cases h₂
    right
    apply Set.mem_image_of_mem
    refine ⟨ρ₂ᵁ A • (ρ₁ᵁ A)⁻¹ • N, ⟨A, ρ₂ᵁ A • (ρ₁ᵁ A)⁻¹ • N⟩, ?_, rfl⟩
    rw [smul_nearLitters, Enumeration.smulPath_rel] at h₁ ⊢
    simp only [inv_smul_smul]
    exact h₁
  case convAtoms_injective => exact convAtoms_injective_of_fixes hS hρ₁ hρ₂
  case atomMemRel_le => sorry
  case inflexible_of_inflexible => sorry
  case atoms_of_inflexible => sorry
  case nearLitters_of_inflexible => sorry
  case litter_eq_of_flexible => sorry

theorem spec_same_of_fixes (S : Support α) (hS : S.Strong) (T : Support γ) (ρ : AllPerm β)
    (hρ : ρᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim) :
    (S + ((T ↗ hγ).strong +
      (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport) ↗ LtLevel.elim).spec =
    (S + (ρᵁ • ((T ↗ hγ).strong +
      (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim).spec := by
  rw [Support.spec_eq_spec_iff]
  apply sameSpec_antisymm
  · have := sameSpecLe_of_fixes S hS T 1 ρ hγ ?_ hρ
    · simp only [allPermForget_one, one_smul, smul_add] at this
      exact this
    · simp only [allPermForget_one, one_smul]
  · have := sameSpecLe_of_fixes S hS T ρ 1 hγ hρ ?_
    · simp only [allPermForget_one, one_smul, smul_add] at this
      exact this
    · simp only [allPermForget_one, one_smul]

theorem exists_allowable_of_fixes (S : Support α) (hS : S.Strong) (T : Support γ) (ρ : AllPerm β)
    (hγ : (γ : TypeIndex) < β)
    (hρ : ρᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim) :
    ∃ ρ' : AllPerm α, ρ'ᵁ • S = S ∧ ρ'ᵁ ↘ LtLevel.elim ↘ hγ • T = ρᵁ ↘ hγ • T := by
  have := spec_same_of_fixes (hγ := hγ) S hS T ρ hρ
  have := exists_conv this ?_ ?_
  · obtain ⟨ρ', hρ'⟩ := this
    use ρ'
    simp only [Support.smul_add] at hρ'
    obtain ⟨hρ'₁, hρ'₂⟩ := add_inj_of_bound_eq_bound (by rfl) (by rfl) hρ'
    rw [Support.smul_scoderiv, scoderiv_inj, smul_add] at hρ'₂
    obtain ⟨hρ'₃, -⟩ := add_inj_of_bound_eq_bound (by rfl) (by rfl) hρ'₂
    have := smul_eq_smul_of_le (T ↗ hγ).subsupport_strong.le hρ'₃
    rw [Support.smul_scoderiv, smul_scoderiv, scoderiv_inj] at this
    exact ⟨hρ'₁, this⟩
  · have := raise_strong' S hS T 1 hγ (by simp only [allPermForget_one, one_smul])
    simp only [allPermForget_one, one_smul] at this
    exact this
  · exact raise_strong' S hS T ρ hγ hρ

end Support

end ConNF
