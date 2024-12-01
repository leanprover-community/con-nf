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

theorem not_mem_scoderiv_botDeriv (S : Support γ) (N : NearLitter) :
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
  · exact not_mem_scoderiv_botDeriv S N h
  · rw [mem_constrainsNearLitters_nearLitters] at h
    obtain ⟨B, N', hN', h⟩ := h
    cases h using Relation.ReflTransGen.head_induction_on
    case refl => exact not_mem_scoderiv_botDeriv S N hN'
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

theorem raise_preStrong' (S : Support α) (hS : S.Strong) (T : Support γ) (ρ : AllPerm β)
    (hγ : (γ : TypeIndex) < β) :
    (S + (ρᵁ • ((T ↗ hγ).strong +
      (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim).PreStrong := by
  apply hS.toPreStrong.add
  constructor
  intro A N hN P t hA ht
  obtain ⟨A, rfl⟩ := eq_of_nearLitter_mem_scoderiv_botDeriv hN
  simp only [scoderiv_botDeriv_eq, add_derivBot, smul_derivBot,
    BaseSupport.add_nearLitters, BaseSupport.smul_nearLitters, interferenceSupport_nearLitters,
    Enumeration.mem_add_iff, Enumeration.mem_smul, Enumeration.not_mem_empty, or_false] at hN
  obtain ⟨δ, ε, ζ, hε, hζ, hεζ, B⟩ := P
  dsimp only at *
  cases A
  case sderiv ζ' A hζ' _ =>
    rw [← Path.coderiv_deriv] at hA
    cases Path.sderiv_index_injective hA
    apply Path.sderiv_left_inj.mp at hA
    cases A
    case nil =>
      cases hA
      cases not_mem_strong_botDeriv T _ hN
    case sderiv ι A hι _ _ =>
      rw [← Path.coderiv_deriv] at hA
      cases Path.sderiv_index_injective hA
      cases hA
      haveI : LtLevel δ := ⟨A.le.trans_lt LtLevel.elim⟩
      haveI : LtLevel ε := ⟨hε.trans LtLevel.elim⟩
      haveI : LtLevel ζ := ⟨hζ.trans LtLevel.elim⟩
      have := (T ↗ hγ).strong_strong.support_le hN ⟨δ, ε, ζ, hε, hζ, hεζ, A⟩
          (ρ⁻¹ ⇘ A ↘ hε • t) rfl ?_
      · simp only [Tangle.smul_support, allPermSderiv_forget, allPermDeriv_forget,
          allPermForget_inv, Tree.inv_deriv, Tree.inv_sderiv] at this
        have := smul_le_smul this (ρᵁ ⇘ A ↘ hε)
        simp only [smul_inv_smul] at this
        apply le_trans this
        intro B
        constructor
        · intro a ha
          simp only [smul_derivBot, Tree.sderiv_apply, Tree.deriv_apply, Path.deriv_scoderiv,
            deriv_derivBot, Enumeration.mem_smul] at ha
          rw [deriv_derivBot, ← Path.deriv_scoderiv, Path.coderiv_deriv', scoderiv_botDeriv_eq,]
          simp only [Path.deriv_scoderiv, add_derivBot, smul_derivBot,
            BaseSupport.add_atoms, BaseSupport.smul_atoms, Enumeration.mem_add_iff,
            Enumeration.mem_smul]
          exact Or.inl ha
        · intro N hN
          simp only [smul_derivBot, Tree.sderiv_apply, Tree.deriv_apply, Path.deriv_scoderiv,
            deriv_derivBot, Enumeration.mem_smul] at hN
          rw [deriv_derivBot, ← Path.deriv_scoderiv, Path.coderiv_deriv', scoderiv_botDeriv_eq,]
          simp only [Path.deriv_scoderiv, add_derivBot, smul_derivBot,
            BaseSupport.add_nearLitters, BaseSupport.smul_nearLitters, Enumeration.mem_add_iff,
            Enumeration.mem_smul]
          exact Or.inl hN
      · rw [← smul_fuzz hε hζ hεζ, ← ht]
        simp only [Path.botSderiv_coe_eq, BasePerm.smul_nearLitter_litter, allPermDeriv_forget,
          allPermForget_inv, Tree.inv_deriv, Tree.inv_sderiv, Tree.inv_sderivBot]
        rfl

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
      (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim).Strong :=
  ⟨raise_preStrong' S hS T ρ hγ, raise_closed' S hS T ρ hγ hρ⟩

theorem convAtoms_injective_of_fixes {S : Support α} {T : Support γ}
    {ρ₁ ρ₂ : AllPerm β} {hγ : (γ : TypeIndex) < β}
    (hρ₁ : ρ₁ᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim)
    (hρ₂ : ρ₂ᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim)
    (A : ↑α ↝ ⊥) :
    (convAtoms
      (S + (ρ₁ᵁ • ((T ↗ hγ).strong + (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗
        LtLevel.elim)
      (S + (ρ₂ᵁ • ((T ↗ hγ).strong + (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗
        LtLevel.elim) A).Injective := by
  rw [Support.smul_eq_iff] at hρ₁ hρ₂
  constructor
  rintro a₁ a₂ a₃ ⟨i, hi₁, hi₂⟩ ⟨j, hj₁, hj₂⟩
  simp only [add_derivBot, BaseSupport.add_atoms, Rel.inv_apply,
    Enumeration.rel_add_iff] at hi₁ hi₂ hj₁ hj₂
  obtain hi₁ | ⟨i, rfl, hi₁⟩ := hi₁
  · obtain hi₂ | ⟨i', rfl, _⟩ := hi₂
    swap
    · have := Enumeration.lt_bound _ _ ⟨_, hi₁⟩
      simp only [add_lt_iff_neg_left] at this
      cases (κ_zero_le i').not_lt this
    cases (Enumeration.rel_coinjective _).coinjective hi₁ hi₂
    obtain hj₁ | ⟨j, rfl, hj₁⟩ := hj₁
    · obtain hj₂ | ⟨j', rfl, _⟩ := hj₂
      · exact (Enumeration.rel_coinjective _).coinjective hj₂ hj₁
      · have := Enumeration.lt_bound _ _ ⟨_, hj₁⟩
        simp only [add_lt_iff_neg_left] at this
        cases (κ_zero_le j').not_lt this
    · obtain hj₂ | hj₂ := hj₂
      · have := Enumeration.lt_bound _ _ ⟨_, hj₂⟩
        simp only [add_lt_iff_neg_left] at this
        cases (κ_zero_le j).not_lt this
      · simp only [add_right_inj, exists_eq_left] at hj₂
        obtain ⟨B, rfl⟩ := eq_of_atom_mem_scoderiv_botDeriv ⟨j, hj₁⟩
        simp only [scoderiv_botDeriv_eq, smul_derivBot, add_derivBot, BaseSupport.smul_atoms,
          BaseSupport.add_atoms, Enumeration.smul_rel, add_right_inj, exists_eq_left] at hj₁ hj₂
        have := (Enumeration.rel_coinjective _).coinjective hj₁ hj₂
        rw [← (hρ₂ B).1 a₁ ⟨_, hi₁⟩, inv_smul_smul, inv_smul_eq_iff, (hρ₁ B).1 a₁ ⟨_, hi₁⟩] at this
        exact this.symm
  · obtain ⟨B, rfl⟩ := eq_of_atom_mem_scoderiv_botDeriv ⟨i, hi₁⟩
    simp only [scoderiv_botDeriv_eq, smul_derivBot, add_derivBot, BaseSupport.smul_atoms,
      BaseSupport.add_atoms, Enumeration.smul_rel, add_right_inj, exists_eq_left] at hi₁ hi₂ hj₁ hj₂
    obtain hi₂ | hi₂ := hi₂
    · have := Enumeration.lt_bound _ _ ⟨_, hi₂⟩
      simp only [add_lt_iff_neg_left] at this
      cases (κ_zero_le i).not_lt this
    have hi := (Enumeration.rel_coinjective _).coinjective hi₁ hi₂
    suffices hj : (ρ₁ᵁ B)⁻¹ • a₂ = (ρ₂ᵁ B)⁻¹ • a₃ by
      rwa [← hj, smul_left_cancel_iff] at hi
    obtain hj₁ | ⟨j, rfl, hj₁⟩ := hj₁
    · obtain hj₂ | ⟨j', rfl, _⟩ := hj₂
      · rw [← (hρ₁ B).1 a₂ ⟨_, hj₁⟩, ← (hρ₂ B).1 a₃ ⟨_, hj₂⟩, inv_smul_smul, inv_smul_smul]
        exact (Enumeration.rel_coinjective _).coinjective hj₁ hj₂
      · have := Enumeration.lt_bound _ _ ⟨_, hj₁⟩
        simp only [add_lt_iff_neg_left] at this
        cases (κ_zero_le j').not_lt this
    · obtain hj₂ | hj₂ := hj₂
      · have := Enumeration.lt_bound _ _ ⟨_, hj₂⟩
        simp only [add_lt_iff_neg_left] at this
        cases (κ_zero_le j).not_lt this
      · simp only [add_right_inj, exists_eq_left] at hj₂
        exact (Enumeration.rel_coinjective _).coinjective hj₁ hj₂

theorem atomMemRel_le_of_fixes {S : Support α} {T : Support γ}
    {ρ₁ ρ₂ : AllPerm β} {hγ : (γ : TypeIndex) < β}
    (hρ₁ : ρ₁ᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim)
    (hρ₂ : ρ₂ᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim)
    (A : ↑α ↝ ⊥) :
    atomMemRel (S + (ρ₁ᵁ • ((T ↗ hγ).strong +
      (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim) A ≤
    atomMemRel (S + (ρ₂ᵁ • ((T ↗ hγ).strong +
      (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim) A := by
  rw [Support.smul_eq_iff] at hρ₁ hρ₂
  rintro i j ⟨N, hN, a, haN, ha⟩
  simp only [add_derivBot, BaseSupport.add_atoms, Rel.inv_apply, Enumeration.rel_add_iff,
    BaseSupport.add_nearLitters] at ha hN
  obtain hN | ⟨i, rfl, hi⟩ := hN
  · obtain ha | ⟨j, rfl, hj⟩ := ha
    · exact ⟨N, Or.inl hN, a, haN, Or.inl ha⟩
    · obtain ⟨B, rfl⟩ := eq_of_atom_mem_scoderiv_botDeriv ⟨j, hj⟩
      simp only [scoderiv_botDeriv_eq, smul_derivBot, add_derivBot, BaseSupport.smul_atoms,
        BaseSupport.add_atoms, Enumeration.smul_rel] at hj hN
      refine ⟨N, Or.inl hN, ρ₂ᵁ B • (ρ₁ᵁ B)⁻¹ • a, ?_, ?_⟩
      · dsimp only
        rw [← (hρ₂ B).2 N ⟨_, hN⟩, BasePerm.smul_nearLitter_atoms, Set.smul_mem_smul_set_iff]
        have := (hρ₁ B).2 N ⟨_, hN⟩
        rw [smul_eq_iff_eq_inv_smul] at this
        rwa [this, BasePerm.smul_nearLitter_atoms, Set.smul_mem_smul_set_iff]
      · rw [Rel.inv_apply, add_derivBot, BaseSupport.add_atoms, Enumeration.rel_add_iff]
        simp only [add_right_inj, scoderiv_botDeriv_eq, smul_derivBot, add_derivBot,
          BaseSupport.smul_atoms, BaseSupport.add_atoms, Enumeration.smul_rel, inv_smul_smul,
          exists_eq_left]
        exact Or.inr hj
  · obtain ⟨B, rfl⟩ := eq_of_nearLitter_mem_scoderiv_botDeriv ⟨i, hi⟩
    simp only [scoderiv_botDeriv_eq, smul_derivBot, add_derivBot, BaseSupport.smul_atoms,
      BaseSupport.add_atoms, Enumeration.smul_rel] at hi ha
    obtain ha | ⟨j, rfl, hj⟩ := ha
    · refine ⟨ρ₂ᵁ B • (ρ₁ᵁ B)⁻¹ • N, ?_, a, ?_, Or.inl ha⟩
      · rw [add_derivBot, BaseSupport.add_nearLitters, Enumeration.rel_add_iff]
        simp only [add_right_inj, scoderiv_botDeriv_eq, smul_derivBot, add_derivBot,
          BaseSupport.smul_nearLitters, BaseSupport.add_nearLitters, Enumeration.smul_rel,
          inv_smul_smul, exists_eq_left]
        exact Or.inr hi
      · dsimp only
        rw [← (hρ₂ B).1 a ⟨_, ha⟩, BasePerm.smul_nearLitter_atoms, Set.smul_mem_smul_set_iff]
        have := (hρ₁ B).1 a ⟨_, ha⟩
        rw [smul_eq_iff_eq_inv_smul] at this
        rwa [this, BasePerm.smul_nearLitter_atoms, Set.smul_mem_smul_set_iff]
    · refine ⟨ρ₂ᵁ B • (ρ₁ᵁ B)⁻¹ • N, ?_, ρ₂ᵁ B • (ρ₁ᵁ B)⁻¹ • a, ?_, ?_⟩
      · rw [add_derivBot, BaseSupport.add_nearLitters, Enumeration.rel_add_iff]
        simp only [add_right_inj, scoderiv_botDeriv_eq, smul_derivBot, add_derivBot,
          BaseSupport.smul_nearLitters, BaseSupport.add_nearLitters, Enumeration.smul_rel,
          inv_smul_smul, exists_eq_left]
        exact Or.inr hi
      · simp only [BasePerm.smul_nearLitter_atoms, Set.smul_mem_smul_set_iff]
        exact haN
      · rw [Rel.inv_apply, add_derivBot, BaseSupport.add_atoms, Enumeration.rel_add_iff]
        simp only [add_right_inj, scoderiv_botDeriv_eq, smul_derivBot, add_derivBot,
          BaseSupport.smul_atoms, BaseSupport.add_atoms, Enumeration.smul_rel, inv_smul_smul,
          exists_eq_left]
        exact Or.inr hj

theorem convNearLitters_cases {S : Support α} {T : Support γ}
    {ρ₁ ρ₂ : AllPerm β} {hγ : (γ : TypeIndex) < β}
    {A : α ↝ ⊥} {N₁ N₂ : NearLitter} :
  convNearLitters
    (S + (ρ₁ᵁ • ((T ↗ hγ).strong +
      (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim)
    (S + (ρ₂ᵁ • ((T ↗ hγ).strong +
      (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim) A N₁ N₂ →
    N₁ = N₂ ∧ N₁ ∈ (S ⇘. A)ᴺ ∨
    ∃ B : β ↝ ⊥, A = B ↗ LtLevel.elim ∧ (ρ₁ᵁ B)⁻¹ • N₁ = (ρ₂ᵁ B)⁻¹ • N₂ ∧
      (ρ₁ᵁ B)⁻¹ • N₁ ∈ (((T ↗ hγ).strong +
        (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport) ⇘. B)ᴺ := by
  rintro ⟨i, hN₁, hN₂⟩
  simp only [add_derivBot, BaseSupport.add_nearLitters, Rel.inv_apply,
    Enumeration.rel_add_iff] at hN₁ hN₂
  obtain hN₁ | ⟨i, rfl, hN₁⟩ := hN₁
  · obtain hN₂ | ⟨i, rfl, hN₂⟩ := hN₂
    swap
    · have := Enumeration.lt_bound _ _ ⟨_, hN₁⟩
      simp only [add_lt_iff_neg_left] at this
      cases (κ_zero_le i).not_lt this
    exact Or.inl ⟨(Enumeration.rel_coinjective _).coinjective hN₁ hN₂, _, hN₁⟩
  · obtain ⟨B, rfl⟩ := eq_of_nearLitter_mem_scoderiv_botDeriv ⟨i, hN₁⟩
    simp only [scoderiv_botDeriv_eq, smul_derivBot, add_derivBot, BaseSupport.smul_nearLitters,
      BaseSupport.add_nearLitters, Enumeration.smul_rel, add_right_inj, exists_eq_left] at hN₁ hN₂
    obtain hN₂ | hN₂ := hN₂
    · have := Enumeration.lt_bound _ _ ⟨_, hN₂⟩
      simp only [add_lt_iff_neg_left] at this
      cases (κ_zero_le i).not_lt this
    exact Or.inr ⟨B, rfl, (Enumeration.rel_coinjective _).coinjective hN₁ hN₂, _, hN₁⟩

theorem inflexible_of_inflexible_of_fixes {S : Support α} {T : Support γ}
    {ρ₁ ρ₂ : AllPerm β} {hγ : (γ : TypeIndex) < β}
    (hρ₁ : ρ₁ᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim)
    (hρ₂ : ρ₂ᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim)
    {A : α ↝ ⊥} {N₁ N₂ : NearLitter} :
    convNearLitters
      (S + (ρ₁ᵁ • ((T ↗ hγ).strong +
        (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim)
      (S + (ρ₂ᵁ • ((T ↗ hγ).strong +
        (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim) A N₁ N₂ →
      ∀ (P : InflexiblePath ↑α) (t : Tangle P.δ), A = P.A ↘ P.hε ↘. → N₁ᴸ = fuzz P.hδε t →
      ∃ ρ : AllPerm P.δ, N₂ᴸ = fuzz P.hδε (ρ • t) := by
  rintro hN ⟨γ, δ, ε, hδ, hε, hδε, A⟩ t hA ht
  haveI : LeLevel γ := ⟨A.le⟩
  haveI : LtLevel δ := ⟨hδ.trans_le LeLevel.elim⟩
  haveI : LtLevel ε := ⟨hε.trans_le LeLevel.elim⟩
  obtain ⟨rfl, _⟩ | ⟨B, rfl, hN'⟩ := convNearLitters_cases hN
  · use 1
    rw [one_smul, ht]
  · clear hN
    cases B
    case sderiv ε B hε' _ =>
      rw [← Path.coderiv_deriv] at hA
      cases Path.sderiv_index_injective hA
      apply Path.sderiv_path_injective at hA
      cases B
      case nil =>
        simp only [Path.botSderiv_coe_eq, add_derivBot, BaseSupport.add_nearLitters,
          interferenceSupport_nearLitters, Enumeration.add_empty] at hN'
        cases not_mem_strong_botDeriv _ _ hN'.2
      case sderiv ζ B hζ _ _ =>
        rw [← Path.coderiv_deriv] at hA
        cases Path.sderiv_index_injective hA
        apply Path.sderiv_path_injective at hA
        dsimp only at hA hζ hε' B t
        cases hA
        use (ρ₂ * ρ₁⁻¹) ⇘ B ↘ hδ
        rw [inv_smul_eq_iff] at hN'
        rw [← smul_fuzz hδ hε hδε, ← ht, hN'.1]
        simp only [allPermDeriv_forget, allPermForget_mul, allPermForget_inv, Tree.mul_deriv,
          Tree.inv_deriv, Tree.mul_sderiv, Tree.inv_sderiv, Tree.mul_sderivBot, Tree.inv_sderivBot,
          Path.botSderiv_coe_eq, BasePerm.smul_nearLitter_litter, mul_smul]
        erw [inv_smul_smul, smul_inv_smul]

theorem atoms_of_inflexible_of_fixes {S : Support α} (hS : S.Strong) {T : Support γ}
    {ρ₁ ρ₂ : AllPerm β} {hγ : (γ : TypeIndex) < β}
    (hρ₁ : ρ₁ᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim)
    (hρ₂ : ρ₂ᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim)
    (A : α ↝ ⊥) (N₁ N₂ : NearLitter) (P : InflexiblePath ↑α) (t : Tangle P.δ) (ρ : AllPerm P.δ) :
    A = P.A ↘ P.hε ↘. → N₁ᴸ = fuzz P.hδε t → N₂ᴸ = fuzz P.hδε (ρ • t) →
    convNearLitters
      (S + (ρ₁ᵁ • ((T ↗ hγ).strong +
        (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim)
      (S + (ρ₂ᵁ • ((T ↗ hγ).strong +
        (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim) A N₁ N₂ →
    ∀ (B : P.δ ↝ ⊥), ∀ a ∈ (t.support ⇘. B)ᴬ, ∀ (i : κ),
      ((S + (ρ₁ᵁ • ((T ↗ hγ).strong + (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗
        LtLevel.elim) ⇘. (P.A ↘ P.hδ ⇘ B))ᴬ.rel i a →
      ((S + (ρ₂ᵁ • ((T ↗ hγ).strong + (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗
        LtLevel.elim) ⇘. (P.A ↘ P.hδ ⇘ B))ᴬ.rel i (ρᵁ B • a) := by
  rw [Support.smul_eq_iff] at hρ₁ hρ₂
  obtain ⟨γ, δ, ε, hδ, hε, hδε, B⟩ := P
  haveI : LeLevel γ := ⟨B.le⟩
  haveI : LtLevel δ := ⟨hδ.trans_le LeLevel.elim⟩
  haveI : LtLevel ε := ⟨hε.trans_le LeLevel.elim⟩
  dsimp only at t ρ ⊢
  intro hA hN₁ hN₂ hN C a ha i hi
  obtain ⟨rfl, hN'⟩ | ⟨A, rfl, hN₁', hN₂'⟩ := convNearLitters_cases hN
  · have haS := (hS.support_le hN' ⟨γ, δ, ε, hδ, hε, hδε, _⟩ t hA hN₁ _).1 a ha
    rw [hN₂] at hN₁
    have hρt := congr_arg Tangle.support (fuzz_injective hN₁)
    rw [Tangle.smul_support, Support.smul_eq_iff] at hρt
    simp only [add_derivBot, BaseSupport.add_atoms, Enumeration.rel_add_iff] at hi ⊢
    rw [(hρt C).1 a ha]
    obtain hi | ⟨i, rfl, hi⟩ := hi
    · exact Or.inl hi
    · simp only [add_right_inj, exists_eq_left]
      obtain ⟨D, hD⟩ := eq_of_atom_mem_scoderiv_botDeriv ⟨i, hi⟩
      cases B using Path.recScoderiv
      case nil =>
        cases Path.scoderiv_index_injective hD
        cases Path.scoderiv_left_inj.mp hD
        simp only [hD, Path.coderiv_deriv, Path.coderiv_deriv', scoderiv_botDeriv_eq, smul_derivBot,
          add_derivBot, BaseSupport.smul_atoms, BaseSupport.add_atoms, Enumeration.smul_rel] at hi ⊢
        rw [deriv_derivBot, hD] at haS
        rw [← (hρ₂ _).1 a haS, inv_smul_smul]
        rw [← (hρ₁ _).1 a haS, inv_smul_smul] at hi
        exact Or.inr hi
      case scoderiv ζ B hζ' _ =>
        rw [Path.coderiv_deriv, Path.coderiv_deriv'] at hD
        cases Path.scoderiv_index_injective hD
        rw [Path.scoderiv_left_inj] at hD
        cases hD
        simp only [Path.coderiv_deriv, Path.coderiv_deriv', scoderiv_botDeriv_eq, smul_derivBot,
          add_derivBot, BaseSupport.smul_atoms, BaseSupport.add_atoms, Enumeration.smul_rel] at hi ⊢
        rw [deriv_derivBot, Path.coderiv_deriv, Path.coderiv_deriv'] at haS
        rw [← (hρ₂ _).1 a haS, inv_smul_smul]
        rw [← (hρ₁ _).1 a haS, inv_smul_smul] at hi
        exact Or.inr hi
  · simp only [add_derivBot, BaseSupport.add_nearLitters, interferenceSupport_nearLitters,
      Enumeration.add_empty] at hN₂'
    cases A
    case sderiv ζ A hζ' _ =>
      rw [← Path.coderiv_deriv] at hA
      cases Path.sderiv_index_injective hA
      apply Path.sderiv_path_injective at hA
      cases A
      case nil =>
        cases hA
        cases not_mem_strong_botDeriv _ _ hN₂'
      case sderiv ζ A hζ _ _ =>
        rw [← Path.coderiv_deriv] at hA
        cases Path.sderiv_index_injective hA
        apply Path.sderiv_path_injective at hA
        cases hA
        simp only [Path.coderiv_deriv, Path.coderiv_deriv', add_derivBot, scoderiv_botDeriv_eq,
          smul_derivBot, BaseSupport.add_atoms, BaseSupport.smul_atoms] at hi ⊢
        have : N₂ᴸ = (ρ₂ ⇘ A)ᵁ ↘ hζ ↘. • (ρ₁⁻¹ ⇘ A)ᵁ ↘ hζ ↘. • fuzz hδε t := by
          rw [inv_smul_eq_iff] at hN₁'
          rw [hN₁', Path.botSderiv_coe_eq, BasePerm.smul_nearLitter_litter,
            BasePerm.smul_nearLitter_litter, smul_smul, smul_eq_iff_eq_inv_smul,
            mul_inv_rev, inv_inv, mul_smul, ← Tree.inv_apply, ← allPermForget_inv] at hN₁
          rw [hN₁]
          simp only [allPermForget_inv, Tree.inv_apply, allPermDeriv_forget, Tree.inv_deriv,
            Tree.inv_sderiv, Tree.inv_sderivBot]
          rfl
        rw [smul_fuzz hδ hε hδε, smul_fuzz hδ hε hδε] at this
        have := fuzz_injective (hN₂.symm.trans this)
        rw [smul_smul] at this
        rw [t.smul_atom_eq_of_mem_support this ha]
        rw [Enumeration.rel_add_iff] at hi ⊢
        obtain hi | ⟨i, rfl, hi⟩ := hi
        · left
          simp only [allPermForget_mul, allPermSderiv_forget, allPermDeriv_forget,
            allPermForget_inv, Tree.inv_deriv, Tree.inv_sderiv, Tree.mul_apply, Tree.sderiv_apply,
            Tree.deriv_apply, Path.deriv_scoderiv, Tree.inv_apply, mul_smul]
          rwa [← (hρ₁ _).1 a ⟨i, hi⟩, inv_smul_smul, (hρ₂ _).1 a ⟨i, hi⟩]
        · refine Or.inr ⟨i, rfl, ?_⟩
          simp only [allPermForget_mul, allPermSderiv_forget, allPermDeriv_forget,
            allPermForget_inv, Tree.inv_deriv, Tree.inv_sderiv, Tree.mul_apply, Tree.sderiv_apply,
            Tree.deriv_apply, Path.deriv_scoderiv, Tree.inv_apply, mul_smul, Enumeration.smul_rel,
            inv_smul_smul]
          exact hi

theorem nearLitters_of_inflexible_of_fixes {S : Support α} (hS : S.Strong) {T : Support γ}
    {ρ₁ ρ₂ : AllPerm β} {hγ : (γ : TypeIndex) < β}
    (hρ₁ : ρ₁ᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim)
    (hρ₂ : ρ₂ᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim)
    (A : α ↝ ⊥) (N₁ N₂ : NearLitter) (P : InflexiblePath ↑α) (t : Tangle P.δ) (ρ : AllPerm P.δ) :
    A = P.A ↘ P.hε ↘. → N₁ᴸ = fuzz P.hδε t → N₂ᴸ = fuzz P.hδε (ρ • t) →
    convNearLitters
      (S + (ρ₁ᵁ • ((T ↗ hγ).strong +
        (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim)
      (S + (ρ₂ᵁ • ((T ↗ hγ).strong +
        (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim) A N₁ N₂ →
    ∀ (B : P.δ ↝ ⊥), ∀ N ∈ (t.support ⇘. B)ᴺ, ∀ (i : κ),
      ((S + (ρ₁ᵁ • ((T ↗ hγ).strong + (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗
        LtLevel.elim) ⇘. (P.A ↘ P.hδ ⇘ B))ᴺ.rel i N →
      ((S + (ρ₂ᵁ • ((T ↗ hγ).strong + (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗
        LtLevel.elim) ⇘. (P.A ↘ P.hδ ⇘ B))ᴺ.rel i (ρᵁ B • N) := by
  rw [Support.smul_eq_iff] at hρ₁ hρ₂
  obtain ⟨γ, δ, ε, hδ, hε, hδε, B⟩ := P
  haveI : LeLevel γ := ⟨B.le⟩
  haveI : LtLevel δ := ⟨hδ.trans_le LeLevel.elim⟩
  haveI : LtLevel ε := ⟨hε.trans_le LeLevel.elim⟩
  dsimp only at t ρ ⊢
  intro hA hN₁ hN₂ hN C N₀ hN₀ i hi
  obtain ⟨rfl, hN'⟩ | ⟨A, rfl, hN₁', hN₂'⟩ := convNearLitters_cases hN
  · have haS := (hS.support_le hN' ⟨γ, δ, ε, hδ, hε, hδε, _⟩ t hA hN₁ _).2 N₀ hN₀
    rw [hN₂] at hN₁
    have hρt := congr_arg Tangle.support (fuzz_injective hN₁)
    rw [Tangle.smul_support, Support.smul_eq_iff] at hρt
    simp only [add_derivBot, BaseSupport.add_nearLitters, Enumeration.rel_add_iff] at hi ⊢
    rw [(hρt C).2 N₀ hN₀]
    obtain hi | ⟨i, rfl, hi⟩ := hi
    · exact Or.inl hi
    · simp only [add_right_inj, exists_eq_left]
      obtain ⟨D, hD⟩ := eq_of_nearLitter_mem_scoderiv_botDeriv ⟨i, hi⟩
      cases B using Path.recScoderiv
      case nil =>
        cases Path.scoderiv_index_injective hD
        cases Path.scoderiv_left_inj.mp hD
        simp only [hD, Path.coderiv_deriv, Path.coderiv_deriv', scoderiv_botDeriv_eq, smul_derivBot,
          add_derivBot, BaseSupport.smul_nearLitters, BaseSupport.add_nearLitters, Enumeration.smul_rel] at hi ⊢
        rw [deriv_derivBot, hD] at haS
        rw [← (hρ₂ _).2 N₀ haS, inv_smul_smul]
        rw [← (hρ₁ _).2 N₀ haS, inv_smul_smul] at hi
        exact Or.inr hi
      case scoderiv ζ B hζ' _ =>
        rw [Path.coderiv_deriv, Path.coderiv_deriv'] at hD
        cases Path.scoderiv_index_injective hD
        rw [Path.scoderiv_left_inj] at hD
        cases hD
        simp only [Path.coderiv_deriv, Path.coderiv_deriv', scoderiv_botDeriv_eq, smul_derivBot,
          add_derivBot, BaseSupport.smul_nearLitters, BaseSupport.add_nearLitters, Enumeration.smul_rel] at hi ⊢
        rw [deriv_derivBot, Path.coderiv_deriv, Path.coderiv_deriv'] at haS
        rw [← (hρ₂ _).2 N₀ haS, inv_smul_smul]
        rw [← (hρ₁ _).2 N₀ haS, inv_smul_smul] at hi
        exact Or.inr hi
  · simp only [add_derivBot, BaseSupport.add_nearLitters, interferenceSupport_nearLitters,
      Enumeration.add_empty] at hN₂'
    cases A
    case sderiv ζ A hζ' _ =>
      rw [← Path.coderiv_deriv] at hA
      cases Path.sderiv_index_injective hA
      apply Path.sderiv_path_injective at hA
      cases A
      case nil =>
        cases hA
        cases not_mem_strong_botDeriv _ _ hN₂'
      case sderiv ζ A hζ _ _ =>
        rw [← Path.coderiv_deriv] at hA
        cases Path.sderiv_index_injective hA
        apply Path.sderiv_path_injective at hA
        cases hA
        simp only [Path.coderiv_deriv, Path.coderiv_deriv', add_derivBot, scoderiv_botDeriv_eq,
          smul_derivBot, BaseSupport.add_nearLitters, BaseSupport.smul_nearLitters] at hi ⊢
        have : N₂ᴸ = (ρ₂ ⇘ A)ᵁ ↘ hζ ↘. • (ρ₁⁻¹ ⇘ A)ᵁ ↘ hζ ↘. • fuzz hδε t := by
          rw [inv_smul_eq_iff] at hN₁'
          rw [hN₁', Path.botSderiv_coe_eq, BasePerm.smul_nearLitter_litter,
            BasePerm.smul_nearLitter_litter, smul_smul, smul_eq_iff_eq_inv_smul,
            mul_inv_rev, inv_inv, mul_smul, ← Tree.inv_apply, ← allPermForget_inv] at hN₁
          rw [hN₁]
          simp only [allPermForget_inv, Tree.inv_apply, allPermDeriv_forget, Tree.inv_deriv,
            Tree.inv_sderiv, Tree.inv_sderivBot]
          rfl
        rw [smul_fuzz hδ hε hδε, smul_fuzz hδ hε hδε] at this
        have := fuzz_injective (hN₂.symm.trans this)
        rw [smul_smul] at this
        rw [t.smul_nearLitter_eq_of_mem_support this hN₀]
        rw [Enumeration.rel_add_iff] at hi ⊢
        obtain hi | ⟨i, rfl, hi⟩ := hi
        · left
          simp only [allPermForget_mul, allPermSderiv_forget, allPermDeriv_forget,
            allPermForget_inv, Tree.inv_deriv, Tree.inv_sderiv, Tree.mul_apply, Tree.sderiv_apply,
            Tree.deriv_apply, Path.deriv_scoderiv, Tree.inv_apply, mul_smul]
          rwa [← (hρ₁ _).2 N₀ ⟨i, hi⟩, inv_smul_smul, (hρ₂ _).2 N₀ ⟨i, hi⟩]
        · refine Or.inr ⟨i, rfl, ?_⟩
          simp only [allPermForget_mul, allPermSderiv_forget, allPermDeriv_forget,
            allPermForget_inv, Tree.inv_deriv, Tree.inv_sderiv, Tree.mul_apply, Tree.sderiv_apply,
            Tree.deriv_apply, Path.deriv_scoderiv, Tree.inv_apply, mul_smul, Enumeration.smul_rel,
            inv_smul_smul]
          exact hi

theorem litter_eq_of_flexible_of_fixes {S : Support α} {T : Support γ}
    {ρ₁ ρ₂ : AllPerm β} {hγ : (γ : TypeIndex) < β}
    (hρ₁ : ρ₁ᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim)
    (hρ₂ : ρ₂ᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim)
    {A : ↑α ↝ ⊥} {N₁ N₂ N₃ N₄ : NearLitter} :
    convNearLitters
      (S + (ρ₁ᵁ • ((T ↗ hγ).strong +
        (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim)
      (S + (ρ₂ᵁ • ((T ↗ hγ).strong +
        (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim) A N₁ N₂ →
    convNearLitters
      (S + (ρ₁ᵁ • ((T ↗ hγ).strong +
        (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim)
      (S + (ρ₂ᵁ • ((T ↗ hγ).strong +
        (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim) A N₃ N₄ →
      ¬Inflexible A N₁ᴸ → ¬Inflexible A N₂ᴸ → ¬Inflexible A N₃ᴸ → ¬Inflexible A N₄ᴸ →
      N₁ᴸ = N₃ᴸ → N₂ᴸ = N₄ᴸ := by
  rw [Support.smul_eq_iff] at hρ₁ hρ₂
  rintro ⟨i, hi₁, hi₂⟩ ⟨j, hj₁, hj₂⟩ hN₁ hN₂ hN₃ hN₄ hN₁₃
  simp only [add_derivBot, BaseSupport.add_nearLitters, Rel.inv_apply,
    Enumeration.rel_add_iff] at hi₁ hi₂ hj₁ hj₂
  obtain hi₁ | ⟨i, rfl, hi₁⟩ := hi₁
  · obtain hi₂ | ⟨i, rfl, hi₂⟩ := hi₂
    swap
    · have := Enumeration.lt_bound _ _ ⟨_, hi₁⟩
      simp only [add_lt_iff_neg_left] at this
      cases (κ_zero_le i).not_lt this
    cases (Enumeration.rel_coinjective _).coinjective hi₁ hi₂
    obtain hj₁ | ⟨j, rfl, hj₁⟩ := hj₁
    · obtain hj₂ | ⟨j, rfl, hj₂⟩ := hj₂
      swap
      · have := Enumeration.lt_bound _ _ ⟨_, hj₁⟩
        simp only [add_lt_iff_neg_left] at this
        cases (κ_zero_le j).not_lt this
      cases (Enumeration.rel_coinjective _).coinjective hj₁ hj₂
      exact hN₁₃
    · simp only [add_right_inj, exists_eq_left] at hj₂
      obtain hj₂ | hj₂ := hj₂
      · have := Enumeration.lt_bound _ _ ⟨_, hj₂⟩
        simp only [add_lt_iff_neg_left] at this
        cases (κ_zero_le j).not_lt this
      obtain ⟨A, rfl⟩ := eq_of_nearLitter_mem_scoderiv_botDeriv ⟨j, hj₁⟩
      simp only [scoderiv_botDeriv_eq, smul_derivBot, add_derivBot, BaseSupport.smul_nearLitters,
        BaseSupport.add_nearLitters, Enumeration.smul_rel] at hj₁ hj₂
      have := congr_arg (·ᴸ) ((Enumeration.rel_coinjective _).coinjective hj₁ hj₂)
      simp only [BasePerm.smul_nearLitter_litter] at this
      rw [← hN₁₃, ← (hρ₁ A).2 N₁ ⟨i, hi₁⟩, BasePerm.smul_nearLitter_litter, inv_smul_smul] at this
      have hN₁' := (hρ₂ A).2 N₁ ⟨i, hi₁⟩
      rw [smul_eq_iff_eq_inv_smul] at hN₁'
      rwa [hN₁', BasePerm.smul_nearLitter_litter, smul_left_cancel_iff] at this
  · obtain hi₂ | hi₂ := hi₂
    · have := Enumeration.lt_bound _ _ ⟨_, hi₂⟩
      simp only [add_lt_iff_neg_left] at this
      cases (κ_zero_le i).not_lt this
    simp only [add_right_inj, exists_eq_left] at hi₂
    obtain ⟨A, rfl⟩ := eq_of_nearLitter_mem_scoderiv_botDeriv ⟨i, hi₁⟩
    simp only [scoderiv_botDeriv_eq, smul_derivBot, add_derivBot, BaseSupport.smul_nearLitters,
      BaseSupport.add_nearLitters, Enumeration.smul_rel] at hi₁ hi₂ hj₁ hj₂
    have hN₁₂ := congr_arg (·ᴸ) ((Enumeration.rel_coinjective _).coinjective hi₁ hi₂)
    obtain hj₁ | ⟨j, rfl, hj₁⟩ := hj₁
    · obtain hj₂ | ⟨j, rfl, hj₂⟩ := hj₂
      swap
      · have := Enumeration.lt_bound _ _ ⟨_, hj₁⟩
        simp only [add_lt_iff_neg_left] at this
        cases (κ_zero_le j).not_lt this
      cases (Enumeration.rel_coinjective _).coinjective hj₁ hj₂
      simp only [BasePerm.smul_nearLitter_litter] at hN₁₂
      rw [hN₁₃, ← (hρ₁ A).2 N₃ ⟨j, hj₁⟩, BasePerm.smul_nearLitter_litter, inv_smul_smul,
        eq_inv_smul_iff, ← BasePerm.smul_nearLitter_litter, (hρ₂ A).2 N₃ ⟨j, hj₁⟩] at hN₁₂
      rw [hN₁₂]
    · simp only [add_right_inj, exists_eq_left] at hj₂
      obtain hj₂ | hj₂ := hj₂
      · have := Enumeration.lt_bound _ _ ⟨_, hj₂⟩
        simp only [add_lt_iff_neg_left] at this
        cases (κ_zero_le j).not_lt this
      have hN₃₄ := congr_arg (·ᴸ) ((Enumeration.rel_coinjective _).coinjective hj₁ hj₂)
      simp only [BasePerm.smul_nearLitter_litter] at hN₁₂ hN₃₄
      rw [hN₁₃] at hN₁₂
      rwa [hN₁₂, smul_left_cancel_iff] at hN₃₄

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
  case convAtoms_injective => exact convAtoms_injective_of_fixes hρ₁ hρ₂
  case atomMemRel_le => exact atomMemRel_le_of_fixes hρ₁ hρ₂
  case inflexible_of_inflexible => exact inflexible_of_inflexible_of_fixes hρ₁ hρ₂
  case atoms_of_inflexible => exact atoms_of_inflexible_of_fixes hS hρ₁ hρ₂
  case nearLitters_of_inflexible => exact nearLitters_of_inflexible_of_fixes hS hρ₁ hρ₂
  case litter_eq_of_flexible => exact litter_eq_of_flexible_of_fixes hρ₁ hρ₂

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
