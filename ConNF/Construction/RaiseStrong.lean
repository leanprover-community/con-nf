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

theorem Support.not_mem_strongbotDeriv (S : Support γ) (N : NearLitter) :
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

theorem Support.not_mem_strong_botDeriv (S : Support γ) (N : NearLitter) :
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

theorem Support.raise_preStrong (S : Support γ) (hγ : (γ : TypeIndex) < β) :
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
      rw [Path.coderiv_deriv, Support.scoderiv_deriv_eq]
      exact (S ↗ hγ).strong_strong.support_le ⟨i, hB₂⟩ ⟨γ, δ, ε, hδ, hε, hδε, B⟩ t rfl ht

theorem Support.raise_strong (S : Support γ) (hγ : (γ : TypeIndex) < β) :
    ((S ↗ hγ).strong ↗ LtLevel.elim).Strong := by
  sorry

end ConNF
