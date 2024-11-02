import ConNF.Counting.BaseCoding
import ConNF.Counting.CountSupportOrbit

/-!
# Counting coding functions at level `⊥` and `0`

In this file, we show that there are less than `μ` coding functions at levels `⊥` and `0`.

## Main declarations

* `ConNF.card_bot_codingFunction_lt`, `ConNF.card_codingFunction_lt_of_isMin`: There are less than
  `μ` coding functions at levels `⊥` and `0`.
-/

noncomputable section
universe u

open Cardinal Ordinal WithBot

namespace ConNF

variable [Params.{u}] [Level] [CoherentData]

theorem card_codingFunction_lt_of_card_supportOrbit_lt {β : TypeIndex} [LeLevel β]
    (ν : Cardinal.{u}) (hν : ν < #μ)
    (hβ : #(SupportOrbit β) < #μ)
    (hνS : ∀ S : Support β, #{x : TSet β // S.Supports x} ≤ ν) :
    #(CodingFunction β) < #μ := by
  have := mk_le_of_surjective
    (f := λ x : (o : SupportOrbit β) × {x : TSet β // o.out.Supports x} ↦
      (Tangle.code ⟨x.2, x.1.out, x.2.prop⟩ : CodingFunction β)) ?_
  · apply this.trans_lt
    simp only [mk_sigma]
    refine (sum_le_sum (g := λ _ ↦ ν) ?_ ?_).trans_lt ?_
    · intro o
      exact hνS o.out
    · simp only [sum_const, Cardinal.lift_id]
      exact mul_lt_of_lt μ_isStrongLimit.aleph0_le hβ hν
  · intro χ
    obtain ⟨S, x, hx⟩ := χ.rel_dom_nonempty
    have : S.orbit = S.orbit.out.orbit := by rw [SupportOrbit.out_orbit (β := β)]
    rw [Support.orbit_eq_iff] at this
    obtain ⟨ρ, hρ⟩ := this
    refine ⟨⟨S.orbit, ρ • x, ?_⟩, ?_⟩
    · rw [← hρ]
      exact (χ.supports_of_rel hx).smul ρ
    refine CodingFunction.ext S x ?_ hx
    dsimp only
    refine ⟨ρ⁻¹, ?_, ?_⟩
    · simp only [allPermForget_inv, ← hρ, inv_smul_smul]
    · simp only [inv_smul_smul]

theorem card_bot_codingFunction_lt :
    #(CodingFunction ⊥) < #μ := by
  apply card_codingFunction_lt_of_card_supportOrbit_lt (2 ^ #κ)
  · exact μ_isStrongLimit.2 _ κ_lt_μ
  · apply card_supportOrbit_lt
    intro δ hδ
    cases not_lt_bot hδ
  intro S
  apply le_trans ?_ (card_supports_le (S ⇘. .nil))
  refine mk_le_of_injective (f := λ x ↦ ⟨{StrSet.botEquiv x.valᵁ}, ?_⟩) ?_
  · intro π hπ
    obtain ⟨ρ, hρ⟩ := allPerm_of_basePerm π
    have := x.prop.supports ρ ?_
    · rw [Set.smul_set_singleton, Set.singleton_eq_singleton_iff]
      have := congr_arg (λ x ↦ StrSet.botEquiv xᵁ) this
      simp only [smul_forget, StrSet.strPerm_smul_bot, hρ] at this
      exact this
    · apply Support.ext
      intro A
      cases Path.eq_nil A
      simp only [Support.smul_derivBot, hρ, hπ]
  · intro x y h
    rw [Subtype.mk.injEq, Set.singleton_eq_singleton_iff,
      EmbeddingLike.apply_eq_iff_eq] at h
    exact Subtype.coe_injective (tSetForget_injective h)

omit [CoherentData] in
theorem eq_bot_of_lt_of_isMin {β : Λ} [LeLevel β] (hβ : IsMin β) {δ : TypeIndex} (hδ : δ < β) :
    δ = ⊥ := by
  cases δ using recBotCoe
  case bot => rfl
  case coe δ =>
    cases hδ.not_le (coe_le_coe.mpr (hβ (coe_le_coe.mp hδ.le)))

theorem allPerm_of_basePerm_of_isMin {β : Λ} [LeLevel β] (hβ : IsMin β) (π : BasePerm) :
    ∃ ρ : AllPerm β, ρᵁ (Path.nil ↘.) = π := by
  obtain ⟨ρ, hρ⟩ := allPerm_of_basePerm π
  have := allPerm_of_smulFuzz (γ := β) (λ {δ} _ hδ ↦ eq_bot_of_lt_of_isMin hβ hδ ▸ ρ) ?_
  · obtain ⟨ρ', hρ'⟩ := this
    use ρ'
    have := hρ' ⊥ (bot_lt_coe _)
    simp only at this
    cases this
    cases hρ
    simp only [allPermSderiv_forget, Tree.sderiv_apply]
    rfl
  · intro _ _ _ _ _ _ hε
    cases eq_bot_of_lt_of_isMin hβ hε

omit [CoherentData] in
theorem path_eq_of_isMin {β : Λ} [LeLevel β] (hβ : IsMin β) (A : β ↝ ⊥) :
    A = Path.nil ↘. := by
  cases A
  case sderiv γ A h₁ h₂ =>
    cases γ using recBotCoe
    case bot => cases not_lt_bot h₁
    case coe γ =>
      cases le_antisymm (coe_le_coe.mp A.le) (hβ (coe_le_coe.mp A.le))
      cases Path.eq_nil A
      rfl

theorem card_codingFunction_lt_of_isMin {β : Λ} [LeLevel β] (hβ : IsMin β) :
    #(CodingFunction β) < #μ := by
  apply card_codingFunction_lt_of_card_supportOrbit_lt (2 ^ #κ)
  · exact μ_isStrongLimit.2 _ κ_lt_μ
  · apply card_supportOrbit_lt
    intro δ hδ
    cases eq_bot_of_lt_of_isMin hβ hδ
    exact card_bot_codingFunction_lt
  intro S
  apply le_trans ?_ (card_supports_le (S ⇘. (Path.nil ↘.)))
  refine mk_le_of_injective
    (f := λ x ↦ ⟨StrSet.botEquiv '' StrSet.coeEquiv x.valᵁ ⊥ (bot_lt_coe _), ?_⟩) ?_
  · intro π hπ
    obtain ⟨ρ, hρ⟩ := allPerm_of_basePerm_of_isMin hβ π
    have := x.prop.supports ρ ?_
    · have := congr_arg (λ x ↦ StrSet.botEquiv '' StrSet.coeEquiv xᵁ ⊥ (bot_lt_coe _)) this
      convert this using 1
      cases hρ
      simp only [smul_forget, StrSet.strPerm_smul_coe]
      ext a
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        refine ⟨ρᵁ ↘ (bot_lt_coe _) • a, ⟨a, ha, rfl⟩, ?_⟩
        simp only [StrSet.strPerm_smul_bot, Tree.sderiv_apply]
        rfl
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        refine ⟨_, ⟨a, ha, rfl⟩, ?_⟩
        simp only [StrSet.strPerm_smul_bot, Tree.sderiv_apply]
        rfl
    · apply Support.ext
      intro A
      cases path_eq_of_isMin hβ A
      rw [← hπ, ← hρ]
      rfl
  · intro x y h
    simp only [Subtype.mk.injEq, Equiv.image_eq_iff_eq] at h
    apply Subtype.coe_injective
    apply tSetForget_injective
    apply (StrSet.coeEquiv (α := β)).injective
    ext γ hγ : 2
    cases eq_bot_of_lt_of_isMin hβ hγ
    rw [h]

end ConNF
