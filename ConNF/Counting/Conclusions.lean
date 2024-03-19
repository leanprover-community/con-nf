import ConNF.Counting.CountSpec
import ConNF.Counting.CountStrongOrbit
import ConNF.Counting.CountCodingFunction
import ConNF.Counting.CountRaisedSingleton

open Cardinal Function MulAction Set Quiver

open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions] [CountingAssumptions]

theorem mk_codingFunction (β : Λ) [i : LeLevel β] : #(CodingFunction β) < #μ := by
  revert i
  refine Params.Λ_isWellOrder.induction (C := fun β => [LeLevel β] → #(CodingFunction β) < #μ) β ?_
  intro β ih _
  by_cases h : ∃ γ : Λ, (γ : TypeIndex) < β
  · obtain ⟨γ, hγ⟩ := h
    have : LeLevel γ := ⟨le_trans hγ.le LeLevel.elim⟩
    refine (mk_codingFunction_le hγ).trans_lt ?_
    refine (sum_le_sum _ (fun _ => 2 ^ (#(SupportOrbit β) * #(CodingFunction γ))) ?_).trans_lt ?_
    · intro o
      have := mk_raisedSingleton_le hγ o.out
      exact Cardinal.pow_mono_left 2 two_ne_zero this
    rw [sum_const, lift_id, lift_id]
    have : #(SupportOrbit β) < #μ
    · refine (mk_supportOrbit_le β).trans_lt ?_
      refine mul_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le ?_ ?_
      · exact Params.μ_isStrongLimit.2 _ Params.κ_lt_μ
      · refine mk_spec ?_
        intro δ _ hδ
        exact ih δ hδ
    refine mul_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le this ?_
    · refine Params.μ_isStrongLimit.2 _ ?_
      exact mul_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le this
        (ih γ (WithBot.coe_lt_coe.mp hγ))
  · simp only [WithBot.coe_lt_coe, not_exists, not_lt] at h
    cases le_antisymm (h 0) (Params.Λ_zero_le β)
    exact mk_codingFunction_zero

noncomputable def Tangle.code {β : Λ} [LeLevel β] (t : Tangle β) : CodingFunction β × Support β :=
  (CodingFunction.code _ _ (support_supports t), t.support)

theorem Tangle.code_injective {β : Λ} [LeLevel β] : Function.Injective (Tangle.code (β := β)) := by
  intro t₁ t₂ h
  rw [code, code] at h
  simp only [Prod.mk.injEq, CodingFunction.code_eq_code_iff] at h
  obtain ⟨⟨ρ, _, rfl⟩, h⟩ := h
  refine (support_supports t₁ ρ ?_).symm
  rintro c ⟨i, hi, hc⟩
  have := support_f_congr h i hi
  simp only [← hc, smul_support, Enumeration.smul_f] at this
  exact this.symm

/-- **Theorem.** There are exactly `μ` tangles at each level. -/
@[simp]
theorem mk_tangle (β : Λ) [LeLevel β] : #(Tangle β) = #μ := by
  refine le_antisymm ?_ ?_
  · refine (mk_le_of_injective Tangle.code_injective).trans ?_
    simp only [mk_prod, lift_id, mk_support]
    exact Cardinal.mul_le_of_le (mk_codingFunction β).le le_rfl
      Params.μ_isStrongLimit.isLimit.aleph0_le
  · have := mk_le_of_injective (typedAtom (α := β)).injective
    simp only [mk_atom] at this
    exact this

end ConNF
