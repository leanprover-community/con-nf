import ConNF.Counting.CountSpec
import ConNF.Counting.CountStrongOrbit
import ConNF.Counting.CountCodingFunction
import ConNF.Counting.CountRaisedSingleton

open Cardinal Function MulAction Set Quiver

open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions] [CountingAssumptions]

theorem mk_codingFunction (β : Λ) [i : LeLevel β] (hzero : #(CodingFunction 0) < #μ) :
    #(CodingFunction β) < #μ := by
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
    exact hzero

noncomputable def Shell.code {β : Λ} [LeLevel β] (t : Shell β) : CodingFunction β × Support β :=
  (CodingFunction.code _ _ (Shell.support_supports t), t.support)

theorem Shell.code_injective {β : Λ} [LeLevel β] : Function.Injective (Shell.code (β := β)) := by
  intro t₁ t₂ h
  rw [code, code] at h
  simp only [Prod.mk.injEq, CodingFunction.code_eq_code_iff] at h
  obtain ⟨⟨ρ, h₁, rfl⟩, h₂⟩ := h
  refine (Shell.support_supports t₁ ρ ?_).symm
  rintro c ⟨i, hi, hc⟩
  have := support_f_congr h₂ i hi
  simp only [← hc, h₁, Enumeration.smul_f] at this
  exact this.symm

theorem mk_shell_le (β : Λ) [LeLevel β] (hzero : #(CodingFunction 0) < #μ) : #(Shell β) ≤ #μ := by
  refine (mk_le_of_injective Shell.code_injective).trans ?_
  simp only [mk_prod, lift_id, mk_support]
  exact Cardinal.mul_le_of_le (mk_codingFunction β hzero).le le_rfl
    Params.μ_isStrongLimit.isLimit.aleph0_le

theorem mk_tangle_le (β : Λ) [LeLevel β] : #(Tangle β) ≤ #(Shell β) * #(Support β) := by
  refine mk_le_of_injective (f := fun t : Tangle β => (Shell.ofTangle t, t.support)) ?_
  intro t₁ t₂ h
  simp only [Prod.mk.injEq] at h
  refine tangle_ext β t₁ t₂ ?_ h.2
  rw [Shell.ofTangle_eq_iff]
  exact h.1

theorem mk_tangle (β : Λ) [LeLevel β] (hzero : #(CodingFunction 0) < #μ) : #(Tangle β) = #μ := by
  refine le_antisymm ?_ ?_
  · refine le_trans (mk_tangle_le β) ?_
    exact mul_le_of_le (mk_shell_le β hzero) mk_support.le Params.μ_isStrongLimit.isLimit.aleph0_le
  · have := mk_le_of_injective (typedAtom (α := β)).injective
    simp only [mk_atom] at this
    exact this

end ConNF
