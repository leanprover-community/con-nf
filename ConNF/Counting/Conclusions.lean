import ConNF.Counting.CountSpec
import ConNF.Counting.CountStrongOrbit
import ConNF.Counting.CountCodingFunction
import ConNF.Counting.CountRaisedSingleton

open Cardinal Function MulAction Set Quiver

open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] [Level] [CountingAssumptions]

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
  · sorry

end ConNF
