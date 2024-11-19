import ConNF.Counting.BaseCounting
import ConNF.Counting.CountSupportOrbit
import ConNF.Counting.Recode

/-!
# Concluding the counting argument

In this file, we finish the counting argument.

## Main declarations

* `ConNF.card_tSet_le`: There are at most `μ`-many t-sets at each level.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}] [Level] [CoherentData]

theorem card_codingFunction (β : TypeIndex) [LeLevel β] :
    #(CodingFunction β) < #μ := by
  revert β
  intro β
  induction β using WellFoundedLT.induction
  case ind β ih =>
  intro
  cases β using WithBot.recBotCoe
  case bot => exact card_bot_codingFunction_lt
  case coe β _ =>
  by_cases hβ : IsMin β
  · exact card_codingFunction_lt_of_isMin hβ
  rw [not_isMin_iff] at hβ
  obtain ⟨γ, hγ⟩ := hβ
  have hγ := WithBot.coe_lt_coe.mpr hγ
  have : LeLevel γ := ⟨hγ.le.trans LeLevel.elim⟩
  have := exists_combination_raisedSingleton hγ
  choose s o h₁ h₂ using this
  refine (mk_le_of_injective (f := λ χ ↦ (s χ, o χ)) ?_).trans_lt ?_
  · intro χ₁ χ₂ h
    rw [Prod.mk.injEq] at h
    have hχ₁ := h₂ χ₁
    have hχ₂ := h₂ χ₂
    simp only [h.1, h.2, ← hχ₂] at hχ₁
    exact hχ₁
  · rw [mk_prod, mk_set, Cardinal.lift_id, Cardinal.lift_id]
    refine mul_lt_of_lt μ_isStrongLimit.aleph0_le ?_ (card_supportOrbit_lt ih)
    apply μ_isStrongLimit.2
    exact card_raisedSingleton_lt _ (card_supportOrbit_lt ih) ih

theorem card_supportOrbit (β : TypeIndex) [LeLevel β] :
    #(SupportOrbit β) < #μ := by
  apply card_supportOrbit_lt
  intro δ _ _
  exact card_codingFunction δ

/-- Note that we cannot prove the reverse implication because all of our hypotheses at this stage
are about permutations, not objects. -/
theorem card_tSet_le (β : TypeIndex) [LeLevel β] :
    #(TSet β) ≤ #μ := by
  refine (mk_le_of_injective
    (f := λ x : TSet β ↦ (Tangle.code ⟨x, designatedSupport x, designatedSupport_supports x⟩,
      designatedSupport x)) ?_).trans ?_
  · intro x y h
    rw [Prod.mk.injEq, Tangle.code_eq_code_iff] at h
    obtain ⟨⟨ρ, hρ⟩, h⟩ := h
    have := (designatedSupport_supports x).supports ρ ?_
    · have hρx := congr_arg (·.set) hρ
      simp only [Tangle.smul_set] at hρx
      rw [← hρx, this]
    · have hρx := congr_arg (·.support) hρ
      simp only [Tangle.smul_support] at hρx
      rw [hρx, h]
  · rw [mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    apply mul_le_of_le μ_isStrongLimit.aleph0_le (card_codingFunction β).le
    rw [card_support]

theorem card_tangle_le (β : TypeIndex) [LeLevel β] :
    #(Tangle β) ≤ #μ :=
  card_tangle_le_of_card_tSet (card_tSet_le β)

end ConNF
