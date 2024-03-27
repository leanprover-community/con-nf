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
    have : #(SupportOrbit β) < #μ
    · refine (mk_supportOrbit_le β).trans_lt ?_
      refine mul_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le ?_ ?_
      · exact Params.μ_isStrongLimit.2 _ Params.κ_lt_μ
      · refine mk_spec ?_
        intro δ _ hδ
        exact ih δ hδ
    refine mul_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le this ?_
    refine Params.μ_isStrongLimit.2 _ ?_
    refine (mk_raisedSingleton_le hγ).trans_lt ?_
    exact mul_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le
      (mul_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le Params.κ_lt_μ this)
      (ih γ (WithBot.coe_lt_coe.mp hγ))
  · simp only [WithBot.coe_lt_coe, not_exists, not_lt] at h
    cases le_antisymm (h 0) (Params.Λ_zero_le β)
    exact hzero

noncomputable def TSet.code {β : Λ} [LeLevel β] (t : TSet β) : CodingFunction β × Support β :=
  (CodingFunction.code _ _ (TangleData.TSet.support_supports t), t.support)

theorem TSet.code_injective {β : Λ} [LeLevel β] : Function.Injective (TSet.code (β := β)) := by
  intro t₁ t₂ h
  rw [code, code] at h
  simp only [Prod.mk.injEq, CodingFunction.code_eq_code_iff] at h
  obtain ⟨⟨ρ, h₁, rfl⟩, h₂⟩ := h
  refine (TangleData.TSet.support_supports t₁ ρ ?_).symm
  rintro c ⟨i, hi, hc⟩
  have := support_f_congr h₂ i hi
  simp only [← hc, h₁, Enumeration.smul_f] at this
  exact this.symm

theorem mk_tSet_le (β : Λ) [LeLevel β] (hzero : #(CodingFunction 0) < #μ) : #(TSet β) ≤ #μ := by
  refine (mk_le_of_injective TSet.code_injective).trans ?_
  simp only [mk_prod, lift_id, mk_support]
  exact Cardinal.mul_le_of_le (mk_codingFunction β hzero).le le_rfl
    Params.μ_isStrongLimit.isLimit.aleph0_le

theorem mk_tangle_le (β : Λ) [LeLevel β] : #(Tangle β) ≤ #(TSet β) * #(Support β) := by
  refine mk_le_of_injective (f := fun t : Tangle β => (t.set, t.support)) ?_
  intro t₁ t₂ h
  simp only [Prod.mk.injEq] at h
  exact Tangle.ext t₁ t₂ h.1 h.2

theorem exists_tangle [i : CountingAssumptions] {β : TypeIndex} [iβ : LeLevel β] (t : TSet β) :
    ∃ u : Tangle β, u.set = t := by
  revert i iβ
  change (_ : _) → _
  refine WithBot.recBotCoe ?_ ?_ β
  · intro _ _ t
    exact ⟨t, rfl⟩
  · intro β _ _ t
    obtain ⟨S, hS⟩ := t.has_support
    exact ⟨⟨t, S, hS⟩, rfl⟩

protected noncomputable def Tangle.typedAtom (β : Λ) [LeLevel β] (a : Atom) : Tangle β :=
  (exists_tangle (typedAtom a)).choose

protected noncomputable def Tangle.typedAtom_injective (β : Λ) [LeLevel β] :
    Function.Injective (Tangle.typedAtom β) := by
  intro a₁ a₂ h
  refine (typedAtom (α := β)).injective ?_
  rw [← (exists_tangle (typedAtom a₁)).choose_spec, ← (exists_tangle (typedAtom a₂)).choose_spec]
  exact congr_arg Tangle.set h

theorem mk_tangle (β : Λ) [LeLevel β] (hzero : #(CodingFunction 0) < #μ) : #(Tangle β) = #μ := by
  refine le_antisymm ?_ ?_
  · refine le_trans (mk_tangle_le β) ?_
    exact mul_le_of_le (mk_tSet_le β hzero) mk_support.le Params.μ_isStrongLimit.isLimit.aleph0_le
  · have := mk_le_of_injective (Tangle.typedAtom_injective β)
    simp only [mk_atom] at this
    exact this

end ConNF
