import ConNF.Counting.Spec

open Cardinal Quiver Set Sum WithBot

open scoped Cardinal symmDiff

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ} [LeLevel β]

def SpecCondition' (β : Λ) :=
  (ExtendedIndex β × Set κ × Set κ) ⊕
  (ExtendedIndex β × Set κ × (κ → Set κ)) ⊕
  ((A : ExtendedIndex β) × (h : InflexibleCoePath A) × CodingFunction h.δ × (κ → Set κ)) ⊕
  ((A : ExtendedIndex β) × InflexibleBotPath A × Set κ × (κ → Set κ))

def SpecCondition.toPrime : SpecCondition β → SpecCondition' β
  | .atom A s t => Sum.inl (A, s, t)
  | .flexible A s t => Sum.inr (Sum.inl (A, s, t))
  | .inflexibleCoe A h χ _ t => Sum.inr (Sum.inr (Sum.inl ⟨A, h, χ, t⟩))
  | .inflexibleBot A h s t => Sum.inr (Sum.inr (Sum.inr ⟨A, h, s, t⟩))

theorem SpecCondition.toPrime_injective : Function.Injective (toPrime (β := β)) := by
  intro c d h
  cases c <;> cases d <;> unfold toPrime at h <;>
    simp only [Sum.inl_injective.eq_iff, Sum.inr_injective.eq_iff, Prod.mk.injEq] at h <;>
    aesop

theorem _root_.Cardinal.pow_mono_left (a : Cardinal) (ha : a ≠ 0) :
    Monotone (fun (b : Cardinal) => a ^ b) := by
  intro b c
  revert ha
  refine Cardinal.inductionOn₃ a b c ?_
  intro α β γ hα h
  suffices : #(β → α) ≤ #(γ → α)
  · simp only [mk_pi, prod_const, lift_id] at this
    exact this
  obtain (hβ | hβ) := isEmpty_or_nonempty β
  · rw [mk_ne_zero_iff] at hα
    obtain ⟨a⟩ := hα
    refine ⟨fun _ _ => a, ?_⟩
    intro f g _
    ext x
    cases IsEmpty.false x
  · rw [Cardinal.le_def] at h
    obtain ⟨f, hf⟩ := h
    refine mk_le_of_surjective (f := (· ∘ f)) ?_
    intro g
    obtain ⟨k, hk⟩ := hf.hasLeftInverse
    rw [Function.leftInverse_iff_comp] at hk
    refine ⟨g ∘ k, ?_⟩
    dsimp only
    rw [Function.comp.assoc, hk, Function.comp_id]

theorem mk_inflexibleCoePath (A : ExtendedIndex β) : #(InflexibleCoePath A) ≤ #Λ := sorry

theorem mk_inflexibleBotPath (A : ExtendedIndex β) : #(InflexibleBotPath A) ≤ #Λ := sorry

theorem mk_specCondition (h : ∀ (δ : Λ) [LeLevel δ], δ < β → #(CodingFunction δ) < #μ) :
    #(SpecCondition β) < #μ := by
  refine (mk_le_of_injective SpecCondition.toPrime_injective).trans_lt ?_
  rw [SpecCondition']
  simp only [mk_sum, mk_prod, lift_id, mk_set, mk_pi, prod_const, mk_sigma]
  have := Params.μ_isStrongLimit.isLimit.aleph0_le
  have mk_extendedIndex' := (mk_extendedIndex β).trans_lt (Params.Λ_lt_κ.trans Params.κ_lt_μ)
  have mk_pow_κ := Params.μ_isStrongLimit.2 _ Params.κ_lt_μ
  refine add_lt_of_lt this ?_ (add_lt_of_lt this ?_ (add_lt_of_lt this ?_ ?_))
  · exact mul_lt_of_lt this mk_extendedIndex' (mul_lt_of_lt this mk_pow_κ mk_pow_κ)
  · refine mul_lt_of_lt this mk_extendedIndex' (mul_lt_of_lt this mk_pow_κ ?_)
    rw [← Cardinal.power_mul, mul_eq_self Params.κ_isRegular.aleph0_le]
    exact mk_pow_κ
  · refine (sum_lt_prod
        (fun (A : ExtendedIndex β) =>
          sum fun (h : InflexibleCoePath A) => #(CodingFunction h.δ) * (2 ^ #κ) ^ #κ)
        (fun _ => #μ) ?_).trans_le ?_
    intro A
    refine (sum_lt_prod
        (fun (h : InflexibleCoePath A) => #(CodingFunction h.δ) * (2 ^ #κ) ^ #κ)
        (fun _ => #μ) ?_).trans_le ?_
    · intro hA
      refine mul_lt_of_lt this (h hA.δ (coe_lt_coe.mp hA.δ_lt_β)) ?_
      rw [← Cardinal.power_mul, mul_eq_self Params.κ_isRegular.aleph0_le]
      exact mk_pow_κ
    · simp only [prod_const, lift_id]
      have := pow_le_of_isStrongLimit Params.μ_isStrongLimit
        (Params.Λ_lt_κ.trans_le Params.κ_le_μ_ord_cof)
      refine (pow_mono_left #μ Params.μ_isStrongLimit.1 ?_).trans this
      exact mk_inflexibleCoePath A
    · simp only [prod_const, lift_id]
      have := pow_le_of_isStrongLimit Params.μ_isStrongLimit
        (Params.Λ_lt_κ.trans_le Params.κ_le_μ_ord_cof)
      refine (pow_mono_left #μ Params.μ_isStrongLimit.1 ?_).trans this
      exact mk_extendedIndex _
  · refine (sum_lt_prod
        (fun (A : ExtendedIndex β) =>
          #(InflexibleBotPath A) * ((2 ^ #κ) * (2 ^ #κ) ^ #κ))
        (fun _ => #μ) ?_).trans_le ?_
    intro A
    · refine mul_lt_of_lt this ?_ (mul_lt_of_lt this mk_pow_κ ?_)
      · exact (mk_inflexibleBotPath A).trans_lt (Params.Λ_lt_κ.trans Params.κ_lt_μ)
      · rw [← Cardinal.power_mul, mul_eq_self Params.κ_isRegular.aleph0_le]
        exact mk_pow_κ
    · simp only [prod_const, lift_id]
      have := pow_le_of_isStrongLimit Params.μ_isStrongLimit
        (Params.Λ_lt_κ.trans_le Params.κ_le_μ_ord_cof)
      refine (pow_mono_left #μ Params.μ_isStrongLimit.1 ?_).trans this
      exact mk_extendedIndex _

end ConNF
