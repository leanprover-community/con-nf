import ConNF.Counting.Spec

open Cardinal Quiver Set Sum WithBot

open scoped Cardinal symmDiff

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions] [CountingAssumptions] {β : Λ} [LeLevel β]

def SpecCondition' (β : Λ) :=
  (ExtendedIndex β × Set κ × Set κ) ⊕
  (ExtendedIndex β × Set κ × (κ → Set κ)) ⊕
  ((A : ExtendedIndex β) × (h : InflexibleCoePath A) × CodingFunction h.δ ×
    (κ → Set κ) × κ × (κ → Set κ)) ⊕
  ((A : ExtendedIndex β) × InflexibleBotPath A × Set κ × (κ → Set κ))

def SpecCondition.toPrime : SpecCondition β → SpecCondition' β
  | .atom A s t => Sum.inl (A, s, t)
  | .flexible A s t => Sum.inr (Sum.inl (A, s, t))
  | .inflexibleCoe A h χ _ t m u => Sum.inr (Sum.inr (Sum.inl ⟨A, h, χ, t, m, u⟩))
  | .inflexibleBot A h s t => Sum.inr (Sum.inr (Sum.inr ⟨A, h, s, t⟩))

theorem SpecCondition.toPrime_injective : Function.Injective (toPrime (β := β)) := by
  intro c d h
  cases c <;> cases d <;> unfold toPrime at h <;>
    simp only [Sum.inl_injective.eq_iff, Sum.inr_injective.eq_iff, Prod.mk.injEq] at h <;>
    aesop

def InflexibleCoePath' (β : Λ) : Type u :=
  Λ × Λ × Λ × ExtendedIndex β

def InflexibleCoePath'.toPrime {A : ExtendedIndex β} (h : InflexibleCoePath A) :
    InflexibleCoePath' β :=
  ⟨h.γ, h.δ, h.ε, h.B.cons (bot_lt_coe _)⟩

theorem InflexibleCoePath'.toPrime_injective {A : ExtendedIndex β} :
    Function.Injective (toPrime (A := A)) := by
  intro h₁ h₂ h
  cases h₁
  cases h₂
  cases h
  rfl

theorem mk_inflexibleCoePath (A : ExtendedIndex β) : #(InflexibleCoePath A) ≤ #Λ := by
  refine (mk_le_of_injective InflexibleCoePath'.toPrime_injective).trans ?_
  simp only [InflexibleCoePath', mk_prod, lift_id]
  refine (Cardinal.mul_le_max _ _).trans ?_
  simp only [ge_iff_le, le_max_iff, aleph0_le_mk, true_or, max_eq_left, max_le_iff, le_refl,
    true_and]
  refine (Cardinal.mul_le_max _ _).trans ?_
  simp only [ge_iff_le, le_max_iff, aleph0_le_mk, true_or, max_eq_left, max_le_iff, le_refl,
    true_and]
  refine (Cardinal.mul_le_max _ _).trans ?_
  simp only [ge_iff_le, le_max_iff, aleph0_le_mk, true_or, max_eq_left, max_le_iff, le_refl,
    true_and]
  exact mk_extendedIndex _

def InflexibleBotPath' (β : Λ) : Type u :=
  Λ × Λ × ExtendedIndex β

def InflexibleBotPath'.toPrime {A : ExtendedIndex β} (h : InflexibleBotPath A) :
    InflexibleBotPath' β :=
  ⟨h.γ, h.ε, h.B.cons (bot_lt_coe _)⟩

theorem InflexibleBotPath'.toPrime_injective {A : ExtendedIndex β} :
    Function.Injective (toPrime (A := A)) := by
  intro h₁ h₂ h
  cases h₁
  cases h₂
  cases h
  rfl

theorem mk_inflexibleBotPath (A : ExtendedIndex β) : #(InflexibleBotPath A) ≤ #Λ := by
  refine (mk_le_of_injective InflexibleBotPath'.toPrime_injective).trans ?_
  simp only [InflexibleBotPath', mk_prod, lift_id]
  refine (Cardinal.mul_le_max _ _).trans ?_
  simp only [ge_iff_le, le_max_iff, aleph0_le_mk, true_or, max_eq_left, max_le_iff, le_refl,
    true_and]
  refine (Cardinal.mul_le_max _ _).trans ?_
  simp only [ge_iff_le, le_max_iff, aleph0_le_mk, true_or, max_eq_left, max_le_iff, le_refl,
    true_and]
  exact mk_extendedIndex _

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
          sum fun (h : InflexibleCoePath A) => #(CodingFunction h.δ) *
            ((2 ^ #κ) ^ #κ * (#κ * (2 ^ #κ) ^ #κ)))
        (fun _ => #μ) ?_).trans_le ?_
    intro A
    refine (sum_lt_prod
        (fun (h : InflexibleCoePath A) => #(CodingFunction h.δ) *
          ((2 ^ #κ) ^ #κ * (#κ * (2 ^ #κ) ^ #κ)))
        (fun _ => #μ) ?_).trans_le ?_
    · intro hA
      refine mul_lt_of_lt this (h hA.δ (coe_lt_coe.mp hA.δ_lt_β)) ?_
      rw [← Cardinal.power_mul, mul_eq_self Params.κ_isRegular.aleph0_le]
      refine mul_lt_of_lt this mk_pow_κ ?_
      exact mul_lt_of_lt this Params.κ_lt_μ mk_pow_κ
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

theorem mk_spec (h : ∀ (δ : Λ) [LeLevel δ], δ < β → #(CodingFunction δ) < #μ) :
    #(Spec β) < #μ :=
  mk_enumeration_lt (mk_specCondition h)

end ConNF
