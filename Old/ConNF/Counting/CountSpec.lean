import ConNF.Counting.Spec

open Cardinal Quiver Set Sum WithBot

open scoped Cardinal symmDiff

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions] [FOAAssumptions] {β : Λ} [LeLevel β]

def SpecCondition' (β : Λ) :=
  (ExtendedIndex β × Set κ × Set κ) ⊕
  (ExtendedIndex β × Set κ × (κ → Set κ)) ⊕
  ((A : ExtendedIndex β) × (h : InflexibleCoePath A) × CodingFunction h.δ ×
    (κ → Set κ) × κ × (κ → Set κ)) ⊕
  ((A : ExtendedIndex β) × InflexibleBotPath A × Set κ × (κ → Set κ))

def SpecCondition.toPrime : SpecCondition β → SpecCondition' β
  | .atom A s t => Sum.inl (A, s, t)
  | .flexible A s t => Sum.inr (Sum.inl (A, s, t))
  | .inflexibleCoe A h χ t m u => Sum.inr (Sum.inr (Sum.inl ⟨A, h, χ, t, m, u⟩))
  | .inflexibleBot A h s t => Sum.inr (Sum.inr (Sum.inr ⟨A, h, s, t⟩))

theorem SpecCondition.toPrime_injective : Function.Injective (toPrime (β := β)) := by
  intro c d h
  cases c <;> cases d <;> unfold toPrime at h <;>
    simp only [Sum.inl_injective.eq_iff, Sum.inr_injective.eq_iff, Prod.mk.injEq] at h <;>
    aesop

def InflexibleCoePath' (β : Λ) : Type u :=
  { γ // γ ≤ β } × { γ // γ < β } × { γ // γ < β } × ExtendedIndex β

def InflexibleCoePath'.toPrime {A : ExtendedIndex β} (h : InflexibleCoePath A) :
    InflexibleCoePath' β :=
  ⟨⟨h.γ, coe_le_coe.mp (le_of_path h.B)⟩,
    ⟨h.δ, coe_lt_coe.mp (h.hδ.trans_le (le_of_path h.B))⟩,
    ⟨h.ε, coe_lt_coe.mp (h.hε.trans_le (le_of_path h.B))⟩,
    h.B.cons (bot_lt_coe _)⟩

theorem InflexibleCoePath'.toPrime_injective {A : ExtendedIndex β} :
    Function.Injective (toPrime (A := A)) := by
  intro h₁ h₂ h
  cases h₁
  cases h₂
  cases h
  rfl

theorem mk_inflexibleCoePath_lt (A : ExtendedIndex β) : #(InflexibleCoePath A) < (#μ).ord.cof := by
  refine (mk_le_of_injective InflexibleCoePath'.toPrime_injective).trans_lt ?_
  simp only [InflexibleCoePath', mk_prod, lift_id]
  refine (Cardinal.mul_le_max _ _).trans_lt ?_
  rw [max_lt_iff, max_lt_iff]
  refine ⟨⟨card_Iic_lt_Λ β, ?_⟩, Params.aleph0_lt_mk_κ.trans_le Params.κ_le_μ_ord_cof⟩
  refine (Cardinal.mul_le_max _ _).trans_lt ?_
  rw [max_lt_iff, max_lt_iff]
  refine ⟨⟨card_Iio_lt_Λ β, ?_⟩, Params.aleph0_lt_mk_κ.trans_le Params.κ_le_μ_ord_cof⟩
  refine (Cardinal.mul_le_max _ _).trans_lt ?_
  rw [max_lt_iff, max_lt_iff]
  refine ⟨⟨card_Iio_lt_Λ β, ?_⟩, Params.aleph0_lt_mk_κ.trans_le Params.κ_le_μ_ord_cof⟩
  exact mk_extendedIndex_lt_cof_μ β

def InflexibleBotPath' (β : Λ) : Type u :=
  { γ // γ ≤ β } × { γ // γ < β } × ExtendedIndex β

def InflexibleBotPath'.toPrime {A : ExtendedIndex β} (h : InflexibleBotPath A) :
    InflexibleBotPath' β :=
  ⟨⟨h.γ, coe_le_coe.mp (le_of_path h.B)⟩,
    ⟨h.ε, coe_lt_coe.mp (h.hε.trans_le (le_of_path h.B))⟩,
    h.B.cons (bot_lt_coe _)⟩

theorem InflexibleBotPath'.toPrime_injective {A : ExtendedIndex β} :
    Function.Injective (toPrime (A := A)) := by
  intro h₁ h₂ h
  cases h₁
  cases h₂
  cases h
  rfl

theorem mk_inflexibleBotPath_lt (A : ExtendedIndex β) : #(InflexibleBotPath A) < (#μ).ord.cof := by
  refine (mk_le_of_injective InflexibleBotPath'.toPrime_injective).trans_lt ?_
  simp only [InflexibleBotPath', mk_prod, lift_id]
  refine (Cardinal.mul_le_max _ _).trans_lt ?_
  rw [max_lt_iff, max_lt_iff]
  refine ⟨⟨card_Iic_lt_Λ β, ?_⟩, Params.aleph0_lt_mk_κ.trans_le Params.κ_le_μ_ord_cof⟩
  refine (Cardinal.mul_le_max _ _).trans_lt ?_
  rw [max_lt_iff, max_lt_iff]
  refine ⟨⟨card_Iio_lt_Λ β, ?_⟩, Params.aleph0_lt_mk_κ.trans_le Params.κ_le_μ_ord_cof⟩
  exact mk_extendedIndex_lt_cof_μ β

theorem mk_specCondition (h : ∀ (δ : Λ) [LeLevel δ], δ < β → #(CodingFunction δ) < #μ) :
    #(SpecCondition β) < #μ := by
  refine (mk_le_of_injective SpecCondition.toPrime_injective).trans_lt ?_
  rw [SpecCondition']
  simp only [mk_sum, mk_prod, lift_id, mk_set, mk_pi, prod_const, mk_sigma]
  have := Params.μ_isStrongLimit.isLimit.aleph0_le
  have mk_pow_κ := Params.μ_isStrongLimit.2 _ Params.κ_lt_μ
  refine add_lt_of_lt this ?_ (add_lt_of_lt this ?_ (add_lt_of_lt this ?_ ?_))
  · exact mul_lt_of_lt this (mk_extendedIndex_lt_μ β) (mul_lt_of_lt this mk_pow_κ mk_pow_κ)
  · refine mul_lt_of_lt this (mk_extendedIndex_lt_μ β) (mul_lt_of_lt this mk_pow_κ ?_)
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
      exact pow_le_of_isStrongLimit Params.μ_isStrongLimit (mk_inflexibleCoePath_lt A)
    · simp only [prod_const, lift_id]
      exact pow_le_of_isStrongLimit Params.μ_isStrongLimit (mk_extendedIndex_lt_cof_μ β)
  · refine (sum_lt_prod
        (fun (A : ExtendedIndex β) =>
          #(InflexibleBotPath A) * ((2 ^ #κ) * (2 ^ #κ) ^ #κ))
        (fun _ => #μ) ?_).trans_le ?_
    intro A
    · refine mul_lt_of_lt this ?_ (mul_lt_of_lt this mk_pow_κ ?_)
      · exact (mk_inflexibleBotPath_lt A).trans_le (Ordinal.cof_ord_le #μ)
      · rw [← Cardinal.power_mul, mul_eq_self Params.κ_isRegular.aleph0_le]
        exact mk_pow_κ
    · simp only [prod_const, lift_id]
      exact pow_le_of_isStrongLimit Params.μ_isStrongLimit (mk_extendedIndex_lt_cof_μ β)

theorem mk_spec (h : ∀ (δ : Λ) [LeLevel δ], δ < β → #(CodingFunction δ) < #μ) :
    #(Spec β) < #μ :=
  mk_enumeration_lt (mk_specCondition h)

end ConNF
