import ConNF.Counting.Recode
import ConNF.Counting.SpecSame

/-!
# Counting tangles
-/

open Cardinal Function MulAction Set
open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [CountingAssumptions α] {β γ : Iic α} (hγ : γ < β)

noncomputable def recodeSurjection
    (x : { x : Set (RaisedSingleton hγ) × OrdSupportOrbit β //
      x.2.Strong ∧
      ∃ ho : ∀ U ∈ x.2, AppearsRaised hγ (Subtype.val '' x.1) U,
      ∀ U, ∀ hU : U ∈ x.2,
        Supports (Allowable β) {c | c ∈ U} (decodeRaised hγ (Subtype.val '' x.1) U (ho U hU)) }) :
    { χ : CodingFunction β // CodingFunction.Strong χ } :=
  ⟨raisedCodingFunction hγ (Subtype.val '' x.val.1) x.val.2 x.prop.2.1 x.prop.2.2,
    raisedCodingFunction_strong hγ x.prop.1⟩

theorem recodeSurjection_surjective : Surjective (recodeSurjection hγ) := by
  rintro ⟨χ, S, hSχ, hS⟩
  refine ⟨⟨⟨Subtype.val ⁻¹' raiseSingletons hγ S ((χ.decode S).get hSχ), OrdSupportOrbit.mk S⟩,
      ?_, ?_, ?_⟩, ?_⟩
  · exact ⟨S, rfl, hS⟩
  · intro U hU
    rw [image_preimage_eq_of_subset (raiseSingletons_subset_range hγ)]
    exact appearsRaised_of_mem_orbit hγ S ((χ.decode S).get hSχ) (χ.supports_decode S hSχ) U hU
  · intro U hU
    conv in (Subtype.val '' _) => rw [image_preimage_eq_of_subset (raiseSingletons_subset_range hγ)]
    exact supports_decodeRaised_of_mem_orbit hγ S
      ((χ.decode S).get hSχ) (χ.supports_decode S hSχ) U hU
  · rw [recodeSurjection, Subtype.mk.injEq]
    conv in (Subtype.val '' _) => rw [image_preimage_eq_of_subset (raiseSingletons_subset_range hγ)]
    conv_rhs => rw [CodingFunction.eq_code hSχ,
      ← recode_eq hγ S ((χ.decode S).get hSχ) (χ.supports_decode S hSχ)]

theorem mk_strong_codingFunction_le :
    #{ χ : CodingFunction β // χ.Strong } ≤
    2 ^ #(RaisedSingleton hγ) * #{ o : OrdSupportOrbit β // o.Strong } := by
  refine (mk_le_of_surjective (recodeSurjection_surjective hγ)).trans ?_
  refine (mk_subtype_le_of_subset (q := fun x => x.2.Strong) (fun x hx => hx.1)).trans ?_
  have := mk_prod (Set (RaisedSingleton hγ)) { o : OrdSupportOrbit β // o.Strong }
  simp only [mk_set, lift_id] at this
  rw [← this]
  refine ⟨⟨fun x => ⟨x.val.1, x.val.2, x.prop⟩, ?_⟩⟩
  rintro ⟨⟨cs₁, o₁⟩, _⟩ ⟨⟨cs₂, o₂⟩, _⟩ h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  cases h.1
  cases h.2
  rfl

noncomputable def OrdSupportOrbit.spec (o : OrdSupportOrbit β) (h : o.Strong) : Spec β :=
  Spec.spec h.out h.out_strong

theorem OrdSupportOrbit.spec_specifies_out (o : OrdSupportOrbit β) (h : o.Strong) :
    (o.spec h).Specifies h.out :=
  Spec.spec_specifies h.out_strong

theorem OrdSupportOrbit.spec_injective {o₁ o₂ : OrdSupportOrbit β} {h₁ : o₁.Strong} {h₂ : o₂.Strong}
    (h : o₁.spec h₁ = o₂.spec h₂) : o₁ = o₂ := by
  have := Spec.convertAllowable_smul (σ := o₁.spec h₁) ?_ ?_ h₁.out_strong h₂.out_strong
  · exact (OrdSupportOrbit.eq_of_mem_orbit h₂.mk_out h₁.mk_out ⟨_, this⟩).symm
  · exact o₁.spec_specifies_out h₁
  · rw [h]
    exact o₂.spec_specifies_out h₂

theorem mk_ordSupportOrbit_le :
    lift.{u + 1} #{ o : OrdSupportOrbit β // o.Strong } ≤
      #{ σ : Spec β // ∃ S : OrdSupport β, σ.Specifies S } := by
  refine ⟨fun o => ⟨o.down.val.spec o.down.prop,
    o.down.prop.out, o.down.val.spec_specifies_out _⟩, ?_⟩
  intro o₁ o₂ h
  rw [Subtype.mk.injEq] at h
  exact ULift.ext _ _ (Subtype.coe_injective (OrdSupportOrbit.spec_injective h))

inductive SpecConditionBelow (β : Iic α) (i : Ordinal.{u})
  | atom (A : ExtendedIndex β) (j : Ordinal) (h : j < i)
  | flexible (A : ExtendedIndex β)
  | inflexibleCoe (A : ExtendedIndex β) (h : InflexibleCoePath A)
      (χ : CodingFunction (h.δ : Iic α)) (hχ : χ.Strong)
  | inflexibleBot (A : ExtendedIndex β) (h : InflexibleBotPath A) (j : Ordinal) (hj : j < i)

def SpecConditionBelowType (β : Iic α) (i : Ordinal.{u}) :=
    (ExtendedIndex β × Iio i) ⊕ (ExtendedIndex β) ⊕
    (ExtendedIndex β × Σ δ : { δ : Iic α // δ < β }, { χ : CodingFunction δ.val // χ.Strong }) ⊕
    (ExtendedIndex β × Iio i)

def specConditionBelow_map {β : Iic α} {i : Ordinal} :
    SpecConditionBelow β i → SpecConditionBelowType β i
  | .atom A j hj => Sum.inl (A, ⟨j, hj⟩)
  | .flexible A => Sum.inr (Sum.inl A)
  | .inflexibleCoe A h χ hχ => Sum.inr (Sum.inr (Sum.inl
      (A, ⟨⟨h.δ, h.hδ.trans_le (WithBot.coe_le_coe.mp <| le_of_path h.B)⟩, χ, hχ⟩)))
  | .inflexibleBot A _ j hj => Sum.inr (Sum.inr (Sum.inr (A, ⟨j, hj⟩)))

theorem specConditionBelow_map_injective {β : Iic α} {i : Ordinal} :
    Function.Injective (specConditionBelow_map (β := β) (i := i)) := by
  intro c d h
  unfold specConditionBelow_map at h
  cases c with
  | atom A j h =>
    cases d <;> cases h
    rfl
  | flexible A =>
    cases d <;> cases h
    rfl
  | inflexibleCoe A P χ hχ =>
    cases d with
    | inflexibleCoe B Q χ' hχ' =>
      rw [Sum.inr.inj_iff, Sum.inr.inj_iff, Sum.inl.inj_iff] at h
      simp only [Prod.mk.injEq, Sigma.mk.inj_iff, Subtype.mk.injEq] at h
      have := (P.hA).symm.trans (h.1.trans Q.hA)
      obtain ⟨⟨γ, _⟩, ⟨δ, _⟩, ⟨ε, _⟩, _⟩ := P
      obtain ⟨⟨γ', _⟩, ⟨δ', _⟩, ⟨ε', _⟩, _⟩ := Q
      have := Quiver.Path.obj_eq_of_cons_eq_cons this
      rw [WithBot.coe_inj] at this
      subst this
      have := eq_of_heq (Quiver.Path.heq_of_cons_eq_cons this)
      have := Quiver.Path.obj_eq_of_cons_eq_cons this
      rw [WithBot.coe_inj] at this
      subst this
      have := eq_of_heq (Quiver.Path.heq_of_cons_eq_cons this)
      subst this
      cases h.1
      cases h.2.1
      cases h.2.2
      rfl
    | _ => try cases h
  | inflexibleBot A P j hj =>
    cases d with
    | inflexibleBot B Q χ' hχ' =>
      rw [Sum.inr.inj_iff, Sum.inr.inj_iff, Sum.inr.inj_iff] at h
      simp only [Prod.mk.injEq, Sigma.mk.inj_iff, Subtype.mk.injEq] at h
      have := (P.hA).symm.trans (h.1.trans Q.hA)
      obtain ⟨⟨γ, _⟩, ⟨ε, _⟩, _⟩ := P
      obtain ⟨⟨γ', _⟩, ⟨ε', _⟩, _⟩ := Q
      have := Quiver.Path.obj_eq_of_cons_eq_cons this
      rw [WithBot.coe_inj] at this
      subst this
      have := eq_of_heq (Quiver.Path.heq_of_cons_eq_cons this)
      have := Quiver.Path.obj_eq_of_cons_eq_cons this
      rw [WithBot.coe_inj] at this
      subst this
      have := eq_of_heq (Quiver.Path.heq_of_cons_eq_cons this)
      subst this
      cases h.1
      cases h.2
      rfl
    | _ => try cases h

theorem mk_codingFunction_ne_zero (β : Iic α) :
    #{ χ : CodingFunction β // χ.Strong } ≠ 0 := by
  rw [Cardinal.mk_ne_zero_iff]
  sorry

theorem sum_mk_codingFunction_ne_zero (β : Iic α) (hβ : ¬IsMin β) :
    (sum fun δ : { δ : Iic α // δ < β } =>
      lift.{u + 1} #{ χ : CodingFunction δ.val // χ.Strong }) ≠ 0 := by
  rw [not_isMin_iff] at hβ
  obtain ⟨δ, hδ⟩ := hβ
  intro h
  sorry

theorem _root_.Cardinal.mul_le_of_le {a b c : Cardinal} (ha : a ≤ c) (hb : b ≤ c) (hc : ℵ₀ ≤ c) :
    a * b ≤ c := by
  by_cases ha' : ℵ₀ ≤ a
  · refine le_trans (mul_le_max_of_aleph0_le_left ha') ?_
    simp only [ge_iff_le, max_le_iff]
    exact ⟨ha, hb⟩
  by_cases hb' : ℵ₀ ≤ b
  · refine le_trans (mul_le_max_of_aleph0_le_right hb') ?_
    simp only [ge_iff_le, max_le_iff]
    exact ⟨ha, hb⟩
  · simp only [not_le] at ha' hb'
    exact (mul_lt_aleph0 ha' hb').le.trans hc

@[simp]
theorem mk_iio (i : Ordinal.{u}) : #(Iio i) = lift.{u + 1} i.card :=
  Ordinal.mk_initialSeg i

theorem mk_specCondition_below (β : Iic α) (hβ : ¬IsMin β)
    (i : Ordinal.{u}) (hi : Ordinal.card i ≤ #κ) :
    #(SpecConditionBelow β i) ≤
    lift.{u + 1}
      (#κ * sum fun δ : { δ : Iic α // δ < β } => #{ χ : CodingFunction δ.val // χ.Strong }) := by
  have : #(SpecConditionBelow β i) ≤ #(SpecConditionBelowType β i) :=
    ⟨specConditionBelow_map, specConditionBelow_map_injective⟩
  refine le_trans this ?_
  rw [SpecConditionBelowType]
  simp only [mk_sum, mk_prod, lift_id, mk_sigma, lift_mul, lift_sum, lift_lift, lift_add]
  have : ℵ₀ ≤ lift.{u + 1} #κ *
      sum fun δ : { δ : Iic α // δ < β } => lift.{u + 1} #{ χ : CodingFunction δ.val // χ.Strong }
  · rw [aleph0_le_mul_iff]
    simp only [ne_eq, lift_eq_zero, mk_ne_zero, not_false_eq_true, aleph0_le_lift, aleph0_le_mk,
      true_or, and_true, true_and]
    exact sum_mk_codingFunction_ne_zero β hβ
  refine add_le_of_le this ?_ (add_le_of_le this ?_ (add_le_of_le this ?_ ?_))
  · refine le_trans ?_ (le_mul_right (sum_mk_codingFunction_ne_zero β hβ))
    refine mul_le_of_le ?_ ?_ ?_
    · rw [lift_le]
      exact (mk_extendedIndex β).trans Λ_lt_κ.le
    · rw [mk_iio, Ordinal.lift_card, Ordinal.lift_card, Ordinal.lift_lift,
        ← Ordinal.lift_card, lift_le]
      exact hi
    · simp only [aleph0_le_lift, aleph0_le_mk]
  · refine le_trans ?_ (le_mul_right (sum_mk_codingFunction_ne_zero β hβ))
    rw [lift_le]
    exact (mk_extendedIndex β).trans Λ_lt_κ.le
  · refine mul_le_mul' ?_ le_rfl
    rw [lift_le]
    exact (mk_extendedIndex β).trans Λ_lt_κ.le
  · refine le_trans ?_ (le_mul_right (sum_mk_codingFunction_ne_zero β hβ))
    refine mul_le_of_le ?_ ?_ ?_
    · rw [lift_le]
      exact (mk_extendedIndex β).trans Λ_lt_κ.le
    · rw [mk_iio, Ordinal.lift_card, Ordinal.lift_card, Ordinal.lift_lift,
        ← Ordinal.lift_card, lift_le]
      exact hi
    · simp only [aleph0_le_lift, aleph0_le_mk]

end ConNF
