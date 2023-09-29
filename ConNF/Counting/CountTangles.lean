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
      #{ σ : Spec β // σ.Strong } := by
  refine ⟨fun o => ⟨o.down.val.spec o.down.prop,
    o.down.prop.out, o.down.prop.out_strong, o.down.val.spec_specifies_out _⟩, ?_⟩
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
    (ExtendedIndex β × (δ : { δ : Iic α // δ < β }) × { χ : CodingFunction δ.val // χ.Strong }) ⊕
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

instance {α : Type _} {x : α} : IsTrichotomous ({x} : Set α) emptyRelation := by
  constructor
  rintro ⟨_, rfl⟩ ⟨_, rfl⟩
  exact Or.inr (Or.inl rfl)

instance {α : Type _} {x : α} : IsTrans ({x} : Set α) emptyRelation := by
  constructor
  rintro ⟨_, rfl⟩ ⟨_, rfl⟩ _ h _
  cases h

instance {α : Type _} {x : α} : IsWellFounded ({x} : Set α) emptyRelation := emptyWf.isWellFounded

instance {α : Type _} {x : α} : IsWellOrder ({x} : Set α) emptyRelation := ⟨⟩

def OrdSupport.litter (β : Iic α) (L : Litter) : OrdSupport β where
  carrier := {⟨Quiver.Hom.toPath (WithBot.bot_lt_coe β.val), Sum.inr L.toNearLitter⟩}
  carrier_small := small_singleton _
  r := emptyRelation
  r_isWellOrder := inferInstance

theorem OrdSupport.litter_supports (β : Iic α) (L : Litter) :
    Supports (Allowable β) (OrdSupport.litter β L).carrier
      (typedNearLitter (Litter.toNearLitter L) : Tangle β) := by
  intro ρ h
  have := h rfl
  simp only [Allowable.smul_supportCondition_eq_iff, Sum.smul_inr, Sum.inr.injEq] at this
  rw [Allowable.smul_typedNearLitter, this]

theorem OrdSupport.litter_strong (β : Iic α) (L : Litter)
    (hL : Flexible α (Quiver.Hom.toPath (WithBot.bot_lt_coe β.val)) L) :
    (OrdSupport.litter β L).Strong := by
  constructor
  · rintro ⟨_, rfl⟩
    exact Reduced.mkLitter _
  · rintro c ⟨_, rfl⟩ _ hcd
    cases not_transConstrains_flexible α c hL hcd
  · rintro c ⟨_, rfl⟩ hcd
    cases not_transConstrains_flexible α c hL hcd

noncomputable def CodingFunction.codeLitter (β : Iic α) (L : Litter) : CodingFunction β :=
  CodingFunction.code
    (OrdSupport.litter β L)
    (typedNearLitter L.toNearLitter)
    (OrdSupport.litter_supports β L)

theorem CodingFunction.codeLitter_strong (β : Iic α) (L : Litter)
    (hL : Flexible α (Quiver.Hom.toPath (WithBot.bot_lt_coe β.val)) L) :
    (CodingFunction.codeLitter β L).Strong :=
  CodingFunction.code_strong (OrdSupport.litter_strong β L hL)

theorem mk_codingFunction_ne_zero (β : Iic α) :
    #{ χ : CodingFunction β // χ.Strong } ≠ 0 := by
  have := (aleph0_pos.trans_le μ_isStrongLimit.isLimit.aleph0_le).ne.symm
  rw [← mk_flexible α (Quiver.Hom.toPath (WithBot.bot_lt_coe β.val))] at this
  rw [mk_ne_zero_iff] at this ⊢
  obtain ⟨L, hL⟩ := this
  exact ⟨CodingFunction.codeLitter β L, CodingFunction.codeLitter_strong β L hL⟩

theorem sum_mk_codingFunction_ne_zero (β : Iic α) (hβ : ¬IsMin β) :
    (sum fun δ : { δ : Iic α // δ < β } =>
      lift.{u + 1} #{ χ : CodingFunction δ.val // χ.Strong }) ≠ 0 := by
  rw [not_isMin_iff] at hβ
  obtain ⟨δ, hδ⟩ := hβ
  intro h
  rw [← lift_sum, lift_eq_zero, ← mk_sigma, mk_eq_zero_iff] at h
  refine h.false ⟨⟨δ, hδ⟩, ?_⟩
  have := mk_codingFunction_ne_zero δ
  rw [mk_ne_zero_iff] at this
  exact this.some

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

theorem mk_specConditionBelow (β : Iic α) (hβ : ¬IsMin β)
    (i : Ordinal.{u}) (hi : i.card ≤ #κ) :
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

theorem orderType_lt_of_specifies (σ : Spec β) (S : OrdSupport β) (hσS : σ.Specifies S) :
    σ.orderType.card < #κ := by
  rw [Spec.orderType_eq_of_specifies hσS]
  exact S.small

-- TODO: Could rewrite `SpecSame` making much bigger use of `specifies_subsingleton`.

def SpecType (β : Iic α) : Type _ :=
  (i : Iio (#κ).ord) × (Iio i.val → SpecConditionBelow β i)

theorem specCondition_atom_below {β : Iic α}
    {σ : { σ : Spec β // σ.Strong }}
    {i j : Ordinal} {hi : i < σ.val.orderType} {A : ExtendedIndex β}
    (h : SpecCondition.atom A j = σ.val.cond i hi) :
    j < σ.val.orderType := by
  obtain ⟨σ, S, hS, hσS⟩ := σ
  cases Spec.specifies_subsingleton S hσS (Spec.spec_specifies hS)
  simp only [Spec.spec_cond_eq, Spec.specCondition] at h
  set c := S.conditionAt i hi
  obtain ⟨⟨B, a | N⟩, hc⟩ := c
  · simp only [OrdSupport.coe_sort_coe, SpecCondition.atom.injEq] at h
    cases h.1
    cases h.2
    exact Ordinal.typein_lt_type S.r _
  · dsimp only at h
    split_ifs at h

theorem specCondition_inflexibleBot_below {β : Iic α}
    {σ : { σ : Spec β // σ.Strong }}
    {i j : Ordinal} {hi : i < σ.val.orderType} {A : ExtendedIndex β} {h : InflexibleBotPath A}
    (h : SpecCondition.inflexibleBot A h j = σ.val.cond i hi) :
    j < σ.val.orderType := by
  obtain ⟨σ, S, hS, hσS⟩ := σ
  cases Spec.specifies_subsingleton S hσS (Spec.spec_specifies hS)
  simp only [Spec.spec_cond_eq, Spec.specCondition] at h
  set c := S.conditionAt i hi
  obtain ⟨⟨B, a | N⟩, hc⟩ := c
  · simp only at h
  · dsimp only at h
    split_ifs at h
    simp only [OrdSupport.coe_sort_coe, SpecCondition.inflexibleBot.injEq] at h
    cases h.2.2
    exact Ordinal.typein_lt_type S.r _

noncomputable def specCondition_map (β : Iic α) (σ : { σ : Spec β // σ.Strong })
    (i : Iio σ.val.orderType) : SpecConditionBelow β (σ.val.orderType) :=
  (σ.val.cond i i.prop).rec
  (motive := fun c => c = σ.val.cond i i.prop → SpecConditionBelow β (σ.val.orderType))
  (fun A j hc => .atom A j (specCondition_atom_below hc))
  (fun A _ => .flexible A)
  (fun A h χ hχ _ => .inflexibleCoe A h χ hχ)
  (fun A h j hc => .inflexibleBot A h j (specCondition_inflexibleBot_below hc))
  rfl

theorem specCondition_map_mk_congr {β : Iic α} {o : Ordinal}
    {cond : (i : Ordinal) → i < o → SpecCondition β} {h : Spec.Strong ⟨o, cond⟩}
    {i : Ordinal} {hi : i < o} {d : SpecCondition β} (hd : d = cond i hi) :
    specCondition_map β ⟨⟨o, cond⟩, h⟩ ⟨i, hi⟩ =
    d.rec
    (motive := fun c => c = cond i hi → SpecConditionBelow β o)
    (fun A j hc => .atom A j (specCondition_atom_below (σ := ⟨⟨o, cond⟩, h⟩) hc))
    (fun A _ => .flexible A)
    (fun A h χ hχ _ => .inflexibleCoe A h χ hχ)
    (fun A h' j hc => .inflexibleBot A h' j
      (specCondition_inflexibleBot_below (σ := ⟨⟨o, cond⟩, h⟩) hc))
    hd := by
  subst hd
  rfl

noncomputable def specType_map (β : Iic α) (σ : { σ : Spec β // σ.Strong }) :
    SpecType β :=
  ⟨⟨σ.val.orderType,
    lt_ord.mpr (orderType_lt_of_specifies σ.val σ.prop.choose σ.prop.choose_spec.2)⟩,
    specCondition_map β σ⟩

theorem specType_map_injective (β : Iic α) : Injective (specType_map β) := by
  rintro ⟨⟨o₁, c₁⟩, S₁, hS₁, hσS₁⟩ ⟨⟨σ₂, c₂⟩, S₂, hS₂, hσS₂⟩ h
  rw [specType_map, specType_map, Sigma.ext_iff] at h
  cases h.1
  simp only [heq_eq_eq, true_and] at h
  simp only [Subtype.mk.injEq, Spec.mk.injEq, heq_eq_eq, true_and]
  funext i hi
  have := congr_fun h ⟨i, hi⟩
  set d₁ := c₁ i hi with hd₁
  set d₂ := c₂ i hi with hd₂
  revert hd₁ hd₂
  cases d₁ with
  | atom =>
    cases d₂ <;>
      intros hd₁ hd₂ <;>
      rw [specCondition_map_mk_congr hd₁, specCondition_map_mk_congr hd₂] at this <;>
      aesop
  | flexible =>
    cases d₂ <;>
      intros hd₁ hd₂ <;>
      rw [specCondition_map_mk_congr hd₁, specCondition_map_mk_congr hd₂] at this <;>
      aesop
  | inflexibleCoe =>
    cases d₂ with
    | inflexibleCoe =>
      intros hd₁ hd₂
      rw [specCondition_map_mk_congr hd₁, specCondition_map_mk_congr hd₂,
        SpecConditionBelow.inflexibleCoe.injEq] at this
      cases this.1
      cases eq_of_heq this.2.1
      cases eq_of_heq this.2.2
      rfl
    | _ =>
      intros hd₁ hd₂
      rw [specCondition_map_mk_congr hd₁, specCondition_map_mk_congr hd₂] at this
      aesop
  | inflexibleBot =>
    cases d₂ with
    | inflexibleBot =>
      intros hd₁ hd₂
      rw [specCondition_map_mk_congr hd₁, specCondition_map_mk_congr hd₂,
        SpecConditionBelow.inflexibleBot.injEq] at this
      cases this.1
      cases eq_of_heq this.2.1
      cases this.2.2
      rfl
    | _ =>
      intros hd₁ hd₂
      rw [specCondition_map_mk_congr hd₁, specCondition_map_mk_congr hd₂] at this
      aesop

theorem Cardinal.power_le_power_left {a b c : Cardinal} : a ≠ 0 → b ≤ c → a ^ b ≤ a ^ c := by
  refine Cardinal.inductionOn₃ a b c ?_
  rintro α β γ hα ⟨f⟩
  by_cases hβ : Nonempty β
  · rw [power_def, power_def]
    refine ⟨fun g x => g (Function.invFun f x), ?_⟩
    intro g₁ g₂ h
    funext x
    have h₁ := congr_fun h (f x)
    have h₂ := congr_fun (Function.invFun_comp f.injective) x
    dsimp only [comp_apply] at h₁ h₂
    rw [h₂] at h₁
    exact h₁
  rw [mk_ne_zero_iff] at hα
  rw [not_nonempty_iff] at hβ
  rw [power_def, power_def]
  refine ⟨fun _ _ => hα.some, ?_⟩
  intro g₁ g₂ _
  funext x
  exact hβ.elim x

theorem mk_spec_le (β : Iic α) (hβ : ¬IsMin β) :
    #{ σ : Spec β // σ.Strong } ≤
    lift.{u + 1} (#κ * (2 ^ #κ * (sum fun δ : { δ : Iic α // δ < β } =>
        #{ χ : CodingFunction δ.val // χ.Strong }) ^ #κ)) := by
  refine (mk_le_of_injective (specType_map_injective β)).trans ?_
  rw [SpecType]
  simp only [mk_sigma, mk_pi, prod_const, mk_iio, lift_id]
  suffices : ∀ i : (Iio (#κ).ord),
      #(SpecConditionBelow β i.val) ^ lift.{u + 1} i.val.card ≤
      lift.{u + 1} (2 ^ #κ * (sum fun δ : { δ : Iic α // δ < β } =>
        #{ χ : CodingFunction δ.val // χ.Strong }) ^ #κ)
  · refine (sum_le_sum _ _ this).trans ?_
    simp only [sum_const, mk_iio, card_ord, lift_id, lift_mul]
    rfl
  rintro ⟨i, hi⟩
  have := mk_specConditionBelow β hβ i (lt_ord.mp hi).le
  refine (power_le_power_right (c := lift.{u + 1} i.card) this).trans ?_
  rw [← lift_power, lift_le, mul_power]
  refine mul_le_mul' ?_ ?_
  · rw [← power_self_eq κ_isRegular.aleph0_le]
    exact power_le_power_left κ_isRegular.pos.ne.symm (lt_ord.mp hi).le
  · refine power_le_power_left ?_ (lt_ord.mp hi).le
    have := sum_mk_codingFunction_ne_zero β hβ
    rw [← lift_sum, ne_eq, lift_eq_zero] at this
    exact this

end ConNF
