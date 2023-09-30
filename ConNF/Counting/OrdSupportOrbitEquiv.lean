import ConNF.Counting.OrdSupportOrbit
import ConNF.Counting.SpecSame

open Set
open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}

noncomputable def InflexibleCoe.smul {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleCoe A L) (ρ : Allowable β) :
    InflexibleCoe A (Allowable.toStructPerm ρ A • L) where
  path := h.path
  t := Allowable.comp (show Quiver.Path ((β : IicBot α) : TypeIndex) (h.path.δ : IicBot α) from
    h.path.B.cons (WithBot.coe_lt_coe.mpr h.path.hδ)) ρ • h.t
  hL := by
    have := toStructPerm_smul_fuzz (β : IicBot α) h.path.γ h.path.δ h.path.ε ?_ ?_ ?_
      h.path.B ρ h.t
    rw [← this, ← h.path.hA, ← h.hL]
    · intro hδε
      simp only [Subtype.mk.injEq, WithBot.coe_inj] at hδε
      exact h.path.hδε (Subtype.coe_injective hδε)
    · exact WithBot.coe_lt_coe.mpr h.path.hε
    · exact WithBot.coe_lt_coe.mpr h.path.hδ

@[simp]
theorem InflexibleCoe.smul_path {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleCoe A L) (ρ : Allowable β) :
    (h.smul ρ).path = h.path :=
  rfl

@[simp]
theorem InflexibleCoe.smul_t {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleCoe A L) (ρ : Allowable β) :
    (h.smul ρ).t =
    Allowable.comp (show Quiver.Path ((β : IicBot α) : TypeIndex) (h.path.δ : IicBot α) from
      h.path.B.cons (WithBot.coe_lt_coe.mpr h.path.hδ)) ρ • h.t :=
  rfl

noncomputable def InflexibleBot.smul {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleBot A L) (ρ : Allowable β) :
    InflexibleBot A (Allowable.toStructPerm ρ A • L) where
  path := h.path
  a := Allowable.toStructPerm ρ (h.path.B.cons (WithBot.bot_lt_coe _)) • h.a
  hL := by
    have := toStructPerm_smul_fuzz (β : IicBot α) h.path.γ ⊥ h.path.ε ?_ ?_ ?_
      h.path.B ρ h.a
    rw [Allowable.comp_bot (β := (β : IicBot α))] at this
    rw [← this, ← h.path.hA, ← h.hL]
    · intro hδε
      simp only [IioBot.bot_ne_mk_coe] at hδε
    · exact WithBot.coe_lt_coe.mpr h.path.hε
    · exact WithBot.bot_lt_coe _

@[simp]
theorem InflexibleBot.smul_path {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleBot A L) (ρ : Allowable β) :
    (h.smul ρ).path = h.path :=
  rfl

@[simp]
theorem InflexibleBot.smul_a {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleBot A L) (ρ : Allowable β) :
    (h.smul ρ).a = Allowable.toStructPerm ρ (h.path.B.cons (WithBot.bot_lt_coe _)) • h.a :=
  rfl

theorem Flexible.smul {A : ExtendedIndex β} {L : Litter}
    (h : Flexible α A L) (ρ : Allowable β) :
    Flexible α A (Allowable.toStructPerm ρ A • L) := by
  obtain (hL | ⟨⟨hL⟩⟩ | ⟨⟨hL⟩⟩) := flexible_cases' β A (Allowable.toStructPerm ρ A • L)
  · exact hL
  · have := hL.smul ρ⁻¹
    simp only [map_inv, Tree.inv_apply, inv_smul_smul] at this
    cases h (inflexible_of_inflexibleBot this)
  · have := hL.smul ρ⁻¹
    simp only [map_inv, Tree.inv_apply, inv_smul_smul] at this
    cases h (inflexible_of_inflexibleCoe this)

def Spec.specifies_smul (σ : Spec β) (S : OrdSupport β) (hσS : Specifies σ S) (ρ : Allowable β) :
    σ.Specifies (ρ • S) := by
  constructor
  case lt_orderType =>
    intro c
    rw [OrdSupport.typein_smul]
    exact hσS.lt_orderType _
  case of_lt_orderType =>
    intro i hi
    obtain ⟨c, hc⟩ := hσS.of_lt_orderType i hi
    refine ⟨⟨ρ • c.val, OrdSupport.smul_mem_smul.mpr c.prop⟩, ?_⟩
    simp only [OrdSupport.coe_sort_coe, OrdSupport.typein_smul, inv_smul_smul, Subtype.coe_eta]
    exact hc
  case atom_dom =>
    intro A a h
    simp only [OrdSupport.smul_mem, Allowable.smul_supportCondition, map_inv, Tree.inv_apply,
      Sum.smul_inl] at h
    obtain ⟨N, hN₁, hN₂⟩ := hσS.atom_dom A ((Allowable.toStructPerm ρ A)⁻¹ • a) h
    refine ⟨Allowable.toStructPerm ρ A • N, hN₁, ?_⟩
    have := (OrdSupport.smul_mem_smul (ρ := ρ)).mpr hN₂
    simp only [Allowable.smul_supportCondition, Sum.smul_inr] at this
    exact this
  case atom_spec =>
    intro A a N ha hN haN
    simp only [OrdSupport.coe_sort_coe, OrdSupport.typein_smul]
    simp only [OrdSupport.coe_sort_coe, Allowable.smul_supportCondition, map_inv, Tree.inv_apply,
      Sum.smul_inl, Sum.smul_inr]
    refine hσS.atom_spec A ((Allowable.toStructPerm ρ A)⁻¹ • a)
      ((Allowable.toStructPerm ρ A)⁻¹ • N) _ _ ?_
    change (Allowable.toStructPerm ρ A) • (Allowable.toStructPerm ρ A)⁻¹ • a ∈ N
    rw [smul_inv_smul]
    exact haN
  case flexible_spec =>
    intro A N hNS hN
    simp only [OrdSupport.coe_sort_coe, OrdSupport.typein_smul]
    exact hσS.flexible_spec A (Allowable.toStructPerm ρ⁻¹ A • N) hNS (hN.smul ρ⁻¹)
  case inflexibleCoe_spec =>
    rintro A N hNS hN
    obtain ⟨χ, hχ₁, hχ₂, h₁, h₂⟩ := hσS.inflexibleCoe_spec A
      (Allowable.toStructPerm ρ⁻¹ A • N) hNS (hN.smul ρ⁻¹)
    refine ⟨χ, hχ₁, ?_, ?_, ?_⟩
    · simp only [OrdSupport.coe_sort_coe, OrdSupport.typein_smul, OrdSupport.before_smul,
        OrdSupport.comp_smul]
      exact χ.smul_mem _ hχ₂
    · simp only [OrdSupport.coe_sort_coe, OrdSupport.typein_smul, OrdSupport.before_smul,
        OrdSupport.comp_smul]
      simp only [NearLitterPerm.smul_nearLitter_fst, InflexibleCoe.smul_path,
        OrdSupport.coe_sort_coe, map_inv, Tree.inv_apply, InflexibleCoe.smul_t] at h₁
      rw [eq_inv_smul_iff] at h₁
      rw [χ.decode_smul, ← h₁]
      simp only [NearLitterPerm.smul_nearLitter_fst, InflexibleCoe.smul_path,
        OrdSupport.coe_sort_coe, Allowable.smul_supportCondition, map_inv, Tree.inv_apply,
        Sum.smul_inr]
    · simp only [OrdSupport.coe_sort_coe, OrdSupport.typein_smul, Allowable.smul_supportCondition,
        map_inv, Tree.inv_apply, Sum.smul_inr]
      simp only [OrdSupport.coe_sort_coe, map_inv, Tree.inv_apply, NearLitterPerm.smul_nearLitter_fst,
        InflexibleCoe.smul_path] at h₂
      exact h₂
  case inflexibleBot_spec =>
    intro A N hNS hN
    obtain ⟨h₁, h₂⟩ := hσS.inflexibleBot_spec A (Allowable.toStructPerm ρ⁻¹ A • N) hNS (hN.smul ρ⁻¹)
    refine ⟨h₁, ?_⟩
    simp only [OrdSupport.coe_sort_coe, OrdSupport.typein_smul, Allowable.smul_supportCondition,
      map_inv, Tree.inv_apply, Sum.smul_inr, Sum.smul_inl]
    simp only [OrdSupport.coe_sort_coe, map_inv, Tree.inv_apply, NearLitterPerm.smul_nearLitter_fst,
      InflexibleBot.smul_path, InflexibleBot.smul_a] at h₂
    exact h₂

/-- There is an equivalence between strong ordered support orbits and strong specifications. -/
noncomputable def specEquiv (β : Iic α) :
    { o : OrdSupportOrbit β // o.Strong } ≃ { σ : Spec β // σ.Strong } where
  toFun o := ⟨Spec.spec o.prop.out o.prop.out_strong,
    o.prop.out, o.prop.out_strong, Spec.spec_specifies _⟩
  invFun σ := ⟨OrdSupportOrbit.mk σ.prop.out, σ.prop.out, rfl, σ.prop.out_strong⟩
  left_inv := by
    intro o
    refine Subtype.coe_injective ?_
    dsimp only
    conv_rhs => rw [← o.prop.mk_out]
    rw [OrdSupportOrbit.eq]
    have h₁ := Spec.spec_specifies o.prop.out_strong
    have h₂ := Spec.Strong.specifies_out (σ := Spec.spec o.prop.out o.prop.out_strong)
      ⟨o.prop.out, o.prop.out_strong, Spec.spec_specifies _⟩
    exact ⟨_, Spec.convertAllowable_smul h₁ h₂ o.prop.out_strong (Spec.Strong.out_strong _)⟩
  right_inv := by
    intro σ
    refine Subtype.coe_injective ?_
    have := OrdSupportOrbit.Strong.mk_out ⟨σ.prop.out, rfl, σ.prop.out_strong⟩
    rw [OrdSupportOrbit.eq] at this
    obtain ⟨ρ, h⟩ := this
    simp_rw [← h]
    have h₁ := σ.prop.specifies_out
    have := Spec.specifies_smul σ.val _ h₁ ρ
    exact Spec.specifies_subsingleton _ (Spec.spec_specifies _) this

noncomputable def mk_ordSupportOrbit (β : Iic α) :
    Cardinal.lift.{u + 1} #{ o : OrdSupportOrbit β // o.Strong } = #{ σ : Spec β // σ.Strong } := by
  rw [Cardinal.lift_mk_eq'.mpr ⟨specEquiv β⟩]
  exact Cardinal.lift_id'.{u, u + 1} _

end ConNF
