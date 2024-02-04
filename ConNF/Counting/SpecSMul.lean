import ConNF.Counting.Spec

/-!
# Supports in the same orbit
-/

open Quiver Set Sum WithBot

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ} [i : LeLevel β]

theorem specifiesCondition_atom_smul {S : Support β}
    {σc : SpecCondition β} {A : ExtendedIndex β} {a : Atom}
    (h : Spec.SpecifiesCondition S σc ⟨A, inl a⟩) (ρ : Allowable β) :
    Spec.SpecifiesCondition (ρ • S) σc ⟨A, inl (Allowable.toStructPerm ρ A • a)⟩ := by
  rw [Spec.specifiesCondition_atom_right_iff] at h
  rw [Spec.specifiesCondition_atom_right_iff, h, SpecCondition.atom.injEq]
  simp only [Allowable.smul_support_f, Allowable.smul_support_max, true_and]
  constructor
  · ext i
    constructor
    · rintro ⟨hi₁, hi₂⟩
      refine ⟨hi₁, ?_⟩
      rw [hi₂]
      rfl
    · rintro ⟨hi₁, hi₂⟩
      refine ⟨hi₁, ?_⟩
      rw [smul_eq_iff_eq_inv_smul] at hi₂
      rw [hi₂]
      simp only [Allowable.smul_Address, map_inv, Tree.inv_apply, smul_inl, inv_smul_smul]
  · ext i
    constructor
    · rintro ⟨N, ha, hi₁, hi₂⟩
      refine ⟨Allowable.toStructPerm ρ A • N, ?_, hi₁, ?_⟩
      · rw [← SetLike.mem_coe, NearLitterPerm.smul_nearLitter_coe, smul_mem_smul_set_iff]
        exact ha
      · rw [hi₂]
        rfl
    · rintro ⟨N, ha, hi₁, hi₂⟩
      refine ⟨(Allowable.toStructPerm ρ A)⁻¹ • N, ha, hi₁, ?_⟩
      rw [smul_eq_iff_eq_inv_smul] at hi₂
      rw [hi₂]
      simp only [Allowable.smul_Address, map_inv, Tree.inv_apply, smul_inr]

theorem specifiesCondition_flexible_smul {S : Support β}
    {σc : SpecCondition β} {A : ExtendedIndex β} {N : NearLitter} (hN : Flexible A N.1)
    (h : Spec.SpecifiesCondition S σc ⟨A, inr N⟩) (ρ : Allowable β) :
    Spec.SpecifiesCondition (ρ • S) σc ⟨A, inr (Allowable.toStructPerm ρ A • N)⟩ := by
  rw [Spec.specifiesCondition_flexible_right_iff _ _ _ hN] at h
  rw [Spec.specifiesCondition_flexible_right_iff _ _ _ (by exact hN.smul ρ)]
  exact h

theorem specifiesCondition_inflexibleCoe_smul {S : Support β}
    {σc : SpecCondition β} {A : ExtendedIndex β} {N : NearLitter} (hN : InflexibleCoe A N.1)
    (h : Spec.SpecifiesCondition S σc ⟨A, inr N⟩) (ρ : Allowable β)
    (ih : ∀ {σ : Spec hN.path.δ} {S : Support hN.path.δ} (_ : σ.Specifies S)
      (ρ : Allowable hN.path.δ), σ.Specifies (ρ • S)) :
    Spec.SpecifiesCondition (ρ • S) σc ⟨A, inr (Allowable.toStructPerm ρ A • N)⟩ := by
  rw [Spec.specifiesCondition_inflexibleCoe_right_iff _ _ _ hN] at h
  rw [Spec.specifiesCondition_inflexibleCoe_right_iff _ _ _ (by exact hN.smul ρ)]
  obtain ⟨S', hS', σ, hσ, h⟩ := h
  refine ⟨Allowable.comp (hN.path.B.cons hN.path.hδ) ρ • S', ?_, σ, ih hσ _, ?_⟩
  · have := Allowable.support_isSum_smul hS' (Allowable.comp (hN.path.B.cons hN.path.hδ) ρ)
    rw [inflexibleCoe_smul_t, smul_support]
    rw [Allowable.comp_smul_support_comp] at this
    exact this
  · rw [h]
    simp only [NearLitterPerm.smul_nearLitter_fst, inflexibleCoe_smul_path, inflexibleCoe_smul_t,
      smul_support, SpecCondition.inflexibleCoe.injEq, heq_eq_eq, and_true, true_and]
    rw [CodingFunction.code_smul]

theorem specifiesCondition_inflexibleBot_smul {S : Support β}
    {σc : SpecCondition β} {A : ExtendedIndex β} {N : NearLitter} (hN : InflexibleBot A N.1)
    (h : Spec.SpecifiesCondition S σc ⟨A, inr N⟩) (ρ : Allowable β) :
    Spec.SpecifiesCondition (ρ • S) σc ⟨A, inr (Allowable.toStructPerm ρ A • N)⟩ := by
  rw [Spec.specifiesCondition_inflexibleBot_right_iff _ _ _ hN] at h
  rw [Spec.specifiesCondition_inflexibleBot_right_iff _ _ _ (by exact hN.smul ρ),
    h, SpecCondition.inflexibleBot.injEq]
  refine ⟨rfl, HEq.rfl, ?_⟩
  ext i
  constructor
  · rintro ⟨hi₁, hi₂⟩
    refine ⟨hi₁, ?_⟩
    rw [Allowable.smul_support_f, hi₂]
    simp only [Allowable.smul_Address, smul_inl, NearLitterPerm.smul_nearLitter_fst,
      inflexibleBot_smul_path, inflexibleBot_smul_a, ofBot_smul, Allowable.toStructPerm_apply]
  · rintro ⟨hi₁, hi₂⟩
    refine ⟨hi₁, ?_⟩
    rw [Allowable.smul_support_f, smul_eq_iff_eq_inv_smul] at hi₂
    rw [hi₂]
    simp only [NearLitterPerm.smul_nearLitter_fst, inflexibleBot_smul_path, inflexibleBot_smul_a,
      ofBot_smul, Allowable.toStructPerm_apply, Allowable.smul_Address, map_inv,
      Tree.inv_apply, smul_inl, inv_smul_smul]

theorem Spec.SpecifiesCondition.smul {S : Support β}
    {σc : SpecCondition β} {c : Address β}
    (h : Spec.SpecifiesCondition S σc c) (ρ : Allowable β) :
    Spec.SpecifiesCondition (ρ • S) σc (ρ • c) := by
  have : WellFoundedLT Λ := inferInstance
  revert i S σc c
  have := this.induction
    (C := fun β => (i : LeLevel β) → ∀ S : Support β, ∀ σc : SpecCondition β,
      ∀ c : Address β, ∀ _ : Spec.SpecifiesCondition S σc c, ∀ ρ : Allowable β,
      Spec.SpecifiesCondition (ρ • S) σc (ρ • c))
  refine this β ?_
  intro β ih _ S σc c h ρ
  obtain ⟨B, a | N⟩ := c
  · exact specifiesCondition_atom_smul h ρ
  · obtain (h' | ⟨⟨h'⟩⟩ | ⟨⟨h'⟩⟩) := flexible_cases' B N.1
    · exact specifiesCondition_flexible_smul h' h ρ
    · exact specifiesCondition_inflexibleBot_smul h' h ρ
    · refine specifiesCondition_inflexibleCoe_smul h' h ρ ?_
      intro σ S hS ρ
      rw [specifies_iff] at hS ⊢
      constructor
      · exact hS.1
      · intro i hiσ hiS
        exact ih h'.path.δ (coe_lt_coe.mp h'.δ_lt_β) inferInstance S _ _ (hS.2 i hiσ hiS) ρ

theorem Spec.Specifies.smul {σ : Spec β} {S : Support β} (h : σ.Specifies S) (ρ : Allowable β) :
    σ.Specifies (ρ • S) := by
  rw [specifies_iff] at h ⊢
  constructor
  · exact h.1
  · intro i hiσ hiS
    exact (h.2 i hiσ hiS).smul ρ

end ConNF
