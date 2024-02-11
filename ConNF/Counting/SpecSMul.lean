import ConNF.Counting.Spec

/-!
# Supports in the same orbit
-/

open Quiver Set Sum WithBot

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ} [i : LeLevel β] {σ : Spec β} {S : Support β}
    {lS : ∀ {γ : Λ}, (hγ : (γ : TypeIndex) < β) → (A : Path (β : TypeIndex) γ) → Support γ}

theorem specifiesCondition_atom_smul
    {σc : SpecComponent β} {A : ExtendedIndex β} {a : Atom}
    (h : SpecifiesC σ S lS σc ⟨A, inl a⟩) (ρ : Allowable β) :
    SpecifiesC σ (ρ • S) (fun hγ A => (Allowable.toStructPerm ρ).comp A • lS hγ A)
      σc ⟨A, inl (Allowable.toStructPerm ρ A • a)⟩ := by
  rw [specifiesC_atom_right_iff] at h
  rw [specifiesC_atom_right_iff, h, SpecComponent.atom.injEq]
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
      simp only [Allowable.smul_address, map_inv, Tree.inv_apply, smul_inl, inv_smul_smul]
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
      simp only [Allowable.smul_address, map_inv, Tree.inv_apply, smul_inr]

theorem specifiesCondition_flexible_smul {S : Support β}
    {σc : SpecComponent β} {A : ExtendedIndex β} {N : NearLitter} (hN : Flexible A N.1)
    (h : SpecifiesC σ S lS σc ⟨A, inr N⟩) (ρ : Allowable β) :
    SpecifiesC σ (ρ • S) (fun hγ A => (Allowable.toStructPerm ρ).comp A • lS hγ A) σc
      ⟨A, inr (Allowable.toStructPerm ρ A • N)⟩ := by
  rw [specifiesC_flexible_right_iff _ _ _ hN] at h
  rw [specifiesC_flexible_right_iff _ _ _ (by exact hN.smul ρ), h]
  refine congr_arg _ ?_
  ext i
  constructor
  · rintro ⟨hi, N', hS, hN'⟩
    refine ⟨hi, Allowable.toStructPerm ρ A • N', ?_, ?_⟩
    · rw [Allowable.smul_support_f, hS]
      rfl
    · rw [NearLitterPerm.smul_nearLitter_fst, hN']
      rfl
  · rintro ⟨hi, N', hS, hN'⟩
    refine ⟨hi, (Allowable.toStructPerm ρ A)⁻¹ • N', ?_, ?_⟩
    · rw [Allowable.smul_support_f, smul_eq_iff_eq_inv_smul] at hS
      rw [hS, Allowable.smul_address]
      simp only [map_inv, Tree.inv_apply, smul_inr]
    · rw [NearLitterPerm.smul_nearLitter_fst, hN',
        NearLitterPerm.smul_nearLitter_fst, inv_smul_smul]

theorem specifiesCondition_inflexibleCoe_smul {S : Support β}
    {σc : SpecComponent β} {A : ExtendedIndex β} {N : NearLitter} (hN : InflexibleCoe A N.1)
    (h : SpecifiesC σ S lS σc ⟨A, inr N⟩) (ρ : Allowable β) :
    SpecifiesC σ (ρ • S) (fun hγ A => (Allowable.toStructPerm ρ).comp A • lS hγ A) σc
      ⟨A, inr (Allowable.toStructPerm ρ A • N)⟩ := by
  rw [specifiesC_inflexibleCoe_right_iff _ _ _ hN] at h
  rw [specifiesC_inflexibleCoe_right_iff _ _ _ (by exact hN.smul ρ)]
  obtain ⟨r, hr, hS, rfl⟩ := h
  refine ⟨r, ?_, ?_, ?_⟩
  · intro i hi
    simp only [NearLitterPerm.smul_nearLitter_fst, inflexibleCoe_smul_path, inflexibleCoe_smul_t,
      smul_support, Allowable.smul_support_max] at hi
    exact hr i hi
  · intro i hi
    simp only [NearLitterPerm.smul_nearLitter_fst, inflexibleCoe_smul_path, inflexibleCoe_smul_t,
      smul_support, Allowable.smul_support_max, Support.smul_f] at hi ⊢
    rw [← hS i hi]
    simp only [NearLitterPerm.smul_nearLitter_fst, inflexibleCoe_smul_path,
      Allowable.toStructPerm_smul, Allowable.toStructPerm_comp, Support.smul_f]
  · refine congr_arg₂ _ ?_ rfl
    simp only [NearLitterPerm.smul_nearLitter_fst, inflexibleCoe_smul_path, inflexibleCoe_smul_t,
      smul_support]
    exact (CodingFunction.code_smul _ _ _ _ _).symm

theorem specifiesCondition_inflexibleBot_smul {S : Support β}
    {σc : SpecComponent β} {A : ExtendedIndex β} {N : NearLitter} (hN : InflexibleBot A N.1)
    (h : SpecifiesC σ S lS σc ⟨A, inr N⟩) (ρ : Allowable β) :
    SpecifiesC σ (ρ • S) (fun hγ A => (Allowable.toStructPerm ρ).comp A • lS hγ A) σc
      ⟨A, inr (Allowable.toStructPerm ρ A • N)⟩ := by
  rw [specifiesC_inflexibleBot_right_iff _ _ _ hN] at h
  rw [specifiesC_inflexibleBot_right_iff _ _ _ (by exact hN.smul ρ),
    h, SpecComponent.inflexibleBot.injEq]
  refine ⟨rfl, HEq.rfl, ?_⟩
  ext i
  constructor
  · rintro ⟨hi₁, hi₂⟩
    refine ⟨hi₁, ?_⟩
    rw [Allowable.smul_support_f, hi₂]
    simp only [Allowable.smul_address, smul_inl, NearLitterPerm.smul_nearLitter_fst,
      inflexibleBot_smul_path, inflexibleBot_smul_a, ofBot_smul, Allowable.toStructPerm_apply]
  · rintro ⟨hi₁, hi₂⟩
    refine ⟨hi₁, ?_⟩
    rw [Allowable.smul_support_f, smul_eq_iff_eq_inv_smul] at hi₂
    rw [hi₂]
    simp only [NearLitterPerm.smul_nearLitter_fst, inflexibleBot_smul_path, inflexibleBot_smul_a,
      ofBot_smul, Allowable.toStructPerm_apply, Allowable.smul_address, map_inv,
      Tree.inv_apply, smul_inl, inv_smul_smul]

theorem SpecifiesC.smul {σc : SpecComponent β} {c : Address β}
    (h : SpecifiesC σ S lS σc c) (ρ : Allowable β) :
    SpecifiesC σ (ρ • S) (fun hγ A => (Allowable.toStructPerm ρ).comp A • lS hγ A) σc (ρ • c) := by
  obtain ⟨B, a | N⟩ := c
  · exact specifiesCondition_atom_smul h ρ
  · obtain (h' | ⟨⟨h'⟩⟩ | ⟨⟨h'⟩⟩) := flexible_cases' B N.1
    · exact specifiesCondition_flexible_smul h' h ρ
    · exact specifiesCondition_inflexibleBot_smul h' h ρ
    · exact specifiesCondition_inflexibleCoe_smul h' h ρ

theorem Spec.Specifies.smul {σ : Spec β} {S : Support β} (h : σ.Specifies S) (ρ : Allowable β) :
    σ.Specifies (ρ • S) := by
  have : WellFoundedLT Λ := inferInstance
  revert i σ S
  have := this.induction
    (C := fun β => ∀ (i : LeLevel ↑β) {σ : Spec β} {S : Support ↑β},
      Specifies σ S → ∀ (ρ : Allowable ↑β), Specifies σ (ρ • S))
  refine this β ?_
  intro β ih i σ S h ρ
  obtain ⟨_, _, max_eq_max, lS, hlS₁, hlS₂, hlS₃, cond⟩ := h
  refine ⟨_, _, max_eq_max, fun hγ A => (Allowable.toStructPerm ρ).comp A • lS hγ A,
      hlS₁, ?_, ?_, ?_⟩
  · intro γ hγ A i hi
    simp only [Support.smul_f, Allowable.smul_support_f]
    rw [← hlS₂ hγ A i hi]
    rfl
  · intro γ hγ A
    have : LeLevel γ := ⟨hγ.le.trans i.elim⟩
    have := ih γ (coe_lt_coe.mp hγ) _ (hlS₃ hγ A) (Allowable.comp A ρ)
    rw [Allowable.toStructPerm_smul, Allowable.toStructPerm_comp] at this
    exact this
  · intro i hiσ hiS
    exact (cond i hiσ hiS).smul ρ

end ConNF
