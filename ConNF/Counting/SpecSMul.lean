import ConNF.Counting.Spec

/-!
# Supports in the same orbit
-/

open Quiver Set Sum WithBot

open scoped symmDiff

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ} [LeLevel β]
  {S T : Support β} {hS : S.Strong} {σ : Spec β} (hσS : σ.Specifies S hS) (ρ : Allowable β)

theorem Spec.Specifies.smul : σ.Specifies (ρ • S) (hS.smul ρ) := by
  constructor
  case max_eq_max => exact hσS.max_eq_max
  case atom_spec =>
    intro i hi A a ha
    rw [hσS.atom_spec i hi A ((Allowable.toStructPerm ρ A)⁻¹ • a)]
    swap
    · rw [Enumeration.smul_f, smul_eq_iff_eq_inv_smul] at ha
      rw [ha, Allowable.smul_address, map_inv, Tree.inv_apply, smul_inl]
    simp only [Enumeration.smul_f, Enumeration.smul_max, SpecCondition.atom.injEq]
    refine ⟨trivial, ?_, ?_⟩
    · ext j
      constructor
      · rintro ⟨hj, hjS⟩
        refine ⟨hj, ?_⟩
        rw [hjS, Allowable.smul_address, smul_inl, smul_inv_smul]
      · rintro ⟨hj, hjS⟩
        refine ⟨hj, ?_⟩
        rw [smul_eq_iff_eq_inv_smul] at hjS
        rw [hjS, Allowable.smul_address, smul_inl, map_inv, Tree.inv_apply]
    · ext j
      constructor
      · rintro ⟨hj₁, N, hj₂, hj₃⟩
        refine ⟨hj₁, Allowable.toStructPerm ρ A • N, ?_, ?_⟩
        · rw [hj₂, Allowable.smul_address, smul_inr]
        · rw [← SetLike.mem_coe, NearLitterPerm.smul_nearLitter_coe,
            mem_smul_set_iff_inv_smul_mem]
          exact hj₃
      · rintro ⟨hj₁, N, hj₂, hj₃⟩
        refine ⟨hj₁, (Allowable.toStructPerm ρ A)⁻¹ • N, ?_, ?_⟩
        · rw [smul_eq_iff_eq_inv_smul] at hj₂
          rw [hj₂, Allowable.smul_address, smul_inr, map_inv, Tree.inv_apply]
        · rw [← SetLike.mem_coe, NearLitterPerm.smul_nearLitter_coe,
            mem_smul_set_iff_inv_smul_mem, inv_inv, smul_inv_smul, SetLike.mem_coe]
          exact hj₃
  case flexible_spec =>
    intro i hi A N hN h
    rw [hσS.flexible_spec i hi A ((Allowable.toStructPerm ρ A)⁻¹ • N)]
    swap
    · have := hN.smul ρ⁻¹
      simp only [map_inv, Tree.inv_apply] at this
      exact this
    swap
    · rw [Enumeration.smul_f, smul_eq_iff_eq_inv_smul] at h
      rw [h, Allowable.smul_address, map_inv, Tree.inv_apply, smul_inr]
    simp only [Enumeration.smul_f, Enumeration.smul_max, SpecCondition.flexible.injEq]
    refine ⟨trivial, ?_, ?_⟩
    · ext j
      constructor
      · rintro ⟨hj₁, N', hj₂, hj₃⟩
        refine ⟨hj₁, Allowable.toStructPerm ρ A • N', ?_, ?_⟩
        · rw [hj₂, Allowable.smul_address, smul_inr]
        · rw [NearLitterPerm.smul_nearLitter_fst, hj₃,
            NearLitterPerm.smul_nearLitter_fst, smul_inv_smul]
      · rintro ⟨hj₁, N', hj₂, hj₃⟩
        refine ⟨hj₁, (Allowable.toStructPerm ρ A)⁻¹ • N', ?_, ?_⟩
        · rw [smul_eq_iff_eq_inv_smul] at hj₂
          rw [hj₂, Allowable.smul_address, smul_inr, map_inv, Tree.inv_apply]
        · simp only [NearLitterPerm.smul_nearLitter_fst, smul_left_cancel_iff]
          exact hj₃
    · ext j k
      constructor
      · rintro ⟨hj, hk, a, N', h₁, h₂, h₃, h₄⟩
        refine ⟨hj, hk, Allowable.toStructPerm ρ A • a, Allowable.toStructPerm ρ A • N',
            ?_, ?_, ?_, ?_⟩
        · rw [NearLitterPerm.smul_nearLitter_fst, h₁,
            NearLitterPerm.smul_nearLitter_fst, smul_inv_smul]
        · rw [← mem_inv_smul_set_iff, smul_set_symmDiff,
            ← NearLitterPerm.smul_nearLitter_coe, ← NearLitterPerm.smul_nearLitter_coe,
            inv_smul_smul]
          exact h₂
        · rw [h₃, Allowable.smul_address, smul_inr]
        · rw [h₄, Allowable.smul_address, smul_inl]
      · rintro ⟨hj, hk, a, N', h₁, h₂, h₃, h₄⟩
        refine ⟨hj, hk, (Allowable.toStructPerm ρ A)⁻¹ • a, (Allowable.toStructPerm ρ A)⁻¹ • N',
            ?_, ?_, ?_, ?_⟩
        · rw [NearLitterPerm.smul_nearLitter_fst, h₁,
            NearLitterPerm.smul_nearLitter_fst]
        · rw [← mem_inv_smul_set_iff, smul_set_symmDiff,
            ← NearLitterPerm.smul_nearLitter_coe, ← NearLitterPerm.smul_nearLitter_coe,
            inv_smul_smul, inv_inv, smul_inv_smul]
          exact h₂
        · rw [smul_eq_iff_eq_inv_smul] at h₃
          rw [h₃, Allowable.smul_address, map_inv, Tree.inv_apply, smul_inr]
        · rw [smul_eq_iff_eq_inv_smul] at h₄
          rw [h₄, Allowable.smul_address, map_inv, Tree.inv_apply, smul_inl]
  case inflexibleCoe_spec =>
    rintro i hi A N ⟨P, t, ht⟩ hSi
    rw [hσS.inflexibleCoe_spec i hi A ((Allowable.toStructPerm ρ A)⁻¹ • N)
      ⟨P, (Allowable.comp (P.B.cons P.hδ) ρ)⁻¹ • t, ?_⟩]
    swap
    · rw [Enumeration.smul_f, smul_eq_iff_eq_inv_smul] at hSi
      rw [hSi, Allowable.smul_address, map_inv, Tree.inv_apply, smul_inr]
    swap
    · have := (InflexibleCoe.smul ⟨P, t, ht⟩ ρ⁻¹).hL
      simp only [map_inv, Tree.inv_apply, inflexibleCoe_smul_path, inflexibleCoe_smul_t] at this
      exact this
    rw [SpecCondition.inflexibleCoe.injEq]
    refine ⟨rfl, HEq.rfl, heq_of_eq ?_, ?_⟩
    · simp only [NearLitterPerm.smul_nearLitter_fst, inflexibleCoe_smul_path, inflexibleCoe_smul_t,
        Tree.inv_apply, ne_eq, eq_mp_eq_cast, CodingFunction.code_eq_code_iff]
      refine ⟨Allowable.comp (P.B.cons P.hδ) ρ, ?_, (smul_inv_smul _ _).symm⟩
      simp only [Support.before_smul, Support.comp_smul, NearLitterPerm.smul_nearLitter_fst,
        inflexibleCoe_smul_path, inflexibleCoe_smul_t, Tree.inv_apply, ne_eq, eq_mp_eq_cast]
    · ext j k
      constructor
      · rintro ⟨hj, hk, a, N', h₁, h₂, h₃, h₄⟩
        refine ⟨hj, hk, Allowable.toStructPerm ρ A • a, Allowable.toStructPerm ρ A • N',
            ?_, ?_, ?_, ?_⟩
        · rw [NearLitterPerm.smul_nearLitter_fst, h₁,
            NearLitterPerm.smul_nearLitter_fst, smul_inv_smul]
        · rw [← mem_inv_smul_set_iff, smul_set_symmDiff,
            ← NearLitterPerm.smul_nearLitter_coe, ← NearLitterPerm.smul_nearLitter_coe,
            inv_smul_smul]
          exact h₂
        · rw [Enumeration.smul_f, h₃, Allowable.smul_address, smul_inr]
        · rw [Enumeration.smul_f, h₄, Allowable.smul_address, smul_inl]
      · rintro ⟨hj, hk, a, N', h₁, h₂, h₃, h₄⟩
        refine ⟨hj, hk, (Allowable.toStructPerm ρ A)⁻¹ • a, (Allowable.toStructPerm ρ A)⁻¹ • N',
            ?_, ?_, ?_, ?_⟩
        · rw [NearLitterPerm.smul_nearLitter_fst, h₁,
            NearLitterPerm.smul_nearLitter_fst]
        · rw [← mem_inv_smul_set_iff, smul_set_symmDiff,
            ← NearLitterPerm.smul_nearLitter_coe, ← NearLitterPerm.smul_nearLitter_coe,
            inv_smul_smul, inv_inv, smul_inv_smul]
          exact h₂
        · rw [Enumeration.smul_f, smul_eq_iff_eq_inv_smul] at h₃
          rw [h₃, Allowable.smul_address, map_inv, Tree.inv_apply, smul_inr]
        · rw [Enumeration.smul_f, smul_eq_iff_eq_inv_smul] at h₄
          rw [h₄, Allowable.smul_address, map_inv, Tree.inv_apply, smul_inl]
  case inflexibleBot_spec =>
    rintro i hi A N ⟨P, a, ha⟩ hSi
    rw [hσS.inflexibleBot_spec i hi A ((Allowable.toStructPerm ρ A)⁻¹ • N)
      ⟨P, (Allowable.toStructPerm ρ (P.B.cons (bot_lt_coe _)))⁻¹ • a, ?_⟩]
    swap
    · rw [Enumeration.smul_f, smul_eq_iff_eq_inv_smul] at hSi
      rw [hSi, Allowable.smul_address, map_inv, Tree.inv_apply, smul_inr]
    swap
    · have := (InflexibleBot.smul ⟨P, a, ha⟩ ρ⁻¹).hL
      simp only [map_inv, Tree.inv_apply] at this
      rw [NearLitterPerm.smul_nearLitter_fst, this, InflexibleBot.smul]
      simp_rw [Allowable.comp_bot, map_inv, Tree.inv_apply]
    rw [SpecCondition.inflexibleBot.injEq]
    refine ⟨rfl, HEq.rfl, ?_, ?_⟩
    · ext j
      constructor
      · rintro ⟨hj, hjS⟩
        refine ⟨hj, ?_⟩
        rw [Enumeration.smul_f, hjS, Allowable.smul_address, smul_inl, smul_inv_smul]
      · rintro ⟨hj, hjS⟩
        refine ⟨hj, ?_⟩
        rw [Enumeration.smul_f, smul_eq_iff_eq_inv_smul] at hjS
        simp_rw [hjS, Allowable.smul_address, smul_inl, map_inv, Tree.inv_apply]
    · ext j k
      constructor
      · rintro ⟨hj, hk, a, N', h₁, h₂, h₃, h₄⟩
        refine ⟨hj, hk, Allowable.toStructPerm ρ A • a, Allowable.toStructPerm ρ A • N',
            ?_, ?_, ?_, ?_⟩
        · rw [NearLitterPerm.smul_nearLitter_fst, h₁,
            NearLitterPerm.smul_nearLitter_fst, smul_inv_smul]
        · rw [← mem_inv_smul_set_iff, smul_set_symmDiff,
            ← NearLitterPerm.smul_nearLitter_coe, ← NearLitterPerm.smul_nearLitter_coe,
            inv_smul_smul]
          exact h₂
        · rw [Enumeration.smul_f, h₃, Allowable.smul_address, smul_inr]
        · rw [Enumeration.smul_f, h₄, Allowable.smul_address, smul_inl]
      · rintro ⟨hj, hk, a, N', h₁, h₂, h₃, h₄⟩
        refine ⟨hj, hk, (Allowable.toStructPerm ρ A)⁻¹ • a, (Allowable.toStructPerm ρ A)⁻¹ • N',
            ?_, ?_, ?_, ?_⟩
        · rw [NearLitterPerm.smul_nearLitter_fst, h₁,
            NearLitterPerm.smul_nearLitter_fst]
        · rw [← mem_inv_smul_set_iff, smul_set_symmDiff,
            ← NearLitterPerm.smul_nearLitter_coe, ← NearLitterPerm.smul_nearLitter_coe,
            inv_smul_smul, inv_inv, smul_inv_smul]
          exact h₂
        · rw [Enumeration.smul_f, smul_eq_iff_eq_inv_smul] at h₃
          rw [h₃, Allowable.smul_address, map_inv, Tree.inv_apply, smul_inr]
        · rw [Enumeration.smul_f, smul_eq_iff_eq_inv_smul] at h₄
          rw [h₄, Allowable.smul_address, map_inv, Tree.inv_apply, smul_inl]

end ConNF
