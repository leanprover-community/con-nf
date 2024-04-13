import ConNF.Model.Predicative
import ConNF.Model.RaiseStrong

open Quiver Sum WithBot

open scoped Cardinal Pointwise symmDiff

universe u

noncomputable section

namespace ConNF

variable [Params.{u}]

section FOA

variable [Level] {β γ : Λ} [iβ : LtLevel β] [iγ : LtLevel γ] (hγ : (γ : TypeIndex) < β)

local instance : FOAAssumptions := MainInduction.FOA.foaAssumptions

theorem symmetric_of_image_singleton_symmetric' (s : Set (TSet γ))
    (h : Symmetric (coe_lt_coe.mp iβ.elim) (.singleton (coe_lt_coe.mp hγ) '' s)) :
    Symmetric (coe_lt_coe.mp hγ) s := by
  obtain ⟨S, hS₁, hS₂⟩ := h
  refine ⟨raise iβ.elim ⁻¹' (Support.strongSupport (Enumeration.ofSet S hS₁).small).carrier, ?_, ?_⟩
  · refine Small.preimage ?_ (Support.strongSupport (Enumeration.ofSet S hS₁).small).small
    intro c d h
    exact raise_injective iβ.elim h
  intro ρ hρ
  refine subset_antisymm ?_ ?_
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨ρ', hρ'S, hρ'T⟩ := Support.raiseRaise_eq_smul (hγ := hγ)
      (Support.strongSupport (Enumeration.ofSet S hS₁).small)
      (Support.strongSupport_strong (Enumeration.ofSet S hS₁).small)
      t.support ρ hρ
    have := hS₂ ρ' ?_
    · rw [Set.ext_iff] at this
      obtain ⟨u, hu, hu'⟩ := (this _).mp ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      simp only [smul_singleton] at hu'
      cases singleton_injective' _ _ _ hu'
      refine Set.mem_of_eq_of_mem ?_ hu
      have := t.support_supports ((cons (coe_lt_coe.mp hγ) (cons (coe_lt_coe.mp iβ.elim) ρ'))⁻¹ *
        cons (coe_lt_coe.mp hγ) ρ) ?_
      · rw [mul_smul, inv_smul_eq_iff] at this
        exact this
      rintro _ ⟨i, hi, rfl⟩
      rw [mul_smul, inv_smul_eq_iff]
      exact (support_f_congr hρ'T i hi).symm
    · intro c hc
      have := Support.subset_strongSupport (Enumeration.ofSet S hS₁).small (a := c) ?_
      swap
      · rw [Enumeration.ofSet_coe]
        exact hc
      obtain ⟨i, hi, rfl⟩ := this
      exact support_f_congr hρ'S i hi
  · intro t ht
    have := Support.raiseRaise_eq_smul (hγ := hγ)
      (Support.strongSupport (Enumeration.ofSet S hS₁).small)
      (Support.strongSupport_strong (Enumeration.ofSet S hS₁).small)
      ((cons (coe_lt_coe.mp hγ) ρ)⁻¹ • t).support ρ hρ
    obtain ⟨ρ', hρ'S, hρ'T⟩ := this
    have := hS₂ ρ' ?_
    · rw [Set.ext_iff] at this
      obtain ⟨_, ⟨u, hu, rfl⟩, hu'⟩ := (this (.singleton (coe_lt_coe.mp hγ) t)).mpr ⟨t, ht, rfl⟩
      simp only [smul_singleton] at hu'
      have hu' := singleton_injective' _ _ _ hu'
      have := ((cons (coe_lt_coe.mp hγ) ρ)⁻¹ • t).support_supports
        ((cons (coe_lt_coe.mp hγ) (cons (coe_lt_coe.mp iβ.elim) ρ'))⁻¹ *
          cons (coe_lt_coe.mp hγ) ρ) ?_
      · rw [smul_eq_iff_eq_inv_smul] at hu'
        rw [mul_smul, smul_inv_smul, ← hu', ← smul_eq_iff_eq_inv_smul] at this
        exact ⟨u, hu, this⟩
      rintro _ ⟨i, hi, rfl⟩
      rw [mul_smul, inv_smul_eq_iff]
      exact (support_f_congr hρ'T i hi).symm
    · intro c hc
      have := Support.subset_strongSupport (Enumeration.ofSet S hS₁).small (a := c) ?_
      swap
      · rw [Enumeration.ofSet_coe]
        exact hc
      obtain ⟨i, hi, rfl⟩ := this
      exact support_f_congr hρ'S i hi

end FOA

theorem symmetric_of_image_singleton_symmetric {α β γ : Λ} (hβ : β < α) (hγ : γ < β)
    (s : Set (TSet γ))
    (h : Symmetric hβ (.singleton hγ '' s)) : Symmetric hγ s :=
  letI : Level := ⟨α⟩
  letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
  letI : LtLevel γ := ⟨coe_lt_coe.mpr (hγ.trans hβ)⟩
  symmetric_of_image_singleton_symmetric' (coe_lt_coe.mpr hγ) s h

end ConNF
