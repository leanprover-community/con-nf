import ConNF.Counting.Recode
import ConNF.Counting.Spec

/-!
# Counting raised singletons
-/

open Cardinal Function MulAction Set Quiver

open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions] [CountingAssumptions]
    {β γ : Λ} [LeLevel β] [LeLevel γ] (hγ : (γ : TypeIndex) < β)

noncomputable def RaisedSingleton.code (S : Support β) (r : RaisedSingleton hγ S) :
    SupportOrbit β × CodingFunction γ :=
  (SupportOrbit.mk (raisedSupport hγ S r.prop.choose),
    CodingFunction.code _ _ (Shell.support_supports r.prop.choose))

/-- TODO: Move this -/
instance : IsLeftCancelAdd κ := by
  constructor
  intro i j k h
  have := congr_arg (Ordinal.typein (· < ·)) h
  rw [Params.κ_add_typein, Params.κ_add_typein, Ordinal.add_left_cancel] at this
  exact Ordinal.typein_injective _ this

theorem smul_singleton_smul (S : Support β) (u : Shell γ) (ρ₁ : Allowable β) (ρ₂ : Allowable γ)
    (h₁ : ρ₁ • raisedSupport hγ S (ρ₂ • u) = raisedSupport hγ S u) :
    ρ₁ • Shell.singleton β γ hγ (ρ₂ • u) = Shell.singleton β γ hγ u := by
  rw [Shell.singleton_smul]
  refine congr_arg _ ?_
  rw [smul_smul]
  have := Shell.support_supports u
    (Allowable.comp (Hom.toPath hγ) ρ₁ * (ρ₂ • u).twist * u.twist⁻¹) ?_
  · refine Eq.trans ?_ this
    simp only [mul_smul, smul_left_cancel_iff]
    rw [← (smul_eq_iff_eq_inv_smul _).mp u.eq_twist_smul,
      ← Shell.Orbit.mk_smul u ρ₂, (ρ₂ • u).eq_twist_smul]
  rintro c ⟨i, hi, hc⟩
  rw [raisedSupport, raisedSupport] at h₁
  have hi' : i < (ρ₂ • u).support.max
  · have := congr_arg Enumeration.max h₁
    simp only [Enumeration.smul_add, Enumeration.add_max, Enumeration.smul_max,
      Enumeration.image_max, add_right_inj] at this
    rw [this]
    exact hi
  have := support_f_congr h₁ (S.max + i) ?_
  swap
  · rw [Enumeration.smul_max, Enumeration.add_max, Enumeration.image_max, add_lt_add_iff_left]
    exact hi'
  rw [Enumeration.add_f_right_add (by exact hi),
    Enumeration.smul_f, Enumeration.add_f_right_add (by exact hi')] at this
  refine Address.ext _ _ rfl ?_
  simp only [Enumeration.image_f, raise, raiseIndex, Allowable.smul_address, ← hc,
    Address.mk.injEq] at this
  simp only [Shell.support, Shell.Orbit.mk_smul, Enumeration.smul_f, Allowable.smul_address,
    mul_smul, map_inv, Tree.inv_apply, Allowable.toStructPerm_comp, Tree.comp_apply] at this ⊢
  obtain ⟨h₁, h₂⟩ := this
  rw [Path.comp_inj_right] at h₁
  rw [h₁] at h₂
  refine Eq.trans ?_ h₂
  rw [smul_left_cancel_iff, smul_left_cancel_iff]
  simp only [Shell.support] at hc
  rw [congr_arg Address.value hc, Enumeration.smul_f]
  simp only [inv_smul_eq_iff, Allowable.smul_address, h₁]

theorem RaisedSingleton.code_injective (S : Support β) :
    Function.Injective (RaisedSingleton.code hγ S) := by
  rintro r₁ r₂ h
  refine Subtype.coe_injective ?_
  dsimp only
  rw [code, code, Prod.mk.injEq, CodingFunction.code_eq_code_iff] at h
  rw [← SupportOrbit.mem_def, SupportOrbit.mem_mk_iff] at h
  obtain ⟨⟨ρ₁, hρ₁⟩, ⟨ρ₂, hρ₂, hρ₂'⟩⟩ := h
  rw [r₁.prop.choose_spec, r₂.prop.choose_spec, raiseSingleton, raiseSingleton]
  rw [CodingFunction.code_eq_code_iff]
  refine ⟨ρ₁⁻¹ , ?_, ?_⟩
  · rw [← hρ₁, inv_smul_smul]
  rw [hρ₂'] at hρ₁ ⊢
  rw [← smul_eq_iff_eq_inv_smul]
  exact smul_singleton_smul hγ S _ ρ₁ ρ₂ hρ₁

theorem mk_raisedSingleton_le (S : Support β) :
    #(RaisedSingleton hγ S) ≤ #(SupportOrbit β) * #(CodingFunction γ) := by
  have := mk_le_of_injective (RaisedSingleton.code_injective hγ S)
  simp only [mk_prod, lift_id] at this
  exact this

end ConNF
