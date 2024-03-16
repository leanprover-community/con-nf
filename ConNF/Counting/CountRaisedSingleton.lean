import ConNF.Counting.Recode
import ConNF.Counting.Spec

/-!
# Counting raised singletons
-/

open Cardinal Function MulAction Set Quiver

open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] [Level] [CountingAssumptions] {β γ : Λ} [LeLevel β] [LeLevel γ]
    (hγ : (γ : TypeIndex) < β)

noncomputable def RaisedSingleton.code (S : Support β) (r : RaisedSingleton hγ S) :
    SupportOrbit β × CodingFunction γ :=
  (SupportOrbit.mk (raisedSupport hγ S r.prop.choose),
    CodingFunction.code _ _ (support_supports r.prop.choose))

theorem smul_singleton_smul (S : Support β) (u : Tangle γ) (ρ₁ : Allowable β) (ρ₂ : Allowable γ)
    (h₁ : ρ₁ • raisedSupport hγ S (ρ₂ • u) = raisedSupport hγ S u) :
    ρ₁ • singleton β γ hγ (ρ₂ • u) = singleton β γ hγ u := by
  rw [singleton_smul]
  refine congr_arg _ ?_
  rw [smul_smul]
  refine support_supports u (Allowable.comp (Hom.toPath hγ) ρ₁ * ρ₂) ?_
  rintro c ⟨i, hi, hc⟩
  rw [raisedSupport, raisedSupport] at h₁
  have := support_f_congr h₁ (S.max + i) ?_
  swap
  · simp only [smul_support, Enumeration.add_max, Enumeration.smul_max, Enumeration.image_max,
      add_lt_add_iff_left]
    exact hi
  rw [Enumeration.add_f_right_add (by exact hi), Enumeration.smul_f,
    Enumeration.add_f_right_add] at this
  swap
  · simp only [smul_support, Enumeration.image_max, Enumeration.smul_max]
    exact hi
  simp only [smul_support, Enumeration.image_f, raise, raiseIndex, Enumeration.smul_f, ← hc,
    Allowable.smul_address, Address.mk.injEq, true_and] at this
  refine Address.ext _ _ rfl ?_
  simp only [mul_smul, Allowable.smul_address, Allowable.toStructPerm_comp, Tree.comp_apply]
  exact this

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
