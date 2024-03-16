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
    CodingFunction γ :=
  CodingFunction.code _ _ (support_supports r.prop.choose)

theorem RaisedSingleton.code_injective (S : Support β) :
    Function.Injective (RaisedSingleton.code hγ S) := by
  rintro r₁ r₂ h
  refine Subtype.coe_injective ?_
  dsimp only
  rw [r₁.prop.choose_spec, r₂.prop.choose_spec, raiseSingleton, raiseSingleton]
  rw [code, code] at h
  rw [CodingFunction.code_eq_code_iff] at h ⊢
  obtain ⟨ρ, hρ₁, hρ₂⟩ := h
  sorry

end ConNF
