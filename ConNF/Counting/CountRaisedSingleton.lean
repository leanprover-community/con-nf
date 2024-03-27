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

theorem mem_orbit_of_raiseSingleton_eq (S₁ S₂ : Support β) (u₁ u₂ : TSet γ)
    (hS : S₁.max = S₂.max)
    (hu : CodingFunction.code _ _ (TangleData.TSet.support_supports u₁) =
      CodingFunction.code _ _ (TangleData.TSet.support_supports u₂))
    (hSu : SupportOrbit.mk (raisedSupport hγ S₁ u₁) = SupportOrbit.mk (raisedSupport hγ S₂ u₂)) :
    raiseSingleton hγ S₁ u₁ = raiseSingleton hγ S₂ u₂ := by
  rw [CodingFunction.code_eq_code_iff] at hu
  obtain ⟨ρ₁, hρ₁, rfl⟩ := hu
  symm at hSu
  rw [← SupportOrbit.mem_def, SupportOrbit.mem_mk_iff] at hSu
  obtain ⟨ρ₂, hSu⟩ := hSu
  simp only [raiseSingleton, raisedSupport, CodingFunction.code_eq_code_iff,
    Enumeration.smul_add] at hSu ⊢
  obtain ⟨rfl, hSu'⟩ := Enumeration.add_congr (by exact hS) hSu
  have : Allowable.comp (Hom.toPath hγ) ρ₂ • u₁ = ρ₁ • u₁
  · rw [← inv_smul_eq_iff, smul_smul]
    refine u₁.support_supports _ ?_
    rintro c ⟨i, hi, rfl⟩
    rw [mul_smul, inv_smul_eq_iff]
    have := support_f_congr hSu' i hi
    simp only [Enumeration.smul_f, Enumeration.image_f, hρ₁, raise,
      raiseIndex, Allowable.smul_address, Allowable.toStructPerm_comp, Tree.comp_apply] at this ⊢
    refine Address.ext _ _ rfl ?_
    have := congr_arg Address.value this
    exact this
  refine ⟨ρ₂, hSu.symm, ?_⟩
  rw [← this, singleton_smul]

noncomputable def RaisedSingleton.code (r : RaisedSingleton hγ) :
    κ × SupportOrbit β × CodingFunction γ :=
  (r.prop.choose.max,
    SupportOrbit.mk (raisedSupport hγ r.prop.choose r.prop.choose_spec.choose),
    CodingFunction.code _ _ (TangleData.TSet.support_supports r.prop.choose_spec.choose))

theorem RaisedSingleton.code_injective :
    Function.Injective (RaisedSingleton.code hγ) := by
  rintro r₁ r₂ h
  refine Subtype.coe_injective ?_
  dsimp only
  rw [r₁.prop.choose_spec.choose_spec, r₂.prop.choose_spec.choose_spec]
  exact mem_orbit_of_raiseSingleton_eq hγ _ _ _ _
    (congr_arg (fun x => x.1) h)
    (congr_arg (fun x => x.2.2) h)
    (congr_arg (fun x => x.2.1) h)

theorem mk_raisedSingleton_le :
    #(RaisedSingleton hγ) ≤ #κ * #(SupportOrbit β) * #(CodingFunction γ) := by
  have := mk_le_of_injective (RaisedSingleton.code_injective hγ)
  simp only [mk_prod, lift_id, ← mul_assoc] at this
  exact this

end ConNF
