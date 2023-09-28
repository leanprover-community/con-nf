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
    #{χ : CodingFunction β // χ.Strong} ≤
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
    lift.{u + 1, u} #{ o : OrdSupportOrbit β // o.Strong } ≤
      #{ σ : Spec β // ∃ S : OrdSupport β, σ.Specifies S } := by
  refine ⟨fun o => ⟨o.down.val.spec o.down.prop,
    o.down.prop.out, o.down.val.spec_specifies_out _⟩, ?_⟩
  intro o₁ o₂ h
  rw [Subtype.mk.injEq] at h
  exact ULift.ext _ _ (Subtype.coe_injective (OrdSupportOrbit.spec_injective h))

end ConNF
