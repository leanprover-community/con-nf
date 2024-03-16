import ConNF.Counting.Recode

/-!
# Counting coding functions
-/

open Cardinal Function MulAction Set
open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] [Level] [CountingAssumptions] {β γ : Λ} [LeLevel β] [LeLevel γ]
  (hγ : (γ : TypeIndex) < β)

noncomputable def recodeSurjection
    (x : { x : Set (RaisedSingleton hγ) × SupportOrbit β //
      ∃ ho : ∀ U ∈ x.2, AppearsRaised hγ (Subtype.val '' x.1) U,
      ∀ U, ∀ hU : U ∈ x.2,
        Supports (Allowable β) {c | c ∈ U} (decodeRaised hγ (Subtype.val '' x.1) U (ho U hU)) }) :
    CodingFunction β :=
  raisedCodingFunction hγ (Subtype.val '' x.val.1) x.val.2 x.prop.choose x.prop.choose_spec

theorem recodeSurjection_surjective : Surjective (recodeSurjection hγ) := by
  rintro χ
  obtain ⟨S, hS⟩ := χ.dom_nonempty
  refine ⟨⟨⟨Subtype.val ⁻¹' raiseSingletons hγ S ((χ.decode S).get hS), SupportOrbit.mk S⟩,
      ?_, ?_⟩, ?_⟩
  · intro U hU
    rw [image_preimage_eq_of_subset (raiseSingletons_subset_range hγ)]
    exact appearsRaised_of_mem_orbit hγ S ((χ.decode S).get hS) (χ.supports_decode S hS) U hU
  · intro U hU
    conv in (Subtype.val '' _) => rw [image_preimage_eq_of_subset (raiseSingletons_subset_range hγ)]
    exact supports_decodeRaised_of_mem_orbit hγ S
      ((χ.decode S).get hS) (χ.supports_decode S hS) U hU
  · rw [recodeSurjection]
    conv in (Subtype.val '' _) => rw [image_preimage_eq_of_subset (raiseSingletons_subset_range hγ)]
    conv_rhs => rw [CodingFunction.eq_code hS,
      ← recode_eq hγ S ((χ.decode S).get hS) (χ.supports_decode S hS)]

/-- The main lemma about counting coding functions. -/
theorem mk_strong_codingFunction_le :
    #(CodingFunction β) ≤ 2 ^ #(RaisedSingleton hγ) * #(SupportOrbit β) := by
  refine (mk_le_of_surjective (recodeSurjection_surjective hγ)).trans ?_
  refine (mk_subtype_le _).trans ?_
  simp only [mk_prod, mk_set, lift_id, le_refl]

end ConNF
