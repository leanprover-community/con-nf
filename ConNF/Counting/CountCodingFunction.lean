import ConNF.Counting.Recode

/-!
# Counting coding functions
-/

open Cardinal Function MulAction Set Quiver
open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions] [CountingAssumptions]
  {β γ : Λ} [LeLevel β] [LeLevel γ] (hγ : (γ : TypeIndex) < β)

def RecodeType (o : SupportOrbit β) : Type u :=
  { x : Set (RaisedSingleton hγ) //
    ∃ ho : ∀ U ∈ o, AppearsRaised hγ (Subtype.val '' x) U,
    ∀ U, ∀ hU : U ∈ o,
      Supports (Allowable β) {c | c ∈ U} (decodeRaised hγ (Subtype.val '' x) U (ho U hU)) }

noncomputable def recodeSurjection (o : SupportOrbit β) (x : RecodeType hγ o) :
    CodingFunction β :=
  raisedCodingFunction hγ (Subtype.val '' x.val) o
    x.prop.choose x.prop.choose_spec

theorem recodeSurjection_surjective :
    Surjective (fun (x : (o : SupportOrbit β) × RecodeType hγ o) =>
      recodeSurjection hγ x.1 x.2) := by
  rintro χ
  obtain ⟨S, hS⟩ := χ.dom_nonempty
  refine ⟨⟨SupportOrbit.mk S, Subtype.val ⁻¹' raiseSingletons hγ S ((χ.decode S).get hS),
      ?_, ?_⟩, ?_⟩
  · intro U hU
    rw [image_preimage_eq_of_subset (raiseSingletons_subset_range hγ)]
    exact appearsRaised_of_mem_orbit hγ S ((χ.decode S).get hS) (χ.supports_decode S hS) U hU
  · intro U hU
    conv in (Subtype.val '' _) => rw [image_preimage_eq_of_subset (raiseSingletons_subset_range hγ)]
    exact supports_decodeRaised_of_mem_orbit hγ S
      ((χ.decode S).get hS) (χ.supports_decode S hS) U hU
  · dsimp only
    rw [recodeSurjection]
    conv in (Subtype.val '' _) => rw [image_preimage_eq_of_subset (raiseSingletons_subset_range hγ)]
    conv_rhs => rw [CodingFunction.eq_code hS,
      ← recode_eq hγ S ((χ.decode S).get hS) (χ.supports_decode S hS)]

theorem recodeSurjection_range :
    Set.univ ⊆ Set.range (fun (x : (o : SupportOrbit β) × RecodeType hγ o) =>
      recodeSurjection hγ x.1 x.2) := by
  intro χ _
  exact recodeSurjection_surjective hγ χ

theorem mk_codingFunction_le :
    #(CodingFunction β) ≤ #(SupportOrbit β) * 2 ^ #(RaisedSingleton hγ) := by
  have := mk_subtype_le_of_subset (recodeSurjection_range hγ)
  have := mk_univ.symm.trans_le (this.trans mk_range_le)
  rw [mk_sigma] at this
  have h : ∀ o, #(RecodeType hγ o) ≤ 2 ^ #(RaisedSingleton hγ)
  · intro o
    refine (mk_subtype_le _).trans ?_
    rw [mk_set]
  have := this.trans (Cardinal.sum_le_sum _ _ h)
  simp only [sum_const, lift_id] at this
  exact this

end ConNF
