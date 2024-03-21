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

def RecodeType (S : Support β) : Type u :=
  { x : Set (RaisedSingleton hγ S) //
    ∃ ho : ∀ U ∈ SupportOrbit.mk S, AppearsRaised hγ (Subtype.val '' x) U,
    ∀ U, ∀ hU : U ∈ SupportOrbit.mk S,
      Supports (Allowable β) {c | c ∈ U} (decodeRaised hγ (Subtype.val '' x) U (ho U hU)) }

noncomputable def recodeSurjection (S : Support β) (x : RecodeType hγ S) :
    CodingFunction β :=
  raisedCodingFunction hγ (Subtype.val '' x.val) (SupportOrbit.mk S)
    x.prop.choose x.prop.choose_spec

theorem recodeSurjection_surjective :
    Surjective (fun (x : (S : Support β) × RecodeType hγ S) => recodeSurjection hγ x.1 x.2) := by
  rintro χ
  obtain ⟨S, hS⟩ := χ.dom_nonempty
  refine ⟨⟨S, Subtype.val ⁻¹' raiseSingletons hγ S ((χ.decode S).get hS),
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

/-
def RaisedSingleton.smul {S : Support β} (r : RaisedSingleton hγ S) (ρ : Allowable β) :
    RaisedSingleton hγ (ρ • S) :=
  ⟨r.val, by
    obtain ⟨u, hu⟩ := r.prop
    refine ⟨Allowable.comp (Hom.toPath hγ) ρ • u, ?_⟩
    rw [hu]⟩

@[simp]
theorem RaisedSingleton.smul_val {S : Support β} (r : RaisedSingleton hγ S) (ρ : Allowable β) :
    (r.smul hγ ρ).val = r.val :=
  rfl

theorem RaisedSingleton.smul_image_val {S : Support β} {ρ : Allowable β}
    (x : Set (RaisedSingleton hγ (ρ • S))) :
    Subtype.val '' {u : RaisedSingleton hγ S | u.smul hγ ρ ∈ x} = Subtype.val '' x := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨r, h, rfl⟩
    exact ⟨RaisedSingleton.smul hγ r ρ, h, rfl⟩
  · rintro _ ⟨r, h, rfl⟩
    refine ⟨⟨r.val, ?_⟩, h, rfl⟩
    obtain ⟨u, hu⟩ := (RaisedSingleton.smul hγ r ρ⁻¹).prop
    simp only [smul_val, inv_smul_smul] at hu
    exact ⟨u, hu⟩
-/

theorem recodeSurjection_range_smul_subset (S : Support β) (ρ : Allowable β) :
    Set.range (recodeSurjection hγ (ρ • S)) ⊆ Set.range (recodeSurjection hγ S) := by
  rintro _ ⟨⟨x, h₁, h₂⟩, rfl⟩
  sorry
  -- refine ⟨⟨{u | u.smul hγ ρ ∈ x}, ?_, ?_⟩, ?_⟩
  -- · intro U hU
  --   rw [RaisedSingleton.smul_image_val]
  --   refine h₁ U ?_
  --   simp only [SupportOrbit.mem_mk_iff, orbit_smul] at hU ⊢
  --   exact hU
  -- · intro U hU ρ' h
  --   have := h₂ U ?_ ρ' h
  --   · simp_rw [RaisedSingleton.smul_image_val hγ x]
  --     exact this
  --   · simp only [SupportOrbit.mem_mk_iff, orbit_smul] at hU ⊢
  --     exact hU
  -- · rw [recodeSurjection, recodeSurjection]
  --   simp only
  --   simp_rw [RaisedSingleton.smul_image_val hγ x]
  --   congr 1
  --   rw [← SupportOrbit.mem_def, SupportOrbit.mem_mk_iff]
  --   refine ⟨ρ⁻¹, ?_⟩
  --   simp only [inv_smul_smul]

theorem recodeSurjection_range_smul (S : Support β) (ρ : Allowable β) :
    Set.range (recodeSurjection hγ (ρ • S)) = Set.range (recodeSurjection hγ S) := by
  refine subset_antisymm ?_ ?_
  · exact recodeSurjection_range_smul_subset hγ S ρ
  · have := recodeSurjection_range_smul_subset hγ (ρ • S) ρ⁻¹
    rw [inv_smul_smul] at this
    exact this

theorem recodeSurjection_range :
    Set.univ ⊆ ⋃ (o : SupportOrbit β), Set.range (recodeSurjection hγ o.out) := by
  intro χ _
  simp only [mem_iUnion, mem_range]
  obtain ⟨⟨S, x⟩, h⟩ := recodeSurjection_surjective hγ χ
  refine ⟨SupportOrbit.mk S, ?_⟩
  have := SupportOrbit.out_mem (SupportOrbit.mk S)
  rw [SupportOrbit.mem_mk_iff] at this
  obtain ⟨ρ, hρ⟩ := this
  dsimp only at hρ
  obtain ⟨y, rfl⟩ := (Set.ext_iff.mp (recodeSurjection_range_smul hγ S ρ) χ).mpr ⟨x, h⟩
  refine ⟨hρ ▸ y, ?_⟩
  congr 1
  · exact hρ.symm
  · simp only [eqRec_heq_iff_heq, heq_eq_eq]

theorem mk_codingFunction_le :
    #(CodingFunction β) ≤ sum (fun o : SupportOrbit β => 2 ^ #(RaisedSingleton hγ o.out)) := by
  have := mk_subtype_le_of_subset (recodeSurjection_range hγ)
  have := mk_univ.symm.trans_le (this.trans (mk_iUnion_le_sum_mk))
  suffices h : ∀ S, #(Set.range (recodeSurjection hγ S)) ≤ 2 ^ #(RaisedSingleton hγ S)
  · exact this.trans (sum_le_sum _ _ (fun o => h _))
  intro S
  refine mk_range_le.trans ?_
  refine (mk_subtype_le _).trans ?_
  simp only [mk_prod, mk_set, lift_id, le_refl]

end ConNF
