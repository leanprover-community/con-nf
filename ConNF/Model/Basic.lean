import ConNF.Model.Redefinitions

open Quiver WithBot

open scoped Pointwise

universe u

noncomputable section

namespace ConNF

variable [Params.{u}]

def mem {β α : Λ} (h : β < α) (tβ : TSet β) (tα : TSet α) : Prop :=
  toPretangle tβ ∈ Pretangle.ofCoe (toPretangle tα) β (coe_lt_coe.mpr h)

notation:50 tβ:50 " ∈[" h:50 "] " tα:50 => mem h tβ tα

theorem tSet_mk_aux {β α : Λ} (hβ : β < α) (s : Set (TSet β))
    (hs : ∃ S : Set (Address α), Small S ∧
      ∀ ρ : Allowable α, (∀ c ∈ S, ρ • c = c) →
      comp (Hom.toPath (coe_lt_coe.mpr hβ)) ρ • s = s) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
    ∃ S : Set (Address α), Small S ∧
      ∀ ρ : NewAllowable, (∀ c ∈ S, ρ • c = c) → ρ.val β • s = s := by
  obtain ⟨S, hS₁, hS₂⟩ := hs
  refine ⟨S, hS₁, ?_⟩
  intro ρ h
  have := hS₂ ((allowableIso α).symm ρ) ?_
  · convert this using 2
    have := allowableIso_val hβ ((allowableIso α).symm ρ)
    simp only [MulEquiv.apply_symm_apply, ConNF.allowableCons_eq] at this
    exact this
  · intro c hc
    have := allowableIso_smul_address ((allowableIso α).symm ρ) c
    simp only [MulEquiv.apply_symm_apply] at this
    rw [← this, h c hc]

def TSet.mk {β α : Λ} (hβ : β < α) (s : Set (TSet β))
    (hs : ∃ S : Set (Address α), Small S ∧
      ∀ ρ : Allowable α, (∀ c ∈ S, ρ • c = c) →
      comp (Hom.toPath (coe_lt_coe.mpr hβ)) ρ • s = s) : TSet α :=
  letI : Level := ⟨α⟩
  letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
  (tSetEquiv α).symm (NewTSet.intro s (tSet_mk_aux hβ s hs))

theorem TSet.toPretangle_eq {α : Λ} (t : TSet α) :
    toPretangle t = letI : Level := ⟨α⟩; NewTSet.toPretangle (tSetEquiv α t) := by
  rw [← tSetEquiv_toPretangle α t]
  rfl

theorem TSet.mem_tSetEquiv_iff {β α : Λ} (hβ : β < α) (s : TSet β) (t : TSet α) :
    s ∈[hβ] t ↔
      letI : Level := ⟨α⟩
      toPretangle s ∈
        Pretangle.ofCoe (NewTSet.toPretangle (tSetEquiv α t)) β (coe_lt_coe.mpr hβ) := by
  rw [mem, toPretangle_eq t]
  rfl

theorem TSet.ofCoe_toPretangle_apply_eq {β α : Λ} (hβ : β < α) (t : TSet α) :
    Pretangle.ofCoe (toPretangle t) β (coe_lt_coe.mpr hβ) =
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
    {p | ∃ s ∈ (tSetEquiv α t).val.members β, toPretangle s = p} := by
  letI : Level := ⟨α⟩
  letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
  rw [toPretangle_eq t, NewTSet.toPretangle]
  exact congr_fun₂ (Semitangle.toPretangle_ofCoe (tSetEquiv α t).val) β (coe_lt_coe.mpr hβ)

@[simp]
theorem TSet.mem_mk_iff {β α : Λ} (hβ : β < α) (s : Set (TSet β))
    (hs : ∃ S : Set (Address α), Small S ∧
      ∀ ρ : Allowable α, (∀ c ∈ S, ρ • c = c) →
      comp (Hom.toPath (coe_lt_coe.mpr hβ)) ρ • s = s) (t : TSet β) :
    t ∈[hβ] TSet.mk hβ s hs ↔ t ∈ s := by
  letI : Level := ⟨α⟩
  letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
  have := NewTSet.intro_members s (tSet_mk_aux hβ s hs)
  rw [mem, ofCoe_toPretangle_apply_eq hβ]
  simp only [Set.mem_setOf_eq, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
  rw [mk, Equiv.apply_symm_apply, this]

theorem TSet.eq_toPretangle_of_mem {β α : Λ} (hβ : β < α) (t₁ : TSet α) (t₂ : Pretangle β) :
    letI : Level := ⟨α⟩
    t₂ ∈ Pretangle.ofCoe (NewTSet.toPretangle (tSetEquiv α t₁)) β (coe_lt_coe.mpr hβ) →
    ∃ t₂' : TSet β, t₂ = toPretangle t₂' := by
  intro h
  simp only [NewTSet.toPretangle, Semitangle.toPretangle, Equiv.apply_symm_apply] at h
  obtain ⟨s, _, hs⟩ := h
  exact ⟨s, hs.symm⟩

theorem TSet.ext {β α : Λ} (hβ : β < α) (t₁ t₂ : TSet α) :
    (∀ s, s ∈[hβ] t₁ ↔ s ∈[hβ] t₂) → t₁ = t₂ := by
  intro h
  letI : Level := ⟨α⟩
  letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
  refine (tSetEquiv α).injective (NewTSet.ext β (tSetEquiv α t₁) (tSetEquiv α t₂) ?_)
  intro p
  simp_rw [TSet.mem_tSetEquiv_iff hβ] at h
  constructor
  · intro hp
    obtain ⟨s, rfl⟩ := eq_toPretangle_of_mem hβ t₁ p hp
    exact (h s).mp hp
  · intro hp
    obtain ⟨s, rfl⟩ := eq_toPretangle_of_mem hβ t₂ p hp
    exact (h s).mpr hp

theorem TSet.smul_mem_smul {β α : Λ} (hβ : β < α) (s : TSet β) (t : TSet α) (ρ : Allowable α)
    (h : s ∈[hβ] t) :
    comp (Hom.toPath (coe_lt_coe.mpr hβ)) ρ • s ∈[hβ] ρ • t := by
  letI : Level := ⟨α⟩
  letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
  rw [mem, ofCoe_toPretangle_apply_eq hβ] at h
  obtain ⟨s, hs, hs'⟩ := h
  cases toPretangle.injective hs'
  rw [mem, toPretangle_smul, ofCoe_toPretangle_apply_eq hβ]
  refine ⟨(allowableIso α ρ).val β • s, ?_, ?_⟩
  · rw [tSetEquiv_smul]
    change (allowableIso α ρ).val β • s ∈
      (allowableIso α ρ).val β • (tSetEquiv α t).val.members β
    rw [Set.smul_mem_smul_set_iff]
    exact hs
  · rw [toPretangle_smul, allowableIso_apply_eq]

theorem TSet.smul_mem_smul_iff {β α : Λ} (hβ : β < α) (s : TSet β) (t : TSet α) (ρ : Allowable α) :
    comp (Hom.toPath (coe_lt_coe.mpr hβ)) ρ • s ∈[hβ] ρ • t ↔ s ∈[hβ] t := by
  constructor
  · intro h
    have := smul_mem_smul hβ (comp (Hom.toPath (coe_lt_coe.mpr hβ)) ρ • s) (ρ • t) ρ⁻¹ h
    simp only [map_inv, inv_smul_smul] at this
    exact this
  · exact smul_mem_smul hβ s t ρ

theorem TSet.smul_mem_iff {β α : Λ} (hβ : β < α) (s : TSet β) (t : TSet α) (ρ : Allowable α) :
    comp (Hom.toPath (coe_lt_coe.mpr hβ)) ρ • s ∈[hβ] t ↔ s ∈[hβ] ρ⁻¹ • t := by
  have := smul_mem_smul_iff hβ s (ρ⁻¹ • t) ρ
  rw [smul_inv_smul] at this
  exact this

theorem TSet.induction {β α : Λ} (hβ : β < α) (t : TSet α) :
    ∃ s hs, t = TSet.mk hβ s hs := by
  letI : Level := ⟨α⟩
  letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
  refine ⟨{u | u ∈[hβ] t}, ?_, ?_⟩
  · obtain ⟨S, hS⟩ := (tSetEquiv α t).prop
    refine ⟨S, S.small, ?_⟩
    intro ρ hρ
    have := hS (allowableIso α ρ) ?_
    swap
    · intro c hc
      rw [allowableIso_smul_address]
      exact hρ c hc
    have := (congr_arg Subtype.val (tSetEquiv_smul α ρ t)).trans this
    rw [Subtype.coe_inj] at this
    have := (tSetEquiv α).injective this
    ext u
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [← this, Set.mem_setOf_eq, smul_mem_smul_iff]
      exact hu
    · intro hu
      refine ⟨(comp (Hom.toPath (coe_lt_coe.mpr hβ)) ρ)⁻¹ • u, ?_, ?_⟩
      · dsimp only
        rw [← map_inv, Set.mem_setOf_eq, smul_mem_iff, inv_inv, this]
        exact hu
      · simp only [smul_inv_smul]
  · refine ext hβ _ _ ?_
    intro s
    rw [TSet.mem_mk_iff]
    rfl

end ConNF
