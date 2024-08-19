import ConNF.Model.Redefinitions

open Quiver WithBot

open scoped Pointwise

universe u

noncomputable section

namespace ConNF

variable [Params.{u}]

def mem {β α : Λ} (h : β < α) (tβ : TSet β) (tα : TSet α) : Prop :=
  toStructSet tβ ∈ StructSet.ofCoe (toStructSet tα) β (coe_lt_coe.mpr h)

notation:50 tβ:50 " ∈[" h:50 "] " tα:50 => mem h tβ tα

theorem tSet_mk_aux {β α : Λ} (hβ : β < α) (s : Set (TSet β))
    (hs : ∃ S : Set (Address α), Small S ∧
      ∀ ρ : Allowable α, (∀ c ∈ S, ρ • c = c) →
      cons hβ ρ • s = s) :
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

def Symmetric {β α : Λ} (hβ : β < α) (s : Set (TSet β)) : Prop :=
  ∃ S : Set (Address α), Small S ∧
    ∀ ρ : Allowable α, (∀ c ∈ S, ρ • c = c) →
    cons hβ ρ • s = s

theorem Symmetric.ofSubset {β α : Λ} (hβ : β < α) (s : Set (TSet β)) :
    (∃ S : Set (Address α), Small S ∧
      ∀ ρ : Allowable α, (∀ c ∈ S, ρ • c = c) →
      cons hβ ρ • s ⊆ s) → Symmetric hβ s := by
  rintro ⟨S, hS₁, hS₂⟩
  refine ⟨S, hS₁, ?_⟩
  intro ρ hρ
  refine subset_antisymm (hS₂ ρ hρ) ?_
  have := hS₂ ρ⁻¹  ?_
  · intro c hc
    have := this ⟨c, hc, rfl⟩
    refine ⟨_, this, ?_⟩
    simp only [map_inv, smul_inv_smul]
  · intro c hc
    conv_lhs => rw [← hρ c hc, inv_smul_smul]

namespace ModelData.TSet

def mk {β α : Λ} (hβ : β < α) (s : Set (TSet β)) (hs : Symmetric hβ s) : TSet α :=
  letI : Level := ⟨α⟩
  letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
  (tSetEquiv α).symm (NewTSet.intro s (tSet_mk_aux hβ s hs))

theorem toStructSet_eq {α : Λ} (t : TSet α) :
    toStructSet t = letI : Level := ⟨α⟩; NewTSet.toStructSet (tSetEquiv α t) := by
  rw [← tSetEquiv_toStructSet α t]
  rfl

theorem mem_tSetEquiv_iff {β α : Λ} (hβ : β < α) (s : TSet β) (t : TSet α) :
    s ∈[hβ] t ↔
      letI : Level := ⟨α⟩
      toStructSet s ∈
        StructSet.ofCoe (NewTSet.toStructSet (tSetEquiv α t)) β (coe_lt_coe.mpr hβ) := by
  rw [mem, toStructSet_eq t]
  rfl

theorem ofCoe_toStructSet_apply_eq {β α : Λ} (hβ : β < α) (t : TSet α) :
    StructSet.ofCoe (toStructSet t) β (coe_lt_coe.mpr hβ) =
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
    {p | ∃ s ∈ (tSetEquiv α t).val.members β, toStructSet s = p} := by
  letI : Level := ⟨α⟩
  letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
  rw [toStructSet_eq t, NewTSet.toStructSet]
  exact congr_fun₂ (ExtensionalSet.toStructSet_ofCoe (tSetEquiv α t).val) β (coe_lt_coe.mpr hβ)

@[simp]
theorem mem_mk_iff {β α : Λ} (hβ : β < α) (s : Set (TSet β)) (hs : Symmetric hβ s) (t : TSet β) :
    t ∈[hβ] mk hβ s hs ↔ t ∈ s := by
  letI : Level := ⟨α⟩
  letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
  have := NewTSet.intro_members s (tSet_mk_aux hβ s hs)
  rw [mem, ofCoe_toStructSet_apply_eq hβ]
  simp only [Set.mem_setOf_eq, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
  rw [mk, Equiv.apply_symm_apply, this]

theorem eq_toStructSet_of_mem {β α : Λ} (hβ : β < α) (t₁ : TSet α) (t₂ : StructSet β) :
    letI : Level := ⟨α⟩
    t₂ ∈ StructSet.ofCoe (NewTSet.toStructSet (tSetEquiv α t₁)) β (coe_lt_coe.mpr hβ) →
    ∃ t₂' : TSet β, t₂ = toStructSet t₂' := by
  intro h
  simp only [NewTSet.toStructSet, ExtensionalSet.toStructSet, Equiv.apply_symm_apply] at h
  obtain ⟨s, _, hs⟩ := h
  exact ⟨s, hs.symm⟩

theorem ext {β α : Λ} (hβ : β < α) (t₁ t₂ : TSet α) :
    (∀ s, s ∈[hβ] t₁ ↔ s ∈[hβ] t₂) → t₁ = t₂ := by
  intro h
  letI : Level := ⟨α⟩
  letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
  refine (tSetEquiv α).injective (NewTSet.ext β (tSetEquiv α t₁) (tSetEquiv α t₂) ?_)
  intro p
  simp_rw [TSet.mem_tSetEquiv_iff hβ] at h
  constructor
  · intro hp
    obtain ⟨s, rfl⟩ := eq_toStructSet_of_mem hβ t₁ p hp
    exact (h s).mp hp
  · intro hp
    obtain ⟨s, rfl⟩ := eq_toStructSet_of_mem hβ t₂ p hp
    exact (h s).mpr hp

theorem smul_mem_smul {β α : Λ} (hβ : β < α) (s : TSet β) (t : TSet α) (ρ : Allowable α)
    (h : s ∈[hβ] t) :
    cons hβ ρ • s ∈[hβ] ρ • t := by
  letI : Level := ⟨α⟩
  letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
  rw [mem, ofCoe_toStructSet_apply_eq hβ] at h
  obtain ⟨s, hs, hs'⟩ := h
  cases toStructSet.injective hs'
  rw [mem, toStructSet_smul, ofCoe_toStructSet_apply_eq hβ]
  refine ⟨(allowableIso α ρ).val β • s, ?_, ?_⟩
  · rw [tSetEquiv_smul]
    change (allowableIso α ρ).val β • s ∈
      (allowableIso α ρ).val β • (tSetEquiv α t).val.members β
    rw [Set.smul_mem_smul_set_iff]
    exact hs
  · rw [toStructSet_smul, allowableIso_apply_eq (coe_lt_coe.mpr hβ)]
    rfl

theorem smul_mem_smul_iff {β α : Λ} (hβ : β < α) (s : TSet β) (t : TSet α) (ρ : Allowable α) :
    cons hβ ρ • s ∈[hβ] ρ • t ↔ s ∈[hβ] t := by
  constructor
  · intro h
    have := smul_mem_smul hβ (cons hβ ρ • s) (ρ • t) ρ⁻¹ h
    simp only [map_inv, inv_smul_smul] at this
    exact this
  · exact smul_mem_smul hβ s t ρ

theorem smul_mem_iff {β α : Λ} (hβ : β < α) (s : TSet β) (t : TSet α) (ρ : Allowable α) :
    cons hβ ρ • s ∈[hβ] t ↔ s ∈[hβ] ρ⁻¹ • t := by
  have := smul_mem_smul_iff hβ s (ρ⁻¹ • t) ρ
  rw [smul_inv_smul] at this
  exact this

theorem mem_smul_iff {β α : Λ} (hβ : β < α) (s : TSet β) (t : TSet α) (ρ : Allowable α) :
    s ∈[hβ] ρ • t ↔ (cons hβ ρ)⁻¹ • s ∈[hβ] t := by
  have := smul_mem_smul_iff hβ (cons hβ ρ⁻¹ • s) t ρ
  simp only [map_inv, smul_inv_smul] at this
  exact this

theorem exists_support {α : Λ} (t : TSet α) :
    ∃ S : Set (Address α), Small S ∧ MulAction.Supports (Allowable α) S t := by
  obtain ⟨S, hS⟩ := (tSetEquiv α t).prop
  refine ⟨S, S.small, ?_⟩
  intro ρ hρ
  have := hS (allowableIso α ρ) ?_
  · have := (congr_arg Subtype.val (tSetEquiv_smul α ρ t)).trans this
    rw [Subtype.coe_inj] at this
    exact (tSetEquiv α).injective this
  · intro a ha
    rw [allowableIso_smul_address]
    exact hρ ha

theorem induction {β α : Λ} (hβ : β < α) (t : TSet α) :
    ∃ s hs, t = mk hβ s hs := by
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
      refine ⟨(cons hβ ρ)⁻¹ • u, ?_, ?_⟩
      · dsimp only
        rw [← map_inv, Set.mem_setOf_eq, smul_mem_iff, inv_inv, this]
        exact hu
      · simp only [smul_inv_smul]
  · refine ext hβ _ _ ?_
    intro s
    rw [TSet.mem_mk_iff]
    rfl

end ModelData.TSet

theorem Small.symmetric {β α : Λ} {s : Set (TSet β)} (hs : Small s) (hβ : β < α) :
    Symmetric hβ s := by
  have := ModelData.TSet.exists_support (α := β)
  choose S hS₁ hS₂ using this
  refine ⟨⋃ t ∈ s, raise (coe_lt_coe.mpr hβ) '' S t, ?_, ?_⟩
  · refine Small.bUnion hs ?_
    intro t _
    exact Small.image (hS₁ t)
  · intro ρ hρ
    ext t
    constructor
    · rintro ⟨t, ht, rfl⟩
      have := hS₂ t (cons hβ ρ) ?_
      · dsimp only
        rw [this]
        exact ht
      · intro c hc
        have := hρ (raise (coe_lt_coe.mpr hβ) c) ⟨_, ⟨t, rfl⟩, _, ⟨ht, rfl⟩, c, hc, rfl⟩
        simp only [raise, raiseIndex, Allowable.smul_address_eq_iff] at this
        simp only [Allowable.smul_address_eq_iff, cons_toStructPerm, Tree.comp_apply]
        exact this
    · intro ht
      have := hS₂ t (cons hβ ρ) ?_
      · rw [← this, Set.smul_mem_smul_set_iff]
        exact ht
      · intro c hc
        have := hρ (raise (coe_lt_coe.mpr hβ) c) ⟨_, ⟨t, rfl⟩, _, ⟨ht, rfl⟩, c, hc, rfl⟩
        simp only [raise, raiseIndex, Allowable.smul_address_eq_iff] at this
        simp only [Allowable.smul_address_eq_iff, cons_toStructPerm, Tree.comp_apply]
        exact this

end ConNF
