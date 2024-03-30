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

theorem TSet.mem_mk_iff {β α : Λ} (hβ : β < α) (s : Set (TSet β))
    (hs : ∃ S : Set (Address α), Small S ∧
      ∀ ρ : Allowable α, (∀ c ∈ S, ρ • c = c) →
      comp (Hom.toPath (coe_lt_coe.mpr hβ)) ρ • s = s) (t : TSet β) :
    t ∈[hβ] TSet.mk hβ s hs ↔ t ∈ s := by
  letI : Level := ⟨α⟩
  letI : LtLevel β := ⟨coe_lt_coe.mpr hβ⟩
  have := NewTSet.intro_members s (tSet_mk_aux hβ s hs)
  rw [mem, ← tSetEquiv_toPretangle α (TSet.mk hβ s hs)]
  sorry

end ConNF
