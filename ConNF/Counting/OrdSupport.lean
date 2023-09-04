import ConNF.Foa.Basic.Reduction

/-!
# Ordered supports
-/

open Set Sum

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}

structure OrdSupport (β : Iic α) where
  /-- The position of a support condition in this ordered support.
  Named `cpos` instead of `pos` so it doesn't clash with `pos`.

  The support conditions in the domain of an ordered support are well-ordered lexicographically
  first by `cpos` then their paths. -/
  cpos : SupportCondition β →. μ
  injective (c d : SupportCondition β) (hc : (cpos c).Dom) (hd : (cpos d).Dom) :
    c.path = d.path → (cpos c).get hc = (cpos d).get hd → c = d
  dom_small : Small cpos.Dom

namespace OrdSupport

instance : Membership (SupportCondition β) (OrdSupport β) where
  mem c S := (S.cpos c).Dom

theorem mem_iff {S : OrdSupport β} {c : SupportCondition β} :
    c ∈ S ↔ (S.cpos c).Dom :=
  Iff.rfl

@[ext]
theorem ext {S T : OrdSupport β}
    (hdom : ∀ c, c ∈ S ↔ c ∈ T)
    (h : ∀ c hcS hcT, (S.cpos c).get hcS = (T.cpos c).get hcT) :
    S = T := by
  rw [mk.injEq]
  funext c
  exact Part.ext' (hdom c) (h c)

instance : MulAction (StructPerm β) (OrdSupport β) where
  smul π S := {
    cpos := fun c => S.cpos (π⁻¹ • c)
    injective := fun c d hc hd h₁ h₂ =>
      smul_left_cancel _ (S.injective (π⁻¹ • c) (π⁻¹ • d) hc hd h₁ h₂)
    dom_small := by
      refine lt_of_le_of_lt ?_ S.dom_small
      refine ⟨⟨fun c => ⟨π⁻¹ • c.1, c.2⟩, ?_⟩⟩
      rintro ⟨c, hc⟩ ⟨d, hd⟩
      simp only [Subtype.mk.injEq, smul_left_cancel_iff, PFun.dom_mk, coe_setOf, mem_setOf_eq,
        imp_self]
  }
  one_smul S := by
    ext c hc₁ hc₂
    · change (S.cpos _).Dom ↔ (S.cpos _).Dom
      simp only [inv_one, one_smul]
    · change (S.cpos _).get _ = (S.cpos _).get _
      simp only [inv_one, one_smul]
  mul_smul π₁ π₂ S:= by
    ext c hc₁ hc₂
    · change (S.cpos _).Dom ↔ (S.cpos _).Dom
      simp only [mul_inv_rev, mul_smul]
    · change (S.cpos _).get _ = (S.cpos _).get _
      simp only [mul_inv_rev, mul_smul]

@[simp]
theorem _root_.ConNF.StructPerm.smul_mem_ordSupport {π : StructPerm β}
    {S : OrdSupport β} {c : SupportCondition β} :
    c ∈ π • S ↔ π⁻¹ • c ∈ S :=
  Iff.rfl

theorem _root_.ConNF.Allowable.smul_mem_ordSupport {ρ : Allowable β}
    {S : OrdSupport β} {c : SupportCondition β} :
    c ∈ ρ • S ↔ ρ⁻¹ • c ∈ S := by
  simp only [Allowable.toStructPerm_smul, StructPerm.smul_mem_ordSupport, map_inv]

theorem _root_.ConNF.StructPerm.smul_mem_ordSupport_smul {π : StructPerm β}
    {S : OrdSupport β} {c : SupportCondition β} :
    π • c ∈ π • S ↔ c ∈ S := by
  simp only [StructPerm.smul_mem_ordSupport, inv_smul_smul]

theorem _root_.ConNF.Allowable.smul_mem_ordSupport_smul {ρ : Allowable β}
    {S : OrdSupport β} {c : SupportCondition β} :
    ρ • c ∈ ρ • S ↔ c ∈ S := by
  simp only [Allowable.toStructPerm_smul, StructPerm.smul_mem_ordSupport, inv_smul_smul]

@[simp]
theorem _root_.ConNF.StructPerm.smul_cpos {π : StructPerm β}
    {S : OrdSupport β} {c : SupportCondition β} :
    (π • S).cpos c = S.cpos (π⁻¹ • c) :=
  rfl

theorem _root_.ConNF.Allowable.smul_cpos {ρ : Allowable β}
    {S : OrdSupport β} {c : SupportCondition β} :
    (ρ • S).cpos c = S.cpos (ρ⁻¹ • c) := by
  simp only [Allowable.toStructPerm_smul, StructPerm.smul_cpos, map_inv]

theorem _root_.ConNF.StructPerm.smul_cpos_smul {π : StructPerm β}
    {S : OrdSupport β} {c : SupportCondition β} :
    (π • S).cpos (π • c) = S.cpos c := by
  simp only [StructPerm.smul_cpos, inv_smul_smul]

theorem _root_.ConNF.Allowable.smul_cpos_smul {ρ : Allowable β}
    {S : OrdSupport β} {c : SupportCondition β} :
    (ρ • S).cpos (ρ • c) = S.cpos c := by
  simp only [Allowable.toStructPerm_smul, StructPerm.smul_cpos, inv_smul_smul]

theorem _root_.ConNF.StructPerm.smul_mem_ordSupport_inv {π : StructPerm β}
    {S : OrdSupport β} {c : SupportCondition β} :
    c ∈ π⁻¹ • S ↔ π • c ∈ S := by
  rw [mem_iff, mem_iff]
  simp only [StructPerm.smul_cpos, inv_inv]

theorem _root_.ConNF.Allowable.smul_mem_ordSupport_inv {ρ : Allowable β}
    {S : OrdSupport β} {c : SupportCondition β} :
    c ∈ ρ⁻¹ • S ↔ ρ • c ∈ S := by
  rw [mem_iff, mem_iff]
  simp only [Allowable.toStructPerm_smul, map_inv, StructPerm.smul_cpos, inv_inv]

theorem _root_.ConNF.StructPerm.smul_eq_of_smul_ordSupport_eq (π : StructPerm β)
    {S : OrdSupport β} {c : SupportCondition β} (h : c ∈ S) :
    π • S = S → π • c = c := by
  intro hS
  have := congr_arg₂ OrdSupport.cpos hS (refl c)
  refine eq_inv_smul_iff.mp (S.injective c (π⁻¹ • c) h ?_ rfl ?_)
  · rw [← StructPerm.smul_cpos, this]
    exact h
  · rw [StructPerm.smul_cpos] at this
    simp_rw [this]

theorem _root_.ConNF.Allowable.smul_eq_of_smul_ordSupport_eq (ρ : Allowable β)
    {S : OrdSupport β} {c : SupportCondition β} (h : c ∈ S) :
    ρ • S = S → ρ • c = c :=
  (Allowable.toStructPerm ρ).smul_eq_of_smul_ordSupport_eq h

/-- The restriction of this ordered support to conditions that come before position `i`. -/
def before (S : OrdSupport β) (i : μ) : OrdSupport β where
  cpos c := ⟨∃ h : c ∈ S, (S.cpos c).get h < i, fun h => (S.cpos c).get h.1⟩
  injective c d hc hd h := S.injective c d _ _ h
  dom_small := by
    refine Small.mono ?_ S.dom_small
    intro c hc
    exact hc.1

/-- Retains only those support conditions beginning with the path `A`. -/
def comp (S : OrdSupport β) (γ : Iic α) (A : Quiver.Path (β : TypeIndex) γ) : OrdSupport γ where
  cpos c := S.cpos ⟨A.comp c.path, c.value⟩
  injective c d hc hd h₁ h₂ := by
    have := S.injective _ _ _ _ ?_ h₂
    · rw [SupportCondition.mk.injEq] at this ⊢
      rw [Quiver.Path.comp_inj_right] at this
      exact this
    · rw [h₁]
  dom_small := by
    change Small ((fun c : SupportCondition γ => ⟨A.comp c.path, c.value⟩) ⁻¹' S.cpos.Dom)
    refine Small.preimage ?_ S.dom_small
    intro c d h
    rw [SupportCondition.mk.injEq] at h ⊢
    rw [Quiver.Path.comp_inj_right] at h
    exact h

/-- An ordered support is strong if every reduced condition it constrains lies in its domain,
and the position of each support condition is given by the global position function. -/
structure Strong (S : OrdSupport β) : Prop where
  transConstrains_mem (c d : SupportCondition β) : Reduced c → c <[α] d → d ∈ S → c ∈ S
  cpos_get_eq (c : SupportCondition β) (hc : c ∈ S) : (S.cpos c).get hc = pos c.value

attribute [simp] Strong.cpos_get_eq

theorem Strong.cpos_eq {S : OrdSupport β} {c : SupportCondition β} (h : S.Strong) :
    S.cpos c = ⟨c ∈ S, fun _ => pos c.value⟩ := by
  refine Part.ext' Iff.rfl ?_
  intros hc _
  exact h.cpos_get_eq c hc

end OrdSupport

end ConNF
