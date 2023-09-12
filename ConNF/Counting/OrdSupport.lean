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
  cpos : SupportCondition β →. Atom ⊕ NearLitter
  injective (c d : SupportCondition β) (hc : (cpos c).Dom) (hd : (cpos d).Dom) :
    c.path = d.path → (cpos c).get hc = (cpos d).get hd → c = d
  dom_small' : Small cpos.Dom

namespace OrdSupport

instance : Membership (SupportCondition β) (OrdSupport β) where
  mem c S := (S.cpos c).Dom

theorem mem_iff {S : OrdSupport β} {c : SupportCondition β} :
    c ∈ S ↔ (S.cpos c).Dom :=
  Iff.rfl

theorem dom_small (S : OrdSupport β) : Small {c | c ∈ S} :=
  S.dom_small'

@[ext]
theorem ext {S T : OrdSupport β}
    (hdom : ∀ c, c ∈ S ↔ c ∈ T)
    (h : ∀ c hcS hcT, (S.cpos c).get hcS = (T.cpos c).get hcT) :
    S = T := by
  rw [mk.injEq]
  funext c
  exact Part.ext' (hdom c) (h c)

instance : MulAction (Allowable β) (OrdSupport β) where
  smul ρ S := {
    cpos := fun c => S.cpos (ρ⁻¹ • c)
    injective := fun c d hc hd h₁ h₂ =>
      smul_left_cancel _ (S.injective (ρ⁻¹ • c) (ρ⁻¹ • d) hc hd h₁ h₂)
    dom_small' := by
      refine lt_of_le_of_lt ?_ S.dom_small
      refine ⟨⟨fun c => ⟨ρ⁻¹ • c.1, c.2⟩, ?_⟩⟩
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
theorem smul_mem {ρ : Allowable β} {S : OrdSupport β} {c : SupportCondition β} :
    c ∈ ρ • S ↔ ρ⁻¹ • c ∈ S :=
  Iff.rfl

theorem smul_mem_smul {ρ : Allowable β} {S : OrdSupport β} {c : SupportCondition β} :
    ρ • c ∈ ρ • S ↔ c ∈ S := by
  simp only [smul_mem, inv_smul_smul]

@[simp]
theorem smul_cpos {ρ : Allowable β} {S : OrdSupport β} {c : SupportCondition β} :
    (ρ • S).cpos c = S.cpos (ρ⁻¹ • c) :=
  rfl

theorem smul_cpos_smul {ρ : Allowable β} {S : OrdSupport β} {c : SupportCondition β} :
    (ρ • S).cpos (ρ • c) = S.cpos c := by
  simp only [smul_cpos, inv_smul_smul]

theorem smul_mem_inv {ρ : Allowable β} {S : OrdSupport β} {c : SupportCondition β} :
    c ∈ ρ⁻¹ • S ↔ ρ • c ∈ S := by
  simp only [smul_mem, inv_inv]

theorem inv_smul_mem {ρ : Allowable β} {S : OrdSupport β} {c : SupportCondition β} :
    ρ⁻¹ • c ∈ S ↔ c ∈ ρ • S := by
  simp only [smul_mem]

theorem smul_eq_of_smul_eq (ρ : Allowable β) {S : OrdSupport β} {c : SupportCondition β}
    (h : c ∈ S) : ρ • S = S → ρ • c = c := by
  intro hS
  have := congr_arg₂ OrdSupport.cpos hS (refl c)
  refine eq_inv_smul_iff.mp (S.injective c (ρ⁻¹ • c) h ?_ rfl ?_)
  · rw [← smul_cpos, this]
    exact h
  · rw [smul_cpos] at this
    simp_rw [this]

/-- The restriction of this ordered support to conditions that come before position `i`. -/
def before (S : OrdSupport β) (i : Atom ⊕ NearLitter) : OrdSupport β where
  cpos c := ⟨∃ h : c ∈ S, (S.cpos c).get h < i, fun h => (S.cpos c).get h.1⟩
  injective c d hc hd h := S.injective c d _ _ h
  dom_small' := by
    refine Small.mono ?_ S.dom_small
    intro c hc
    exact hc.1

@[simp]
theorem mem_before {S : OrdSupport β} {i : Atom ⊕ NearLitter} (c : SupportCondition β) :
    c ∈ S.before i ↔ ∃ h : c ∈ S, (S.cpos c).get h < i :=
  Iff.rfl

@[simp]
theorem before_get {S : OrdSupport β} {i : Atom ⊕ NearLitter} {c : SupportCondition β}
    (hc : c ∈ S.before i) :
    ((S.before i).cpos c).get hc = (S.cpos c).get hc.1 :=
  rfl

/-- Retains only those support conditions beginning with the path `A`. -/
def comp (S : OrdSupport β) (γ : Iic α) (A : Quiver.Path (β : TypeIndex) γ) : OrdSupport γ where
  cpos c := S.cpos ⟨A.comp c.path, c.value⟩
  injective c d hc hd h₁ h₂ := by
    have := S.injective _ _ _ _ ?_ h₂
    · rw [SupportCondition.mk.injEq] at this ⊢
      rw [Quiver.Path.comp_inj_right] at this
      exact this
    · rw [h₁]
  dom_small' := by
    change Small ((fun c : SupportCondition γ => ⟨A.comp c.path, c.value⟩) ⁻¹' S.cpos.Dom)
    refine Small.preimage ?_ S.dom_small
    intro c d h
    rw [SupportCondition.mk.injEq] at h ⊢
    rw [Quiver.Path.comp_inj_right] at h
    exact h

@[simp]
theorem mem_comp {S : OrdSupport β} (γ : Iic α) (A : Quiver.Path (β : TypeIndex) γ)
    (c : SupportCondition γ) :
    c ∈ S.comp γ A ↔ ⟨A.comp c.path, c.value⟩ ∈ S :=
  Iff.rfl

@[simp]
theorem comp_get {S : OrdSupport β} {γ : Iic α} {A : Quiver.Path (β : TypeIndex) γ}
    {c : SupportCondition γ} (hc : c ∈ S.comp γ A) :
    ((S.comp γ A).cpos c).get hc = (S.cpos ⟨A.comp c.path, c.value⟩).get hc :=
  rfl

/-- An ordered support is strong if every element of its domain is reduced, every reduced condition
it constrains lies in its domain, and the position of each support condition is given by the global
position function. -/
structure Strong (S : OrdSupport β) : Prop where
  reduced_of_mem (c : SupportCondition β) : c ∈ S → Reduced c.value
  transConstrains_mem (c d : SupportCondition β) : Reduced c.value → c <[α] d → d ∈ S → c ∈ S
  cpos_get_eq (c : SupportCondition β) (hc : c ∈ S) : (S.cpos c).get hc = c.value

theorem Strong.cpos_eq {S : OrdSupport β} (h : S.Strong) {c : SupportCondition β} :
    S.cpos c = ⟨c ∈ S, fun _ => c.value⟩ := by
  refine Part.ext' Iff.rfl ?_
  intros hc _
  exact h.cpos_get_eq c hc

theorem Strong.fst_toNearLitter_mem {S : OrdSupport β} (hS : S.Strong)
    {A : ExtendedIndex β} {a : Atom} (h : ⟨A, inl a⟩ ∈ S) :
    ⟨A, inr a.1.toNearLitter⟩ ∈ S :=
  hS.transConstrains_mem _ _
    (Reduced.mkLitter a.1) (Relation.TransGen.single (Constrains.atom A a)) h

theorem Strong.isLitter_of_mem {S : OrdSupport β} (hS : S.Strong)
    {A : ExtendedIndex β} {N : NearLitter} (h : ⟨A, inr N⟩ ∈ S) :
    N.IsLitter := by
  cases hS.reduced_of_mem _ h
  exact NearLitter.IsLitter.mk _

end OrdSupport

end ConNF
