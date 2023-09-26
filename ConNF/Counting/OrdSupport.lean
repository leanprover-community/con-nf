import ConNF.Foa.Basic.Reduction

/-!
# Ordered supports
-/

open Set Sum

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}

structure OrdSupport (β : Iic α) where
  /-- The set of support conditions in this ordered support. -/
  carrier : Set (SupportCondition β)
  /-- The carrier set is small. -/
  carrier_small : Small carrier
  /-- An order on `carrier`. -/
  r : carrier → carrier → Prop
  /-- `r` is a well order. -/
  r_isWellOrder : IsWellOrder carrier r

namespace OrdSupport

variable {S : OrdSupport β}

instance : CoeTC (OrdSupport β) (Set (SupportCondition β)) where
  coe := OrdSupport.carrier

instance : Membership (SupportCondition β) (OrdSupport β) where
  mem c S := c ∈ S.carrier

instance : CoeSort (OrdSupport β) (Type _) :=
  ⟨fun S => { x : SupportCondition β // x ∈ S }⟩

instance : HasSubset (OrdSupport β) where
  Subset S T := ∀ ⦃c : SupportCondition β⦄, c ∈ S → c ∈ T

@[simp, norm_cast]
theorem coe_sort_coe (S : OrdSupport β) : ((S : Set (SupportCondition β)) : Type _) = S :=
  rfl

theorem small (S : OrdSupport β) : Small (S : Set (SupportCondition β)) :=
  S.carrier_small

instance isWellOrder (S : OrdSupport β) : IsWellOrder S S.r := S.r_isWellOrder

instance : PartialOrder S := partialOrderOfSO S.r

open scoped Classical in
noncomputable instance : LinearOrder S := linearOrderOfSTO S.r

@[ext]
theorem ext {S T : OrdSupport β} (h₁ : S ⊆ T) (h₂ : T ⊆ S)
    (h : ∀ c d : S, c < d ↔ (⟨c, h₁ c.prop⟩ : T) < ⟨d, h₁ d.prop⟩) :
    S = T := by
  obtain ⟨S, _, r, _⟩ := S
  obtain ⟨T, _, s, _⟩ := T
  cases subset_antisymm (show (S : Set (SupportCondition β)) ⊆ T from h₁) h₂
  simp only [mk.injEq, heq_eq_eq, true_and]
  ext c d
  exact h c d

instance : SMul (Allowable β) (OrdSupport β) where
  smul ρ S := {
    carrier := {c | ρ⁻¹ • c ∈ S}
    carrier_small := Small.preimage (MulAction.injective ρ⁻¹) S.small
    r := fun c d => (⟨ρ⁻¹ • c.val, c.prop⟩ : S) < ⟨ρ⁻¹ • d.val, d.prop⟩
    r_isWellOrder := by
      refine isWellOrder_invImage S.isWellOrder
        (fun c : {c // ρ⁻¹ • c ∈ S} => ⟨ρ⁻¹ • c.val, c.prop⟩) ?_
      intros c d h
      simp only [Subtype.mk.injEq, smul_left_cancel_iff, Subtype.coe_injective.eq_iff] at h
      exact h
  }

@[simp]
theorem smul_mem {ρ : Allowable β} {S : OrdSupport β} {c : SupportCondition β} :
    c ∈ ρ • S ↔ ρ⁻¹ • c ∈ S :=
  Iff.rfl

theorem inv_smul_mem {ρ : Allowable β} {S : OrdSupport β} {c : SupportCondition β} :
    ρ⁻¹ • c ∈ S ↔ c ∈ ρ • S :=
  smul_mem.symm

theorem smul_mem_smul {ρ : Allowable β} {S : OrdSupport β} {c : SupportCondition β} :
    ρ • c ∈ ρ • S ↔ c ∈ S := by
  simp only [smul_mem, inv_smul_smul]

theorem smul_mem_inv {ρ : Allowable β} {S : OrdSupport β} {c : SupportCondition β} :
    c ∈ ρ⁻¹ • S ↔ ρ • c ∈ S := by
  simp only [smul_mem, inv_inv]

@[simp]
theorem lt_iff_smul {ρ : Allowable β} {S : OrdSupport β} {c d : ρ • S} :
    c < d ↔ (⟨ρ⁻¹ • c.val, c.prop⟩ : S) < ⟨ρ⁻¹ • d.val, d.prop⟩ :=
  Iff.rfl

instance : MulAction (Allowable β) (OrdSupport β) where
  one_smul S := by
    refine ext ?_ ?_ ?_
    · intro c hc
      simp only [smul_mem, inv_one, one_smul] at hc
      exact hc
    · intro c hc
      simp only [smul_mem, inv_one, one_smul]
      exact hc
    · intro c d
      simp only [lt_iff_smul, inv_one, one_smul]
  mul_smul ρ₁ ρ₂ S := by
    refine ext ?_ ?_ ?_
    · intro c hc
      simp only [smul_mem, mul_inv_rev, mul_smul] at hc
      exact hc
    · intro c hc
      simp only [smul_mem, mul_inv_rev, mul_smul]
      exact hc
    · intro c d
      simp only [lt_iff_smul, mul_inv_rev, mul_smul]

/-- An ordered support is strong if every element of its domain is reduced, every reduced condition
it constrains lies in its domain, and its order agrees with the constrains relation. -/
structure Strong (S : OrdSupport β) : Prop where
  reduced_of_mem (c : S) : Reduced c.val.value
  transConstrains_mem (c : SupportCondition β) (d : S) : Reduced c.value → c <[α] d → c ∈ S
  lt_of_transConstrains : (c d : S) → c.val <[α] d.val → c < d

/-- `T` *extends* `S` if it is a well-order that end-extends `S`. -/
structure Extends (T S : OrdSupport β) : Prop where
  mem_of_mem (c : S) : c.val ∈ T
  lt_iff_lt (c d : S) :
    c < d ↔ (⟨c, mem_of_mem c⟩ : T) < ⟨d, mem_of_mem d⟩
  /-- If `c` is in `S ∩ T` and `d` is in `T \ S`, then `c` comes before `d`. -/
  get_lt_get (c : S) (d : T) (hd : d.val ∉ S) :
    ⟨c, mem_of_mem c⟩ < d

instance : LE (OrdSupport β) where
  le S T := Extends T S

instance : PartialOrder (OrdSupport β) where
  le_refl S := by
    constructor
    · intro c hc
      rfl
    · intro c d hd
      cases hd d.prop
  le_trans S T U hST hTU := by
    constructor
    · intro c d
      rw [hST.lt_iff_lt, hTU.lt_iff_lt]
    · intro c d hdS
      by_cases hdT : d.val ∈ T
      · have := hST.get_lt_get c ⟨d, hdT⟩ hdS
        rw [hTU.lt_iff_lt] at this
        exact this
      · have := hTU.get_lt_get ⟨c, hST.mem_of_mem c⟩ d hdT
        exact this
  le_antisymm S T hST hTS := by
    refine ext (fun c hc => hST.mem_of_mem ⟨c, hc⟩) (fun c hc => hTS.mem_of_mem ⟨c, hc⟩) ?_
    intro c d
    rw [hST.lt_iff_lt]

theorem smul_le_smul {S T : OrdSupport β} (h : S ≤ T) (ρ : Allowable β) : ρ • S ≤ ρ • T := by
  constructor
  · intro c d
    exact h.lt_iff_lt ⟨ρ⁻¹ • c.val, c.prop⟩ ⟨ρ⁻¹ • d.val, d.prop⟩
  · intro c d
    exact h.get_lt_get ⟨ρ⁻¹ • c.val, c.prop⟩ ⟨ρ⁻¹ • d.val, d.prop⟩
  · intro c
    exact h.mem_of_mem ⟨ρ⁻¹ • c.val, c.prop⟩

theorem smul_le_iff_le_inv {S T : OrdSupport β} (ρ : Allowable β) : S ≤ ρ⁻¹ • T ↔ ρ • S ≤ T := by
  constructor
  · intro h
    have := smul_le_smul h ρ
    rw [smul_inv_smul] at this
    exact this
  · intro h
    have := smul_le_smul h ρ⁻¹
    rw [inv_smul_smul] at this
    exact this

end OrdSupport

end ConNF
