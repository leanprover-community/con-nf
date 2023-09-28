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

@[simp]
theorem mem_carrier_iff {c : SupportCondition β} : c ∈ S.carrier ↔ c ∈ S :=
  Iff.rfl

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

noncomputable def recursion {motive : S → Sort _} (c : S)
    (h : (c : S) → ((d : S) → d < c → motive d) → motive c) :
    motive c :=
  S.isWellOrder.wf.recursion c h

theorem induction {motive : S → Prop} (c : S)
    (h : (c : S) → ((d : S) → d < c → motive d) → motive c) :
    motive c :=
  S.isWellOrder.wf.induction c h

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

theorem lt_iff_smul' {S : OrdSupport β} {c d : S} (ρ : Allowable β) :
    c < d ↔
    (⟨ρ • c.val, smul_mem_smul.mpr c.prop⟩ : ρ • S) < ⟨ρ • d.val, smul_mem_smul.mpr d.prop⟩ := by
  simp only [lt_iff_smul, inv_smul_smul, Subtype.coe_eta]

theorem lt_iff_lt_of_smul_eq {S T : OrdSupport β} (c d : T) (h : S = T)
    (hc : c.val ∈ S) (hd : d.val ∈ S) :
    (⟨c, hc⟩ : S) < ⟨d, hd⟩ ↔ c < d := by
  subst h
  rfl

theorem smul_eq_of_smul_eq (ρ : Allowable β) {S : OrdSupport β} (c : S) :
    ρ • S = S → ρ • c.val = c.val := by
  intro hS
  refine S.induction (motive := fun c => ρ • c.val = c.val) c ?_
  intro c ih
  have hc : ρ • c.val ∈ S
  · conv_rhs => rw [← hS]
    exact smul_mem_smul.mpr c.prop
  have hc' : c.val ∈ ρ • S
  · rw [hS]
    exact c.prop
  obtain (h | h | h) := lt_trichotomy ⟨ρ • c.val, hc⟩ c
  · have := ih ⟨ρ • c.val, hc⟩ h
    simp only [smul_left_cancel_iff] at this
    exact this
  · exact congr_arg Subtype.val h
  · have := ih ⟨ρ⁻¹ • c.val, hc'⟩ ?_
    · simp only [smul_inv_smul] at this
      conv_lhs => rw [this, smul_inv_smul]
    · rw [lt_iff_smul' ρ]
      simp only [smul_inv_smul]
      rw [lt_iff_lt_of_smul_eq c ⟨ρ • c.val, _⟩ hS]
      exact h

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

/-- The restriction of this ordered support to conditions that come before position `i`. -/
def before (S : OrdSupport β) (i : Ordinal.{u}) : OrdSupport β where
  carrier := {c | ∃ hc : c ∈ S, Ordinal.typein S.r ⟨c, hc⟩ < i}
  carrier_small := Small.mono (fun c hc => hc.1) S.small
  r c d := (⟨c, c.prop.1⟩ : S) < ⟨d, d.prop.1⟩
  r_isWellOrder := by
    refine isWellOrder_invImage S.isWellOrder _ ?_
    intro c d h
    simp only [coe_sort_coe, mem_setOf_eq, Subtype.mk.injEq] at h
    exact Subtype.coe_injective h

@[simp]
theorem mem_before {S : OrdSupport β} {i : Ordinal} (c : SupportCondition β) :
    c ∈ S.before i ↔ ∃ hc : c ∈ S, Ordinal.typein S.r ⟨c, hc⟩ < i :=
  Iff.rfl

@[simp]
theorem before_lt {S : OrdSupport β} {i : Ordinal} (c d : S.before i) :
    c < d ↔ (⟨c, c.prop.1⟩ : S) < ⟨d, d.prop.1⟩ :=
  Iff.rfl

/-- Retains only those support conditions beginning with the path `A`. -/
def comp (S : OrdSupport β) (γ : Iic α) (A : Quiver.Path (β : TypeIndex) γ) : OrdSupport γ where
  carrier := {c | ⟨A.comp c.path, c.value⟩ ∈ S}
  carrier_small := by
    refine S.small.preimage ?_
    intro c d h
    rw [SupportCondition.mk.injEq, Quiver.Path.comp_inj_right] at h
    exact SupportCondition.ext _ _ h.1 h.2
  r := InvImage (· < ·) (fun c => (⟨_, c.prop⟩ : S))
  r_isWellOrder := by
    refine isWellOrder_invImage S.isWellOrder _ ?_
    intro c d h
    simp only [mem_setOf_eq, Subtype.mk.injEq, SupportCondition.mk.injEq] at h
    rw [Quiver.Path.comp_inj_right] at h
    exact Subtype.coe_injective (SupportCondition.ext _ _ h.1 h.2)

@[simp]
theorem mem_comp {S : OrdSupport β} (γ : Iic α) (A : Quiver.Path (β : TypeIndex) γ)
    (c : SupportCondition γ) :
    c ∈ S.comp γ A ↔ ⟨A.comp c.path, c.value⟩ ∈ S :=
  Iff.rfl

@[simp]
theorem comp_lt {S : OrdSupport β} {γ : Iic α} {A : Quiver.Path (β : TypeIndex) γ}
    {c d : S.comp γ A} :
    c < d ↔
    (⟨⟨A.comp c.val.path, c.val.value⟩, c.prop⟩ : S) < ⟨⟨A.comp d.val.path, d.val.value⟩, d.prop⟩ :=
  Iff.rfl

/-- An ordered support is strong if every element of its domain is reduced, every reduced condition
it constrains lies in its domain, and its order agrees with the constrains relation. -/
structure Strong (S : OrdSupport β) : Prop where
  reduced_of_mem (c : S) : Reduced c.val.value
  transConstrains_mem (c : SupportCondition β) (d : S) : Reduced c.value → c <[α] d → c ∈ S
  lt_of_transConstrains : (c d : S) → c.val <[α] d.val → c < d

theorem Strong.fst_toNearLitter_mem {S : OrdSupport β} (hS : S.Strong)
    {A : ExtendedIndex β} {a : Atom} (h : ⟨A, inl a⟩ ∈ S) :
    ⟨A, inr a.1.toNearLitter⟩ ∈ S :=
  hS.transConstrains_mem _ ⟨_, h⟩
    (Reduced.mkLitter a.1) (Relation.TransGen.single (Constrains.atom A a))

theorem Strong.before {S : OrdSupport β} (h : S.Strong) (i : Ordinal) :
    (S.before i).Strong := by
  constructor
  case reduced_of_mem =>
    intro c
    exact h.reduced_of_mem ⟨c.val, c.prop.1⟩
  case transConstrains_mem =>
    intro c d hc hcd
    refine ⟨h.transConstrains_mem c ⟨d.val, d.prop.1⟩ hc hcd, ?_⟩
    refine lt_trans ?_ d.prop.2
    rw [Ordinal.typein_lt_typein]
    exact h.lt_of_transConstrains _ _ hcd
  case lt_of_transConstrains =>
    intro c d hcd
    exact h.lt_of_transConstrains _ _ hcd

theorem Strong.comp {S : OrdSupport β} (h : S.Strong)
    (γ : Iic α) (A : Quiver.Path (β : TypeIndex) γ) :
    (S.comp γ A).Strong := by
  constructor
  case reduced_of_mem =>
    intro c
    exact h.reduced_of_mem ⟨_, c.prop⟩
  case transConstrains_mem =>
    intro c d hc hcd
    exact h.transConstrains_mem _ ⟨_, d.prop⟩ hc (transConstrains_comp hcd _)
  case lt_of_transConstrains =>
    intro c d hcd
    exact h.lt_of_transConstrains _ _ (transConstrains_comp hcd _)

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

theorem subset_or_subset_of_le {S₁ S₂ T : OrdSupport β}
    (h₁ : S₁ ≤ T) (h₂ : S₂ ≤ T) :
    (∀ c, c ∈ S₁ → c ∈ S₂) ∨ (∀ c, c ∈ S₂ → c ∈ S₁) := by
  rw [or_iff_not_imp_left]
  intro h c hc₂
  by_contra hc₁
  simp only [not_forall, exists_prop] at h
  obtain ⟨d, hd₁, hd₂⟩ := h
  have h₁' := h₁.get_lt_get ⟨d, hd₁⟩ ⟨c, h₂.mem_of_mem ⟨c, hc₂⟩⟩ hc₁
  have h₂' := h₂.get_lt_get ⟨c, hc₂⟩ ⟨d, h₁.mem_of_mem ⟨d, hd₁⟩⟩ hd₂
  exact not_lt_of_lt h₁' h₂'

/-- If `ρ` maps `S` to an initial segment of itself, it is an order isomorphism. -/
theorem lt_iff_lt_of_le {S T : OrdSupport β} {ρ : Allowable β}
    (h₁ : ρ • S ≤ T) (h₂ : S ≤ T) (h : ∀ c, c ∈ S → ρ • c ∈ S)
    (c d : S) :
    c < d ↔ (⟨ρ • c.val, h c c.prop⟩ : S) < ⟨ρ • d.val, h d d.prop⟩ :=
  by rw [lt_iff_smul' ρ, h₁.lt_iff_lt, h₂.lt_iff_lt]

/-- If `ρ` maps `S` to an initial segment of itself, it is the identity function. -/
theorem smul_eq_of_le' {S T : OrdSupport β} {ρ : Allowable β}
    (h₁ : ρ • S ≤ T) (h₂ : S ≤ T)
    (h : ∀ c, c ∈ S → ρ • c ∈ S)
    (c : S) : ρ • c.val = c.val := by
  refine S.induction (motive := fun c => ρ • c.val = c.val) c ?_
  intro c ih
  have hc' : c.val ∈ ρ • S
  · by_contra hc''
    have := h₁.get_lt_get ⟨ρ • c.val, smul_mem_smul.mpr c.prop⟩ ⟨c, h₂.mem_of_mem c⟩ hc''
    rw [← h₂.lt_iff_lt ⟨ρ • c.val, h c c.prop⟩ c] at this
    have h := ih ⟨ρ • c.val, h c c.prop⟩ this
    simp only [smul_left_cancel_iff] at h
    simp_rw [h] at this
    exact this.false
  obtain (hc | hc | hc) := lt_trichotomy ⟨ρ • c.val, h c c.prop⟩ c
  · have := ih ⟨ρ • c.val, h c c.prop⟩ hc
    simp only [smul_left_cancel_iff] at this
    simp_rw [this] at hc
    cases ne_of_lt hc rfl
  · exact congr_arg Subtype.val hc
  · have := lt_iff_lt_of_le h₁ h₂ h ⟨ρ⁻¹ • c.val, hc'⟩ c
    simp only [smul_inv_smul, Subtype.coe_eta, hc, iff_true] at this
    have h := ih _ this
    simp only [smul_inv_smul] at h
    simp_rw [← h] at this
    cases ne_of_lt this rfl

/-- `ρ` is an order isomorphism. -/
theorem smul_eq_of_le {S T : OrdSupport β} {ρ : Allowable β}
    (h₁ : ρ • S ≤ T) (h₂ : S ≤ T)
    (c : S) : ρ • c.val = c.val := by
  obtain (h | h) := subset_or_subset_of_le h₁ h₂
  · refine smul_eq_of_le' h₁ h₂ ?_ c
    intro c hc
    exact h (ρ • c) (smul_mem_smul.mpr hc)
  · have := smul_eq_of_le' (ρ := ρ⁻¹) (by rwa [inv_smul_smul]) h₁ ?_
        ⟨ρ • c.val, smul_mem_smul.mpr c.prop⟩
    · simp only [inv_smul_smul] at this
      exact this.symm
    · intro c hc
      exact h (ρ⁻¹ • c) hc

theorem eq_of_le {S T : OrdSupport β} {ρ : Allowable β}
    (h₁ : ρ • S ≤ T) (h₂ : S ≤ T) : ρ • S = S := by
  refine ext ?_ ?_ ?_
  · intro c hc
    have := smul_eq_of_le h₁ h₂ ⟨ρ⁻¹ • c, hc⟩
    rw [smul_inv_smul] at this
    rw [this]
    exact hc
  · intro c hc
    have := smul_eq_of_le h₁ h₂ ⟨c, hc⟩
    dsimp only at this
    rw [smul_mem, ← this, inv_smul_smul]
    exact hc
  · intro c d
    rw [h₁.lt_iff_lt, h₂.lt_iff_lt]

end OrdSupport

end ConNF
