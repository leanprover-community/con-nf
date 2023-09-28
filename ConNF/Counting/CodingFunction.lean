import ConNF.Counting.OrdSupport

/-!
# Coding functions
-/

open MulAction Set Sum

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}

structure CodingFunction (β : Iic α) where
  decode : OrdSupport β →. Tangle β
  dom_nonempty : decode.Dom.Nonempty
  supports_decode' (S : OrdSupport β) (hS : (decode S).Dom) :
    Supports (Allowable β) (S : Set (SupportCondition β)) ((decode S).get hS)
  dom_iff (S T : OrdSupport β) (hS : (decode S).Dom) :
    (decode T).Dom ↔ ∃ ρ : Allowable β, T = ρ • S
  decode_smul' (S : OrdSupport β) (ρ : Allowable β)
    (h₁ : (decode S).Dom) (h₂ : (decode (ρ • S)).Dom) :
    (decode (ρ • S)).get h₂ = ρ • (decode S).get h₁

namespace CodingFunction

instance : Membership (OrdSupport β) (CodingFunction β) where
  mem S χ := (χ.decode S).Dom

theorem mem_iff {χ : CodingFunction β} {S : OrdSupport β} :
    S ∈ χ ↔ (χ.decode S).Dom :=
  Iff.rfl

theorem mem_iff_of_mem {χ : CodingFunction β} {S T : OrdSupport β} (h : S ∈ χ) :
    T ∈ χ ↔ ∃ ρ : Allowable β, T = ρ • S :=
  χ.dom_iff S T h

theorem smul_mem {χ : CodingFunction β} {S : OrdSupport β} (ρ : Allowable β) (h : S ∈ χ) :
    ρ • S ∈ χ :=
  (χ.mem_iff_of_mem h).mpr ⟨ρ, rfl⟩

theorem mem_of_smul_mem {χ : CodingFunction β} {S : OrdSupport β} {ρ : Allowable β}
    (h : ρ • S ∈ χ) : S ∈ χ :=
  (χ.mem_iff_of_mem h).mpr ⟨ρ⁻¹, by rw [inv_smul_smul]⟩

theorem exists_mem (χ : CodingFunction β) :
    ∃ S, S ∈ χ :=
  χ.dom_nonempty

theorem supports_decode {χ : CodingFunction β} (S : OrdSupport β) (hS : S ∈ χ) :
    Supports (Allowable β) (S : Set (SupportCondition β)) ((χ.decode S).get hS) :=
  χ.supports_decode' S hS

theorem decode_smul {χ : CodingFunction β} (S : OrdSupport β) (ρ : Allowable β) (h : ρ • S ∈ χ) :
    (χ.decode (ρ • S)).get h = ρ • (χ.decode S).get (mem_of_smul_mem h) :=
  χ.decode_smul' S ρ _ _

/-- Two coding functions are equal if they decode a single ordered support to the same tangle. -/
theorem ext {χ₁ χ₂ : CodingFunction β}
    (S : OrdSupport β) (h₁ : S ∈ χ₁) (h₂ : S ∈ χ₂)
    (h : (χ₁.decode S).get h₁ = (χ₂.decode S).get h₂) :
    χ₁ = χ₂ := by
  rw [mk.injEq]
  funext T
  refine Part.ext' ?_ ?_
  · rw [← mem_iff, mem_iff_of_mem h₁, ← mem_iff, mem_iff_of_mem h₂]
  · intros h₁' h₂'
    rw [← mem_iff, mem_iff_of_mem h₁] at h₁'
    obtain ⟨ρ, rfl⟩ := h₁'
    rw [χ₁.decode_smul' S ρ h₁ h₁', χ₂.decode_smul' S ρ h₂ h₂', h]

theorem smul_supports {S : OrdSupport β} {t : Tangle β}
    (h : Supports (Allowable β) (S : Set (SupportCondition β)) t) (ρ : Allowable β) :
    Supports (Allowable β) (ρ • S : Set (SupportCondition β)) (ρ • t) := by
  intro ρ' hρ'
  have := h (ρ⁻¹ * ρ' * ρ) ?_
  · rw [mul_assoc, mul_smul, inv_smul_eq_iff, mul_smul] at this
    exact this
  intros c hc
  rw [mul_assoc, mul_smul, inv_smul_eq_iff, mul_smul]
  refine hρ' ?_
  simp only [OrdSupport.mem_carrier_iff, OrdSupport.smul_mem, inv_smul_smul]
  exact hc

theorem decode_congr {χ : CodingFunction β} {S₁ S₂ : OrdSupport β}
    {h₁ : S₁ ∈ χ} {h₂ : S₂ ∈ χ} (h : S₁ = S₂) :
    (χ.decode S₁).get h₁ = (χ.decode S₂).get h₂ := by
  subst h
  rfl

/-- Produce a coding function for a given ordered support and tangle it supports. -/
noncomputable def code (S : OrdSupport β) (t : Tangle β)
    (h : Supports (Allowable β) (S : Set (SupportCondition β)) t) :
    CodingFunction β where
  decode T := ⟨∃ ρ : Allowable β, T = ρ • S, fun hT => hT.choose • t⟩
  dom_nonempty := ⟨S, 1, by rw [one_smul]⟩
  supports_decode' T hT := by
    have := smul_supports h hT.choose
    rw [← hT.choose_spec] at this
    exact this
  dom_iff T U hT := by
    obtain ⟨ρ, rfl⟩ := hT
    constructor
    · rintro ⟨ρ', rfl⟩
      refine ⟨ρ' * ρ⁻¹, ?_⟩
      rw [smul_smul, inv_mul_cancel_right]
    · rintro ⟨ρ', h⟩
      refine ⟨ρ' * ρ, ?_⟩
      rw [mul_smul]
      exact h
  decode_smul' T ρ h₁ h₂ := by
    rw [← inv_smul_eq_iff, ← inv_smul_eq_iff, smul_smul, smul_smul]
    refine h _ ?_
    intros c hc
    have := h₂.choose_spec.symm
    conv_rhs at this => rw [h₁.choose_spec]
    rw [← inv_smul_eq_iff, ← inv_smul_eq_iff, smul_smul, smul_smul] at this
    exact OrdSupport.smul_eq_of_smul_eq _ ⟨c, hc⟩ this

@[simp]
theorem code_decode (S : OrdSupport β) (t : Tangle β)
    (h : Supports (Allowable β) (S : Set (SupportCondition β)) t) :
    (code S t h).decode S = Part.some t := by
  refine Part.ext' ?_ ?_
  · simp only [Allowable.toStructPerm_smul, Part.some_dom, iff_true]
    refine ⟨1, ?_⟩
    simp only [map_one, one_smul]
  · intros h' _
    refine h _ ?_
    intros c hc
    exact OrdSupport.smul_eq_of_smul_eq _ ⟨c, hc⟩ h'.choose_spec.symm

@[simp]
theorem mem_code_self {S : OrdSupport β} {t : Tangle β}
    {h : Supports (Allowable β) (S : Set (SupportCondition β)) t} :
    S ∈ code S t h :=
  ⟨1, by rw [one_smul]⟩

@[simp]
theorem mem_code {S : OrdSupport β} {t : Tangle β}
    {h : Supports (Allowable β) (S : Set (SupportCondition β)) t} (T : OrdSupport β) :
    T ∈ code S t h ↔ ∃ ρ : Allowable β, T = ρ • S :=
  Iff.rfl

/-- Every coding function can be obtained by invoking `code` with an ordered support in its
domain. -/
theorem eq_code {χ : CodingFunction β} {S : OrdSupport β} (h : S ∈ χ) :
    χ = code S ((χ.decode S).get h) (χ.supports_decode S h) := by
  refine ext S h ?_ ?_
  · refine ⟨1, ?_⟩
    rw [one_smul]
  · simp only [code_decode, Part.get_some]

/-- A coding function is *strong* if it contains a strong support. -/
def Strong (χ : CodingFunction β) : Prop :=
  ∃ S : OrdSupport β, S ∈ χ ∧ S.Strong

theorem code_strong {S : OrdSupport β} {t : Tangle β}
    {h : Supports (Allowable β) (S : Set (SupportCondition β)) t} (hS : S.Strong) :
    (code S t h).Strong :=
  ⟨S, mem_code_self, hS⟩

end CodingFunction

end ConNF
