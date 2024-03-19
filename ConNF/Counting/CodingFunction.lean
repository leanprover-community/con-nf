import ConNF.Counting.StrongSupport

/-!
# Coding functions
-/

open MulAction Set Sum

universe u

namespace ConNF

variable [Params.{u}] [Level] {β : Λ} [TangleData β]

structure CodingFunction (β : Λ) [TangleData β] where
  decode : Support β →. Tangle β
  dom_nonempty : decode.Dom.Nonempty
  supports_decode' (S : Support β) (hS : (decode S).Dom) :
    Supports (Allowable β) (S : Set (Address β)) ((decode S).get hS)
  dom_iff (S T : Support β) (hS : (decode S).Dom) :
    (decode T).Dom ↔ ∃ ρ : Allowable β, T = ρ • S
  decode_smul' (S : Support β) (ρ : Allowable β)
    (h₁ : (decode S).Dom) (h₂ : (decode (ρ • S)).Dom) :
    (decode (ρ • S)).get h₂ = ρ • (decode S).get h₁

namespace CodingFunction

instance : Membership (Support β) (CodingFunction β) where
  mem S χ := (χ.decode S).Dom

theorem mem_iff {χ : CodingFunction β} {S : Support β} :
    S ∈ χ ↔ (χ.decode S).Dom :=
  Iff.rfl

theorem mem_iff_of_mem {χ : CodingFunction β} {S T : Support β} (h : S ∈ χ) :
    T ∈ χ ↔ ∃ ρ : Allowable β, T = ρ • S :=
  χ.dom_iff S T h

theorem smul_mem {χ : CodingFunction β} {S : Support β} (ρ : Allowable β) (h : S ∈ χ) :
    ρ • S ∈ χ :=
  (χ.mem_iff_of_mem h).mpr ⟨ρ, rfl⟩

theorem mem_of_smul_mem {χ : CodingFunction β} {S : Support β} {ρ : Allowable β}
    (h : ρ • S ∈ χ) : S ∈ χ :=
  (χ.mem_iff_of_mem h).mpr ⟨ρ⁻¹, by rw [inv_smul_smul]⟩

theorem exists_mem (χ : CodingFunction β) :
    ∃ S, S ∈ χ :=
  χ.dom_nonempty

theorem supports_decode {χ : CodingFunction β} (S : Support β) (hS : S ∈ χ) :
    Supports (Allowable β) (S : Set (Address β)) ((χ.decode S).get hS) :=
  χ.supports_decode' S hS

theorem decode_smul {χ : CodingFunction β} (S : Support β) (ρ : Allowable β) (h : ρ • S ∈ χ) :
    (χ.decode (ρ • S)).get h = ρ • (χ.decode S).get (mem_of_smul_mem h) :=
  χ.decode_smul' S ρ _ _

/-- Two coding functions are equal if they decode a single ordered support to the same tangle. -/
theorem ext {χ₁ χ₂ : CodingFunction β}
    (S : Support β) (h₁ : S ∈ χ₁) (h₂ : S ∈ χ₂)
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

theorem smul_supports {S : Support β} {t : Tangle β}
    (h : Supports (Allowable β) (S : Set (Address β)) t) (ρ : Allowable β) :
    Supports (Allowable β) ((ρ • S : Support β) : Set (Address β)) (ρ • t) := by
  intro ρ' hρ'
  have := h (ρ⁻¹ * ρ' * ρ) ?_
  · rw [mul_assoc, mul_smul, inv_smul_eq_iff, mul_smul] at this
    exact this
  intros c hc
  rw [mul_assoc, mul_smul, inv_smul_eq_iff, mul_smul]
  refine hρ' ?_
  exact Enumeration.smul_mem_smul hc ρ

theorem decode_congr {χ : CodingFunction β} {S₁ S₂ : Support β}
    {h₁ : S₁ ∈ χ} {h₂ : S₂ ∈ χ} (h : S₁ = S₂) :
    (χ.decode S₁).get h₁ = (χ.decode S₂).get h₂ := by
  subst h
  rfl

/-- Produce a coding function for a given ordered support and tangle it supports. -/
noncomputable def code (S : Support β) (t : Tangle β)
    (h : Supports (Allowable β) (S : Set (Address β)) t) :
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
    exact Allowable.smul_eq_of_smul_support_eq this hc

@[simp]
theorem code_decode (S : Support β) (t : Tangle β)
    (h : Supports (Allowable β) (S : Set (Address β)) t) :
    (code S t h).decode S = Part.some t := by
  refine Part.ext' ?_ ?_
  · simp only [Allowable.toStructPerm_smul, Part.some_dom, iff_true]
    refine ⟨1, ?_⟩
    simp only [map_one, one_smul]
  · intros h' _
    refine h _ ?_
    intros c hc
    exact Allowable.smul_eq_of_smul_support_eq h'.choose_spec.symm hc

@[simp]
theorem mem_code_self {S : Support β} {t : Tangle β}
    {h : Supports (Allowable β) (S : Set (Address β)) t} :
    S ∈ code S t h :=
  ⟨1, by rw [one_smul]⟩

@[simp]
theorem mem_code {S : Support β} {t : Tangle β}
    {h : Supports (Allowable β) (S : Set (Address β)) t} (T : Support β) :
    T ∈ code S t h ↔ ∃ ρ : Allowable β, T = ρ • S :=
  Iff.rfl

/-- Every coding function can be obtained by invoking `code` with an ordered support in its
domain. -/
theorem eq_code {χ : CodingFunction β} {S : Support β} (h : S ∈ χ) :
    χ = code S ((χ.decode S).get h) (χ.supports_decode S h) := by
  refine ext S h ?_ ?_
  · refine ⟨1, ?_⟩
    rw [one_smul]
  · simp only [code_decode, Part.get_some]

theorem code_smul (S : Support β) (t : Tangle β) (ρ : Allowable β)
    (h₁ : Supports (Allowable β) ((ρ • S : Support β) : Set (Address β)) (ρ • t))
    (h₂ : Supports (Allowable β) (S : Set (Address β)) t) :
    code (ρ • S) (ρ • t) h₁ = code S t h₂ := by
  refine ext S ⟨ρ⁻¹, eq_inv_smul_iff.mpr rfl⟩ mem_code_self ?_
  have := decode_smul (χ := code (ρ • S) (ρ • t) h₁) (ρ • S) ρ⁻¹ ⟨ρ⁻¹, rfl⟩
  simp_rw [inv_smul_smul] at this
  rw [this]
  simp only [code_decode, Part.get_some, inv_smul_smul]

@[simp]
theorem code_eq_code_iff (S S' : Support β) (t t' : Tangle β)
    (h : Supports (Allowable β) (S : Set (Address β)) t)
    (h' : Supports (Allowable β) (S' : Set (Address β)) t') :
    code S t h = code S' t' h' ↔ ∃ ρ : Allowable β, S' = ρ • S ∧ t' = ρ • t := by
  constructor
  · intro hc
    have : S' ∈ code S t h
    · rw [hc]
      exact mem_code_self
    obtain ⟨ρ, rfl⟩ := this
    refine ⟨ρ, rfl, ?_⟩
    have := code_decode (ρ • S) t' h'
    rw [← hc, ← Part.get_eq_iff_eq_some, decode_smul] at this
    simp only [code_decode, Part.get_some] at this
    exact this.symm
    exact ⟨ρ, rfl⟩
  · rintro ⟨ρ, rfl, rfl⟩
    refine ext (ρ • S) ⟨ρ, rfl⟩ ⟨1, by rw [one_smul]⟩ ?_
    simp only [code_decode, Part.get_some, decode_smul]

def Strong [BasePositions] [FOAAssumptions] {β : Λ} [LeLevel β] (χ : CodingFunction β) : Prop :=
  ∀ S ∈ χ.decode.Dom, S.Strong

theorem strong_of_strong_mem [BasePositions] [FOAAssumptions] {β : Λ} [LeLevel β]
    (χ : CodingFunction β) (S : Support β) (hS : S.Strong) (hSχ : S ∈ χ.decode.Dom) : χ.Strong := by
  intro T hTχ
  obtain ⟨ρ, rfl⟩ := (χ.dom_iff S T hSχ).mp hTχ
  exact hS.smul ρ

theorem code_strong [BasePositions] [FOAAssumptions] {β : Λ} [LeLevel β]
    (S : Support β) (t : Tangle β)
    (ht : Supports (Allowable β) (S : Set (Address β)) t) (hS : S.Strong) :
    (code S t ht).Strong :=
  strong_of_strong_mem _ S hS mem_code_self

end CodingFunction

end ConNF
