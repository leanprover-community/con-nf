import ConNF.FOA
import ConNF.Counting.Spec

/-!
# Supports with the same specification
-/

open Quiver Set Sum WithBot

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ} [LeLevel β]
  {S T : Support β} {hS : S.Strong} {hT : T.Strong}
  {σ : Spec β} (hσS : σ.Specifies S hS) (hσT : σ.Specifies T hT)

def ConvertAtom (S T : Support β) (A : ExtendedIndex β) (aS aT : Atom) : Prop :=
  ∃ (i : κ) (hiS : i < S.max) (hiT : i < T.max), S.f i hiS = ⟨A, inl aS⟩ ∧ T.f i hiT = ⟨A, inl aT⟩

def ConvertNearLitter (S T : Support β) (A : ExtendedIndex β) (NS NT : NearLitter) : Prop :=
  ∃ (i : κ) (hiS : i < S.max) (hiT : i < T.max), S.f i hiS = ⟨A, inr NS⟩ ∧ T.f i hiT = ⟨A, inr NT⟩

theorem convertAtom_subsingleton (A : ExtendedIndex β) (aS aT aT' : Atom)
    (h : ConvertAtom S T A aS aT) (h' : ConvertAtom S T A aS aT') : aT = aT' := by
  obtain ⟨i, hiS₁, hiT₁, hiS₂, hiT₂⟩ := h
  obtain ⟨i', hiS₁', hiT₁', hiS₂', hiT₂'⟩ := h'
  have h₁ := (hσS.atom_spec i hiS₁ A aS hiS₂).symm.trans (hσT.atom_spec i hiT₁ A aT hiT₂)
  have h₂ := (hσS.atom_spec i' hiS₁' A aS hiS₂').symm.trans (hσT.atom_spec i' hiT₁' A aT' hiT₂')
  simp only [SpecCondition.atom.injEq, true_and] at h₁ h₂
  have := h₁.1.symm.trans h₂.1
  rw [Set.ext_iff] at this
  obtain ⟨_, h⟩ := (this i).mp ⟨hiT₁, hiT₂⟩
  have := hiT₂.symm.trans h
  cases this
  rfl

theorem convert_flexible {A : ExtendedIndex β} {NS NT : NearLitter} (h : Flexible A NS.1)
    {i : κ} (hiS : i < S.max) (hiT : i < T.max)
    (hiNS : S.f i hiS = ⟨A, inr NS⟩) (hiNT : T.f i hiT = ⟨A, inr NT⟩) : Flexible A NT.1 := by
  obtain (hN | ⟨⟨hN⟩⟩ | ⟨⟨hN⟩⟩) := flexible_cases' A NT.1
  · exact hN
  · have h₁ := hσS.flexible_spec i hiS A NS h hiNS
    have h₂ := hσT.inflexibleBot_spec i hiT A NT hN hiNT
    cases h₁.symm.trans h₂
  · have h₁ := hσS.flexible_spec i hiS A NS h hiNS
    have h₂ := hσT.inflexibleCoe_spec i hiT A NT hN hiNT
    cases h₁.symm.trans h₂

theorem convertNearLitter_subsingleton_flexible (A : ExtendedIndex β) (NS NT NT' : NearLitter)
    (h : ConvertNearLitter S T A NS NT) (h' : ConvertNearLitter S T A NS NT')
    (hN : Flexible A NS.1) : NT = NT' := by
  obtain ⟨i, hiS₁, hiT₁, hiS₂, hiT₂⟩ := h
  obtain ⟨i', hiS₁', hiT₁', hiS₂', hiT₂'⟩ := h'
  have h₁ := hσS.flexible_spec i hiS₁ A NS hN hiS₂
  have h₂ := hσS.flexible_spec i' hiS₁' A NS hN hiS₂'
  have h₃ := hσT.flexible_spec i hiT₁ A NT
    (convert_flexible hσS hσT hN hiS₁ hiT₁ hiS₂ hiT₂) hiT₂
  have h₄ := hσT.flexible_spec i' hiT₁' A NT'
    (convert_flexible hσS hσT  hN hiS₁' hiT₁' hiS₂' hiT₂') hiT₂'
  have h₅ := h₁.symm.trans h₃
  have h₆ := h₂.symm.trans h₄
  simp only [and_true, exists_const, SpecCondition.flexible.injEq, true_and] at h₅ h₆
  have := h₅.symm.trans h₆
  rw [Set.ext_iff] at this
  obtain ⟨_, h⟩ := (this i).mp ⟨hiT₁, hiT₂⟩
  have := hiT₂.symm.trans h
  cases this
  rfl

theorem convert_inflexibleCoe {A : ExtendedIndex β} {NS NT : NearLitter} (P : InflexibleCoePath A)
    (t : Tangle P.δ) (hNS : NS.1 = fuzz P.hδε t)
    {i : κ} (hiS : i < S.max) (hiT : i < T.max)
    (hiNS : S.f i hiS = ⟨A, inr NS⟩) (hiNT : T.f i hiT = ⟨A, inr NT⟩) :
    ∃ t', NT.1 = fuzz P.hδε t' := by
  obtain (hN | ⟨⟨hN⟩⟩ | ⟨⟨P', t', hNT⟩⟩) := flexible_cases' A NT.1
  · have h₁ := hσS.inflexibleCoe_spec i hiS A NS ⟨P, t, hNS⟩ hiNS
    have h₂ := hσT.flexible_spec i hiT A NT hN hiNT
    cases h₁.symm.trans h₂
  · have h₁ := hσS.inflexibleCoe_spec i hiS A NS ⟨P, t, hNS⟩ hiNS
    have h₂ := hσT.inflexibleBot_spec i hiT A NT hN hiNT
    cases h₁.symm.trans h₂
  · have h₁ := hσS.inflexibleCoe_spec i hiS A NS ⟨P, t, hNS⟩ hiNS
    have h₂ := hσT.inflexibleCoe_spec i hiT A NT ⟨P', t', hNT⟩ hiNT
    have := h₁.symm.trans h₂
    simp only [SpecCondition.inflexibleCoe.injEq, heq_eq_eq, true_and] at this
    cases this.1
    exact ⟨t', hNT⟩

theorem convertNearLitter_subsingleton (A : ExtendedIndex β) (NS NT NT' : NearLitter)
    (h : ConvertNearLitter S T A NS NT) (h' : ConvertNearLitter S T A NS NT') : NT = NT' := by
  obtain (hNS | ⟨⟨hNS⟩⟩ | ⟨⟨P, t, hNS⟩⟩) := flexible_cases' A NS.1
  · exact convertNearLitter_subsingleton_flexible hσS hσT A NS NT NT' h h' hNS
  · obtain ⟨i, hiS₁, hiT₁, hiS₂, hiT₂⟩ := h
    obtain ⟨i', hiS₁', hiT₁', hiS₂', hiT₂'⟩ := h'
    sorry
  · obtain ⟨i, hiS₁, hiT₁, hiS₂, hiT₂⟩ := h
    obtain ⟨i', hiS₁', hiT₁', hiS₂', hiT₂'⟩ := h'
    have h₁ := hσS.inflexibleCoe_spec i hiS₁ A NS ⟨P, t, hNS⟩ hiS₂
    have h₂ := hσS.inflexibleCoe_spec i' hiS₁' A NS ⟨P, t, hNS⟩ hiS₂'
    obtain ⟨u, hNT⟩ := convert_inflexibleCoe hσS hσT P t hNS hiS₁ hiT₁ hiS₂ hiT₂
    obtain ⟨u', hNT'⟩ := convert_inflexibleCoe hσS hσT P t hNS hiS₁' hiT₁' hiS₂' hiT₂'
    have h₃ := hσT.inflexibleCoe_spec i hiT₁ A NT ⟨P, u, hNT⟩ hiT₂
    have h₄ := hσT.inflexibleCoe_spec i' hiT₁' A NT' ⟨P, u', hNT'⟩ hiT₂'
    have h₅ := h₁.symm.trans h₃
    have h₆ := h₂.symm.trans h₄
    clear h₁ h₂ h₃ h₄
    simp only [SpecCondition.inflexibleCoe.injEq, heq_eq_eq, CodingFunction.code_eq_code_iff,
      true_and] at h₅ h₆
    obtain ⟨ρ, h₅, rfl⟩ := h₅
    obtain ⟨ρ', h₆, rfl⟩ := h₆
    sorry

def convert (S T : Support β) : StructBehaviour β :=
  fun A => {
    atomMap := sorry
    nearLitterMap := sorry
    atomMap_dom_small := sorry
    nearLitterMap_dom_small := sorry
  }

end ConNF
