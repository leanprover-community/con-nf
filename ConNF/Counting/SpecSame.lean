import ConNF.FOA
import ConNF.Counting.Spec

/-!
# Supports with the same specification
-/

open Quiver Set Sum WithBot

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ} [LeLevel β]
  {S T : Support β} {σ : Spec β} (hS : σ.Specifies S) (hT : σ.Specifies T)

@[mk_iff]
inductive MapAtom (aS aT : Atom) : ExtendedIndex β → Prop
  | mem (i : κ) (hi : i < σ.max) (A : ExtendedIndex β)
      (hiS : S.f i (hS.lt_max hi) = ⟨A, inl aS⟩) (hiT : T.f i (hT.lt_max hi) = ⟨A, inl aT⟩) :
      MapAtom aS aT A
  | atom (i : κ) (hi : i < σ.max) (A : ExtendedIndex β) (NS NT : NearLitter)
      (hiS : S.f i (hS.lt_max hi) = ⟨A, inr NS⟩) (hiT : T.f i (hT.lt_max hi) = ⟨A, inr NT⟩)
      (P : InflexibleBotPath A)
      (haS : NS.1 = fuzz (bot_ne_coe (a := P.ε)) aS) (haT : NT.1 = fuzz (bot_ne_coe (a := P.ε)) aT) :
      MapAtom aS aT A
  | support (i : κ) (hi : i < σ.max) (A : ExtendedIndex β) (NS NT : NearLitter)
      (hiS : S.f i (hS.lt_max hi) = ⟨A, inr NS⟩) (hiT : T.f i (hT.lt_max hi) = ⟨A, inr NT⟩)
      (P : InflexibleCoePath A) (tS tT : Tangle P.δ)
      (haS : NS.1 = fuzz P.hδε tS) (haT : NT.1 = fuzz P.hδε tS)
      (ρ : Allowable P.δ) (hρt : ρ • tS = tT)
      (hρ' : ∀ (j : κ)
        (hjS : j < (S.comp (P.B.cons P.hδ)).max) (hjT : j < (T.comp (P.B.cons P.hδ)).max),
        ρ • (S.comp (P.B.cons P.hδ)).f j hjS = (T.comp (P.B.cons P.hδ)).f j hjT)
      (B : ExtendedIndex P.δ)
      (hB : ∃ d, (d ∈ tS.support ∨ d ∈ S.comp (P.B.cons P.hδ)) ∧ ⟨B, inl aS⟩ ≤ d)
      (h : Allowable.toStructPerm ρ B • aS = aT) :
      MapAtom aS aT ((P.B.cons P.hδ).comp B)

@[mk_iff]
inductive MapNearLitter (NS NT : NearLitter) : ExtendedIndex β → Prop
  | mem (i : κ) (hi : i < σ.max) (A : ExtendedIndex β)
      (hiS : S.f i (hS.lt_max hi) = ⟨A, inr NS⟩) (hiT : T.f i (hT.lt_max hi) = ⟨A, inr NT⟩) :
      MapNearLitter NS NT A
  | support (i : κ) (hi : i < σ.max) (A : ExtendedIndex β) (NS' NT' : NearLitter)
      (hiS : S.f i (hS.lt_max hi) = ⟨A, inr NS'⟩) (hiT : T.f i (hT.lt_max hi) = ⟨A, inr NT'⟩)
      (P : InflexibleCoePath A) (tS tT : Tangle P.δ)
      (haS : NS'.1 = fuzz P.hδε tS) (haT : NT'.1 = fuzz P.hδε tS)
      (ρ : Allowable P.δ) (hρ : ρ • tS = tT)
      (hρ' : ∀ (j : κ)
        (hjS : j < (S.comp (P.B.cons P.hδ)).max) (hjT : j < (T.comp (P.B.cons P.hδ)).max),
        ρ • (S.comp (P.B.cons P.hδ)).f j hjS = (T.comp (P.B.cons P.hδ)).f j hjT)
      (B : ExtendedIndex P.δ)
      (hB : ∃ d, (d ∈ tS.support ∨ d ∈ S.comp (P.B.cons P.hδ)) ∧ ⟨B, inr NS⟩ ≤ d)
      (h : Allowable.toStructPerm ρ B • NS = NT) :
      MapNearLitter NS NT ((P.B.cons P.hδ).comp B)

theorem mapAtom_mem_mem (aS aT₁ aT₂ : Atom) (i₁ i₂ : κ) (hi₁ : i₁ < σ.max) (hi₂ : i₂ < σ.max)
    (A : ExtendedIndex β)
    (hiS₁ : S.f i₁ (hS.lt_max hi₁) = ⟨A, inl aS⟩) (hiT₁ : T.f i₁ (hT.lt_max hi₁) = ⟨A, inl aT₁⟩)
    (hiS₂ : S.f i₂ (hS.lt_max hi₂) = ⟨A, inl aS⟩) (hiT₂ : T.f i₂ (hT.lt_max hi₂) = ⟨A, inl aT₂⟩) :
    aT₁ = aT₂ := by
  have h₁ := hS.specifies i₁ hi₁ (hS.lt_max hi₁)
  rw [hiS₁, Spec.specifiesCondition_atom_right_iff] at h₁
  have h₂ := hS.specifies i₂ hi₂ (hS.lt_max hi₂)
  rw [hiS₂, Spec.specifiesCondition_atom_right_iff] at h₂
  have h₃ := hT.specifies i₁ hi₁ (hT.lt_max hi₁)
  rw [hiT₁, Spec.specifiesCondition_atom_right_iff] at h₃
  have h₄ := hT.specifies i₂ hi₂ (hT.lt_max hi₂)
  rw [hiT₂, Spec.specifiesCondition_atom_right_iff] at h₄
  rw [h₁] at h₃
  rw [h₂] at h₄
  simp only [SpecCondition.atom.injEq, true_and] at h₃ h₄
  have h₅ := h₃.1.symm.trans h₄.1
  obtain ⟨_, h⟩ := (ext_iff.mp h₅ i₁).mp ⟨hT.lt_max hi₁, hiT₁⟩
  rw [hiT₁] at h
  cases h
  rfl

theorem mapAtom_support_support (aS aT₁ aT₂ : Atom)
    (i₁ i₂ : κ) (hi₁ : i₁ < σ.max) (hi₂ : i₂ < σ.max) (A₁ A₂ : ExtendedIndex β)
    (NS₁ NT₁ NS₂ NT₂ : NearLitter)
    (hiS₁ : S.f i₁ (hS.lt_max hi₁) = ⟨A₁, inr NS₁⟩) (hiT₁ : T.f i₁ (hT.lt_max hi₁) = ⟨A₁, inr NT₁⟩)
    (hiS₂ : S.f i₂ (hS.lt_max hi₂) = ⟨A₂, inr NS₂⟩) (hiT₂ : T.f i₂ (hT.lt_max hi₂) = ⟨A₂, inr NT₂⟩)
    (P₁ : InflexibleCoePath A₁) (P₂ : InflexibleCoePath A₂)
    (tS₁ tT₁ : Tangle P₁.δ) (tS₂ tT₂ : Tangle P₂.δ)
    (haS₁ : NS₁.1 = fuzz P₁.hδε tS₁) (haT₁ : NT₁.1 = fuzz P₁.hδε tS₁)
    (haS₂ : NS₂.1 = fuzz P₂.hδε tS₂) (haT₂ : NT₂.1 = fuzz P₂.hδε tS₂)
    (ρ₁ : Allowable P₁.δ) (ρ₂ : Allowable P₂.δ) (hρ₁ : ρ₁ • tS₁ = tT₁) (hρ₂ : ρ₂ • tS₂ = tT₂)
    (hρ₁' : ∀ (j : κ)
      (hjS : j < (S.comp (P₁.B.cons P₁.hδ)).max) (hjT : j < (T.comp (P₁.B.cons P₁.hδ)).max),
      ρ₁ • (S.comp (P₁.B.cons P₁.hδ)).f j hjS = (T.comp (P₁.B.cons P₁.hδ)).f j hjT)
    (hρ₂' : ∀ (j : κ)
      (hjS : j < (S.comp (P₂.B.cons P₂.hδ)).max) (hjT : j < (T.comp (P₂.B.cons P₂.hδ)).max),
      ρ₂ • (S.comp (P₂.B.cons P₂.hδ)).f j hjS = (T.comp (P₂.B.cons P₂.hδ)).f j hjT)
    (B₁ : ExtendedIndex P₁.δ) (B₂ : ExtendedIndex P₂.δ)
    (hB₁ : ∃ d, (d ∈ tS₁.support ∨ d ∈ S.comp (P₁.B.cons P₁.hδ)) ∧ ⟨B₁, inl aS⟩ ≤ d)
    (hB₂ : ∃ d, (d ∈ tS₂.support ∨ d ∈ S.comp (P₂.B.cons P₂.hδ)) ∧ ⟨B₂, inl aS⟩ ≤ d)
    (h₁ : Allowable.toStructPerm ρ₁ B₁ • aS = aT₁)
    (h₂ : Allowable.toStructPerm ρ₂ B₂ • aS = aT₂)
    (h₂' : (P₁.B.cons P₁.hδ).comp B₁ = (P₂.B.cons P₂.hδ).comp B₂) :
    aT₁ = aT₂ := by
  sorry

theorem mapAtom_wellDefined (aS aT₁ aT₂ : Atom) (A : ExtendedIndex β)
    (h₁ : MapAtom hS hT aS aT₁ A) (h₂ : MapAtom hS hT aS aT₂ A) : aT₁ = aT₂ := by
  obtain (⟨i₁, hi₁, _, hiS₁, hiT₁⟩ |
      ⟨i₁, hi₁, _, NS₁, NT₁, hiS₁, hiT₁, P₁, haS₁, haT₁⟩ |
      ⟨i₁, hi₁, A₁, NS₁, NT₁, hiS₁, hiT₁, P₁, tS₁, tT₁, haS₁, haT₁,
        ρ₁, hρ₁, hρ₁', B₁, hB₁, h₁⟩) := h₁ <;>
    rw [mapAtom_iff] at h₂ <;>
    obtain (⟨i₂, hi₂, hiS₂, hiT₂⟩ |
      ⟨i₂, hi₂, NS₂, NT₂, hiS₂, hiT₂, P₂, haS₂, haT₂⟩ |
      ⟨i₂, hi₂, A₂, NS₂, NT₂, hiS₂, hiT₂, P₂, tS₂, tT₂, haS₂, haT₂,
        ρ₂, hρ₂, hρ₂', B₂, hB₂, h₂, h₂'⟩) := h₂
  · exact mapAtom_mem_mem hS hT aS aT₁ aT₂ i₁ i₂ hi₁ hi₂ A hiS₁ hiT₁ hiS₂ hiT₂
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · exact mapAtom_support_support hS hT aS aT₁ aT₂ i₁ i₂ hi₁ hi₂ A₁ A₂ NS₁ NT₁ NS₂ NT₂
      hiS₁ hiT₁ hiS₂ hiT₂ P₁ P₂ tS₁ tT₁ tS₂ tT₂ haS₁ haT₁ haS₂ haT₂ ρ₁ ρ₂ hρ₁ hρ₂ hρ₁' hρ₂' B₁ B₂
      hB₁ hB₂ h₁ h₂ h₂'

def supportMap : StructBehaviour β :=
  fun A => {
    atomMap := sorry
    nearLitterMap := sorry
    atomMap_dom_small := sorry
    nearLitterMap_dom_small := sorry
  }

end ConNF
