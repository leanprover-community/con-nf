import ConNF.Mathlib.Support
import ConNF.FOA.Basic.Flexible
import ConNF.Counting.CodingFunction

/-!
# Specifications
-/

open Quiver Set Sum WithBot

open scoped Classical Cardinal symmDiff

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ}

inductive SpecCondition (β : Λ)
  | atom (A : ExtendedIndex β) (s : Set κ) (t : Set κ)
  | flexible (A : ExtendedIndex β) (s : Set κ)
  | inflexibleCoe (A : ExtendedIndex β) (h : InflexibleCoePath A)
      (χ : CodingFunction h.δ) (hχ : χ.Strong)
  | inflexibleBot (A : ExtendedIndex β) (h : InflexibleBotPath A) (s : Set κ)

abbrev Spec (β : Λ) := Enumeration (SpecCondition β)

namespace Spec

theorem before_comp_supports (S : Support β) (hS : S.Strong)
    {i : κ} (hi : i < S.max) {A : ExtendedIndex β}
    {N : NearLitter} (h : InflexibleCoe A N.1) (hSi : S.f i hi = ⟨A, inr N⟩) :
    MulAction.Supports (Allowable h.path.δ)
      ((S.before i hi).comp (h.path.B.cons h.path.hδ)).carrier h.t := by
  refine (support_supports h.t).mono ?_
  simp only [Support.comp_carrier, Support.before_carrier, exists_and_left, preimage_setOf_eq]
  rintro c hc
  have := Support.Precedes.fuzz A N h c hc
  rw [h.path.hA] at hSi
  rw [← hSi] at this
  obtain ⟨j, hj₁, hj₂, h⟩ := hS.precedes hi _ this
  exact ⟨j, hj₂, hj₁, h⟩

/-- A specification `σ` specifies an ordered support `S` if each support condition in `S` is
described in a sensible way by `σ`. -/
structure Specifies (σ : Spec β) (S : Support β) (hS : S.Strong) : Prop where
  max_eq_max : S.max = σ.max
  atom_spec (i : κ) (hi : i < S.max) (A : ExtendedIndex β) (a : Atom) :
      S.f i hi = ⟨A, inl a⟩ →
      σ.f i (hi.trans_eq max_eq_max) = SpecCondition.atom A
        {j | ∃ hj, S.f j hj = ⟨A, inl a⟩} {j | ∃ hj N, S.f j hj = ⟨A, inr N⟩ ∧ a ∈ N}
  flexible_spec (i : κ) (hi : i < S.max) (A : ExtendedIndex β) (N : NearLitter) :
      Flexible A N.1 →
      S.f i hi = ⟨A, inr N⟩ →
      σ.f i (hi.trans_eq max_eq_max) = SpecCondition.flexible A
        {j | ∃ hj, ∃ (N' : NearLitter), S.f j hj = ⟨A, inr N⟩ ∧ N'.1 = N'.1}
  inflexibleCoe_spec (i : κ) (hi : i < S.max) (A : ExtendedIndex β) (N : NearLitter)
      (h : InflexibleCoe A N.1) (hSi : S.f i hi = ⟨A, inr N⟩) :
      σ.f i (hi.trans_eq max_eq_max) = SpecCondition.inflexibleCoe A h.path
        (CodingFunction.code ((S.before i hi).comp (h.path.B.cons h.path.hδ)) h.t
          (before_comp_supports S hS hi h hSi))
        (CodingFunction.code_strong _ _ _
          (Support.comp_strong _ _ (Support.before_strong _ _ _ hS)))
  inflexibleBot_spec (i : κ) (hi : i < S.max) (A : ExtendedIndex β) (N : NearLitter)
      (h : InflexibleBot A N.1) :
      S.f i hi = ⟨A, inr N⟩ →
      σ.f i (hi.trans_eq max_eq_max) = SpecCondition.inflexibleBot A h.path
        {j | ∃ hj, S.f j hj = ⟨h.path.B.cons (bot_lt_coe _), inl h.a⟩}

end Spec

end ConNF
