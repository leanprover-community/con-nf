import ConNF.Mathlib.Support
import ConNF.FOA.Basic.Flexible
import ConNF.Counting.CodingFunction
import ConNF.Counting.StrongSupport

/-!
# Specifications
-/

open Quiver Set Sum WithBot

open scoped Classical Cardinal symmDiff

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions] [FOAAssumptions] {β : Λ}

inductive SpecCondition (β : Λ)
  | atom (A : ExtendedIndex β) (s : Set κ) (t : Set κ)
  | flexible (A : ExtendedIndex β) (s : Set κ) (t : κ → Set κ)
  | inflexibleCoe (A : ExtendedIndex β) (h : InflexibleCoePath A)
      (χ : CodingFunction h.δ) (t : κ → Set κ) (m : κ) (u : κ → Set κ)
  | inflexibleBot (A : ExtendedIndex β) (h : InflexibleBotPath A) (s : Set κ) (t : κ → Set κ)

@[mk_iff le_iff]
protected inductive SpecCondition.LE : SpecCondition β → SpecCondition β → Prop
  | atom {A s₁ s₂ t₁ t₂} : s₁ ⊆ s₂ → t₁ ⊆ t₂ →
      SpecCondition.LE (.atom A s₁ t₁) (.atom A s₂ t₂)
  | flexible {A s₁ s₂ t₁ t₂} : s₁ ⊆ s₂ → t₁ ≤ t₂ →
      SpecCondition.LE (.flexible A s₁ t₁) (.flexible A s₂ t₂)
  | inflexibleCoe {A h χ t₁ t₂ m u₁ u₂} : t₁ ≤ t₂ → u₁ ≤ u₂ →
      SpecCondition.LE (.inflexibleCoe A h χ t₁ m u₁) (.inflexibleCoe A h χ t₂ m u₂)
  | inflexibleBot {A h s₁ s₂ t₁ t₂} : s₁ ⊆ s₂ → t₁ ≤ t₂ →
      SpecCondition.LE (.inflexibleBot A h s₁ t₁) (.inflexibleBot A h s₂ t₂)

instance : LE (SpecCondition β) where
  le := SpecCondition.LE

instance : PartialOrder (SpecCondition β) where
  le_refl c := by
    cases c
    · exact .atom subset_rfl subset_rfl
    · exact .flexible subset_rfl le_rfl
    · exact .inflexibleCoe le_rfl le_rfl
    · exact .inflexibleBot subset_rfl le_rfl
  le_trans c₁ c₂ c₃ h₁ h₂ := by
    cases h₁ <;> cases h₂
    · exact .atom (subset_trans ‹_› ‹_›) (subset_trans ‹_› ‹_›)
    · exact .flexible (subset_trans ‹_› ‹_›) (le_trans ‹_› ‹_›)
    · exact .inflexibleCoe (le_trans ‹_› ‹_›) (le_trans ‹_› ‹_›)
    · exact .inflexibleBot (subset_trans ‹_› ‹_›) (le_trans ‹_› ‹_›)
  le_antisymm c₁ c₂ h₁ h₂ := by
    cases h₁ <;> cases h₂
    · rw [SpecCondition.atom.injEq]
      exact ⟨rfl, subset_antisymm ‹_› ‹_›, subset_antisymm ‹_› ‹_›⟩
    · rw [SpecCondition.flexible.injEq]
      exact ⟨rfl, subset_antisymm ‹_› ‹_›, le_antisymm ‹_› ‹_›⟩
    · rw [SpecCondition.inflexibleCoe.injEq]
      exact ⟨rfl, HEq.rfl, HEq.rfl, le_antisymm ‹_› ‹_›, rfl, le_antisymm ‹_› ‹_›⟩
    · rw [SpecCondition.inflexibleBot.injEq]
      exact ⟨rfl, HEq.rfl, subset_antisymm ‹_› ‹_›, le_antisymm ‹_› ‹_›⟩

abbrev Spec (β : Λ) := Enumeration (SpecCondition β)

namespace Spec

-- TODO: Rename now that we've removed `before`.
theorem before_comp_supports (S : Support β) (hS : S.Strong)
    {i : κ} (hi : i < S.max) {A : ExtendedIndex β}
    {N : NearLitter} (h : InflexibleCoe A N.1) (hSi : S.f i hi = ⟨A, inr N⟩) :
    MulAction.Supports (Allowable h.path.δ)
      (S.comp (h.path.B.cons h.path.hδ)).carrier h.t := by
  refine (support_supports h.t).mono ?_
  simp only [Support.comp_carrier, exists_and_left, preimage_setOf_eq]
  rintro c hc
  have := Support.Precedes.fuzz A N h c hc
  rw [h.path.hA] at hSi
  rw [← hSi] at this
  obtain ⟨j, hj₁, h⟩ := hS.precedes hi _ this
  exact ⟨j, hj₁, h.symm⟩

theorem before_comp_supports' (S : Support β) (hS : S.Strong)
    {i : κ} (hi : i < S.max) {A : ExtendedIndex β}
    {N : NearLitter} (h : InflexibleCoe A N.1) (hSi : S.f i hi = ⟨A, inr N⟩) :
    MulAction.Supports (Allowable h.path.δ)
      (S.comp (h.path.B.cons h.path.hδ)).carrier h.t.set := by
  intro ρ hρ
  rw [← Tangle.smul_set, before_comp_supports S hS hi h hSi ρ hρ]

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
        {j | ∃ hj, ∃ (N' : NearLitter), S.f j hj = ⟨A, inr N'⟩ ∧ N'.1 = N.1}
        /- TODO: This term can be inferred from all of the `atom_spec` results.
        The same goes for the other near-litter cases. -/
        (fun j => {k | ∃ hj hk, ∃ (a : Atom) (N' : NearLitter),
          N'.1 = N.1 ∧ a ∈ (N : Set Atom) ∆ N' ∧
          S.f j hj = ⟨A, inr N'⟩ ∧ S.f k hk = ⟨A, inl a⟩})
  inflexibleCoe_spec (i : κ) (hi : i < S.max) (A : ExtendedIndex β) (N : NearLitter)
      (h : InflexibleCoe A N.1) (hSi : S.f i hi = ⟨A, inr N⟩) :
      σ.f i (hi.trans_eq max_eq_max) = SpecCondition.inflexibleCoe A h.path
        (CodingFunction.code (S.comp (h.path.B.cons h.path.hδ))
          h.t.set (before_comp_supports' S hS hi h hSi))
        (fun j => {k | ∃ hj hk, ∃ (a : Atom) (N' : NearLitter),
          N'.1 = N.1 ∧ a ∈ (N : Set Atom) ∆ N' ∧
          S.f j hj = ⟨A, inr N'⟩ ∧ S.f k hk = ⟨A, inl a⟩})
        h.t.support.max
        (fun j => {k | ∃ (hj : j < h.t.support.max) (hk : k < S.max),
          ⟨(h.path.B.cons h.path.hδ).comp (h.t.support.f j hj).1, (h.t.support.f j hj).2⟩ =
            S.f k hk})
  inflexibleBot_spec (i : κ) (hi : i < S.max) (A : ExtendedIndex β) (N : NearLitter)
      (h : InflexibleBot A N.1) :
      S.f i hi = ⟨A, inr N⟩ →
      σ.f i (hi.trans_eq max_eq_max) = SpecCondition.inflexibleBot A h.path
        {j | ∃ hj, S.f j hj = ⟨h.path.B.cons (bot_lt_coe _), inl h.a⟩}
        (fun j => {k | ∃ hj hk, ∃ (a : Atom) (N' : NearLitter),
          N'.1 = N.1 ∧ a ∈ (N : Set Atom) ∆ N' ∧
          S.f j hj = ⟨A, inr N'⟩ ∧ S.f k hk = ⟨A, inl a⟩})

theorem Specifies.of_eq_atom {σ : Spec β} {S : Support β} {hS : S.Strong} (h : σ.Specifies S hS)
    {i : κ} {hi : i < σ.max} {A : ExtendedIndex β} {s t : Set κ}
    (hi' : σ.f i hi = SpecCondition.atom A s t) :
    ∃ a, S.f i (hi.trans_eq h.max_eq_max.symm) = ⟨A, inl a⟩ := by
  have hiS := hi.trans_eq h.max_eq_max.symm
  set c := S.f i hiS with hc
  obtain ⟨B, a | N⟩ := c
  · cases hi'.symm.trans (h.atom_spec i hiS B a hc.symm)
    exact ⟨a, rfl⟩
  obtain (hN | ⟨⟨hN⟩⟩ | ⟨⟨hN⟩⟩) := flexible_cases' B N.1
  · cases hi'.symm.trans (h.flexible_spec i hiS B N hN hc.symm)
  · cases hi'.symm.trans (h.inflexibleBot_spec i hiS B N hN hc.symm)
  · cases hi'.symm.trans (h.inflexibleCoe_spec i hiS B N hN hc.symm)

theorem Specifies.of_eq_flexible {σ : Spec β} {S : Support β} {hS : S.Strong} (h : σ.Specifies S hS)
    {i : κ} {hi : i < σ.max} {A : ExtendedIndex β} {s : Set κ} {t : κ → Set κ}
    (hi' : σ.f i hi = SpecCondition.flexible A s t) :
    ∃ N, Flexible A N.1 ∧ S.f i (hi.trans_eq h.max_eq_max.symm) = ⟨A, inr N⟩ := by
  have hiS := hi.trans_eq h.max_eq_max.symm
  set c := S.f i hiS with hc
  obtain ⟨B, a | N⟩ := c
  · cases hi'.symm.trans (h.atom_spec i hiS B a hc.symm)
  obtain (hN | ⟨⟨hN⟩⟩ | ⟨⟨hN⟩⟩) := flexible_cases' B N.1
  · cases hi'.symm.trans (h.flexible_spec i hiS B N hN hc.symm)
    exact ⟨N, hN, rfl⟩
  · cases hi'.symm.trans (h.inflexibleBot_spec i hiS B N hN hc.symm)
  · cases hi'.symm.trans (h.inflexibleCoe_spec i hiS B N hN hc.symm)

theorem Specifies.of_eq_inflexibleCoe {σ : Spec β} {S : Support β} {hS : S.Strong}
    (h : σ.Specifies S hS)
    {i : κ} {hi : i < σ.max} {A : ExtendedIndex β} {P : InflexibleCoePath A}
    {χ : CodingFunction P.δ} {s : κ → Set κ} {m : κ} {u : κ → Set κ}
    (hi' : σ.f i hi = SpecCondition.inflexibleCoe A P χ s m u) :
    ∃ N t, N.1 = fuzz P.hδε t ∧ S.f i (hi.trans_eq h.max_eq_max.symm) = ⟨A, inr N⟩ := by
  have hiS := hi.trans_eq h.max_eq_max.symm
  set c := S.f i hiS with hc
  obtain ⟨B, a | N⟩ := c
  · cases hi'.symm.trans (h.atom_spec i hiS B a hc.symm)
  obtain (hN | ⟨⟨hN⟩⟩ | ⟨⟨hN⟩⟩) := flexible_cases' B N.1
  · cases hi'.symm.trans (h.flexible_spec i hiS B N hN hc.symm)
  · cases hi'.symm.trans (h.inflexibleBot_spec i hiS B N hN hc.symm)
  · cases hi'.symm.trans (h.inflexibleCoe_spec i hiS B N hN hc.symm)
    exact ⟨N, hN.t, hN.hL, rfl⟩

theorem Specifies.of_eq_inflexibleBot {σ : Spec β} {S : Support β} {hS : S.Strong}
    (h : σ.Specifies S hS)
    {i : κ} {hi : i < σ.max} {A : ExtendedIndex β} {P : InflexibleBotPath A}
    {s : Set κ} {t : κ → Set κ}
    (hi' : σ.f i hi = SpecCondition.inflexibleBot A P s t) :
    ∃ N a, N.1 = fuzz (bot_ne_coe (a := P.ε)) a ∧
      S.f i (hi.trans_eq h.max_eq_max.symm) = ⟨A, inr N⟩ := by
  have hiS := hi.trans_eq h.max_eq_max.symm
  set c := S.f i hiS with hc
  obtain ⟨B, a | N⟩ := c
  · cases hi'.symm.trans (h.atom_spec i hiS B a hc.symm)
  obtain (hN | ⟨⟨hN⟩⟩ | ⟨⟨hN⟩⟩) := flexible_cases' B N.1
  · cases hi'.symm.trans (h.flexible_spec i hiS B N hN hc.symm)
  · cases hi'.symm.trans (h.inflexibleBot_spec i hiS B N hN hc.symm)
    exact ⟨N, hN.a, hN.hL, rfl⟩
  · cases hi'.symm.trans (h.inflexibleCoe_spec i hiS B N hN hc.symm)

end Spec

end ConNF
