import ConNF.Counting.Spec

open Quiver Set Sum WithBot

open scoped Classical Cardinal symmDiff

universe u

namespace ConNF

variable [Params.{u}] [Level] [BasePositions] [CountingAssumptions] {β : Λ}

noncomputable def Support.spec (S : Support β) (hS : S.Strong) : Spec β where
  max := S.max
  f i hi :=
    if h : ∃ A a, S.f i hi = ⟨A, inl a⟩ then
      let A := h.choose
      let a := h.choose_spec.choose
      SpecCondition.atom A
          {j | ∃ hj, S.f j hj = ⟨A, inl a⟩} {j | ∃ hj N, S.f j hj = ⟨A, inr N⟩ ∧ a ∈ N}
    else if h : ∃ A N, S.f i hi = ⟨A, inr N⟩ then
      let A := h.choose
      let N := h.choose_spec.choose
      if h₁ : Nonempty (InflexibleCoe A N.1) then
        SpecCondition.inflexibleCoe A h₁.some.path
          (CodingFunction.code ((S.before i hi).comp (h₁.some.path.B.cons h₁.some.path.hδ))
            (Shell.ofTangle h₁.some.t)
            (Spec.before_comp_supports' S hS hi h₁.some h.choose_spec.choose_spec))
          (CodingFunction.code_strong _ _ _
            (Support.comp_strong _ _ (Support.before_strong _ _ _ hS)))
          (fun j => {k | ∃ hj hk, ∃ (a : Atom) (N' : NearLitter),
            N'.1 = N.1 ∧ a ∈ (N : Set Atom) ∆ N' ∧
            S.f j hj = ⟨A, inr N'⟩ ∧ S.f k hk = ⟨A, inl a⟩})
          h₁.some.t.support.max
        (fun j => {k | ∃ (hj : j < h₁.some.t.support.max) (hk : k < S.max),
          ⟨(h₁.some.path.B.cons h₁.some.path.hδ).comp (h₁.some.t.support.f j hj).1,
            (h₁.some.t.support.f j hj).2⟩ = S.f k hk})
      else if h₂ : Nonempty (InflexibleBot A N.1) then
        SpecCondition.inflexibleBot A h₂.some.path
          {j | ∃ hj, S.f j hj = ⟨h₂.some.path.B.cons (bot_lt_coe _), inl h₂.some.a⟩}
          (fun j => {k | ∃ hj hk, ∃ (a : Atom) (N' : NearLitter),
              N'.1 = N.1 ∧ a ∈ (N : Set Atom) ∆ N' ∧
              S.f j hj = ⟨A, inr N'⟩ ∧ S.f k hk = ⟨A, inl a⟩})
      else
        SpecCondition.flexible A
          {j | ∃ hj, ∃ (N' : NearLitter), S.f j hj = ⟨A, inr N'⟩ ∧ N'.1 = N.1}
          (fun j => {k | ∃ hj hk, ∃ (a : Atom) (N' : NearLitter),
            N'.1 = N.1 ∧ a ∈ (N : Set Atom) ∆ N' ∧
            S.f j hj = ⟨A, inr N'⟩ ∧ S.f k hk = ⟨A, inl a⟩})
    else
      SpecCondition.atom (S.f i hi).1 ∅ ∅

theorem Support.spec_specifies (S : Support β) (hS : S.Strong) : (S.spec hS).Specifies S hS := by
  constructor
  case max_eq_max => rfl
  case atom_spec =>
    intro i hi A a h
    unfold spec
    dsimp only
    have : ∃ A a, S.f i hi = ⟨A, inl a⟩ := ⟨A, a, h⟩
    rw [dif_pos this]
    have := h.symm.trans this.choose_spec.choose_spec
    simp only [Address.mk.injEq, inl.injEq] at this
    simp only [this, and_self]
  case flexible_spec =>
    intro i hi A N hN h
    unfold spec
    dsimp only
    have h₁ : ¬∃ A a, S.f i hi = ⟨A, inl a⟩
    · rintro ⟨B, b, h'⟩
      cases h.symm.trans h'
    have h₂ : ∃ A N, S.f i hi = ⟨A, inr N⟩ := ⟨A, N, h⟩
    rw [dif_neg h₁, dif_pos h₂]
    have := h.symm.trans h₂.choose_spec.choose_spec
    simp only [Address.mk.injEq, inr.injEq] at this
    simp only [this] at hN ⊢
    rw [dif_neg, dif_neg]
    · rw [flexible_iff_not_inflexibleBot_inflexibleCoe] at hN
      rw [not_nonempty_iff]
      exact hN.1
    · rw [flexible_iff_not_inflexibleBot_inflexibleCoe] at hN
      rw [not_nonempty_iff]
      exact hN.2
  case inflexibleCoe_spec =>
    rintro i hi A N hN h
    unfold spec
    dsimp only
    have h₁ : ¬∃ A a, S.f i hi = ⟨A, inl a⟩
    · rintro ⟨B, b, h'⟩
      cases h.symm.trans h'
    have h₂ : ∃ A N, S.f i hi = ⟨A, inr N⟩ := ⟨A, N, h⟩
    rw [dif_neg h₁, dif_pos h₂]
    cases h.symm.trans h₂.choose_spec.choose_spec
    have h₁ : Nonempty (InflexibleCoe h₂.choose h₂.choose_spec.choose.1) := ⟨hN⟩
    rw [dif_pos h₁]
    have : hN = h₁.some := Subsingleton.elim _ _
    cases this
    rfl
  case inflexibleBot_spec =>
    rintro i hi A N hN h
    unfold spec
    dsimp only
    have h₁ : ¬∃ A a, S.f i hi = ⟨A, inl a⟩
    · rintro ⟨B, b, h'⟩
      cases h.symm.trans h'
    have h₂ : ∃ A N, S.f i hi = ⟨A, inr N⟩ := ⟨A, N, h⟩
    rw [dif_neg h₁, dif_pos h₂]
    cases h.symm.trans h₂.choose_spec.choose_spec
    have h₁ : ¬Nonempty (InflexibleCoe h₂.choose h₂.choose_spec.choose.1)
    · rintro ⟨h⟩
      exact inflexibleBot_inflexibleCoe hN h
    have h₂ : Nonempty (InflexibleBot h₂.choose h₂.choose_spec.choose.1) := ⟨hN⟩
    rw [dif_neg h₁, dif_pos h₂]
    have : hN = h₂.some := Subsingleton.elim _ _
    cases this
    rfl

end ConNF
