import ConNF.FOA.Basic.Flexible
import ConNF.Counting.CodingFunction

/-!
# Specifications
-/

open Quiver Set Sum WithBot

open scoped Classical Cardinal

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ}

mutual
  inductive SpecCondition : Λ → Type u
    | atom {β : Λ} (A : ExtendedIndex β) (others : Set κ) (nearLitters: Set κ) :
        SpecCondition β
    | flexible {β : Λ} (A : ExtendedIndex β) :
        SpecCondition β
    | inflexibleCoe {β : Λ} (A : ExtendedIndex β) (h : InflexibleCoePath A)
        (χ : CodingFunction h.δ) (σ : Spec h.δ) : SpecCondition β
    | inflexibleBot {β : Λ} (A : ExtendedIndex β) (h : InflexibleBotPath A) (atoms : Set κ) :
        SpecCondition β

  inductive Spec : Λ → Type u
    | mk {β : Λ} (max : κ) : ((i : κ) → i < max → SpecCondition β) → Spec β
end

namespace Spec

def max : Spec β → κ
  | mk max _ => max

def f : (σ : Spec β) → (i : κ) → i < σ.max → SpecCondition β
  | mk _ f => f

@[simp]
theorem mk_max (max : κ) (f : (i : κ) → i < max → SpecCondition β) :
    (mk max f).max = max :=
  rfl

@[simp]
theorem mk_f (max : κ) (f : (i : κ) → i < max → SpecCondition β) :
    (mk max f).f = f :=
  rfl

@[ext]
theorem ext {σ τ : Spec β} (h₁ : σ.max = τ.max)
    (h₂ : ∀ (i : κ) (hσ : i < σ.max) (hτ : i < τ.max), σ.f i hσ = τ.f i hτ) : σ = τ := by
  obtain ⟨max, f⟩ := σ
  obtain ⟨max', f'⟩ := τ
  subst h₁
  simp only [mk_max, mk.injEq, heq_eq_eq, true_and]
  ext i hi
  exact h₂ i hi hi

end Spec

theorem Allowable.comp_smul_support_comp {β γ : TypeIndex} [LeLevel β] [LeLevel γ]
    (S : Support β) (ρ : Allowable β) (A : Path β γ) :
    Allowable.comp A ρ • S.comp A = (ρ • S).comp A := by
  by_cases h : ∃ B : ExtendedIndex γ, ∃ x : Atom ⊕ NearLitter, ⟨A.comp B, x⟩ ∈ S
  · rw [Support.comp_eq_of_exists h, Support.comp_eq_of_exists]
    swap
    · obtain ⟨B, x, i, hi, hx⟩ := h
      exact ⟨B, Allowable.toStructPerm ρ (A.comp B) • x, i, hi, congr_arg (ρ • ·) hx⟩
    sorry
  · push_neg at h
    rw [Support.comp_eq_of_forall h, Support.comp_eq_of_forall]
    swap
    · rintro B x ⟨i, hi, hx⟩
      refine h B (Allowable.toStructPerm ρ⁻¹ (A.comp B) • x) ⟨i, hi, ?_⟩
      symm at hx
      rw [Support.smul_f, smul_eq_iff_eq_inv_smul] at hx
      rw [hx]
      rfl
    sorry

instance : WellFoundedRelation Λ where
  rel := (· < ·)
  wf := IsWellFounded.wf

open scoped Classical in
noncomputable def specFor {β : Λ} (S : Support β) : SupportCondition β → SpecCondition β
  | ⟨A, inl a⟩ => SpecCondition.atom A
      {i | ∃ hi : i < S.max, S.f i hi = ⟨A, inl a⟩}
      {i | ∃ N : NearLitter, a ∈ N ∧ ∃ hi : i < S.max, S.f i hi = ⟨A, inr N⟩}
  | ⟨A, inr N⟩ =>
      if h : Nonempty (InflexibleCoe A N.1) then
        SpecCondition.inflexibleCoe A h.some.path
          (CodingFunction.code h.some.t.support h.some.t (support_supports _))
          (have : h.some.path.δ < β := coe_lt_coe.mp (h.some.δ_lt_β);
            (Spec.mk _ (fun i hi => specFor
              (S.comp (h.some.path.B.cons h.some.path.hδ) + h.some.t.support)
              ((S.comp (h.some.path.B.cons h.some.path.hδ) + h.some.t.support).f i hi))))
      else if h : Nonempty (InflexibleBot A N.1) then
        SpecCondition.inflexibleBot A h.some.path
          {i | ∃ hi : i < S.max, S.f i hi = ⟨h.some.path.B.cons (bot_lt_coe _), inl h.some.a⟩}
      else
        SpecCondition.flexible A
termination_by
  specFor β S c => β

noncomputable def Support.spec {β : Λ} (S : Support β) : Spec β :=
  Spec.mk S.max (fun i hi => specFor S (S.f i hi))

@[simp]
theorem specFor_atom {S : Support β} {A : ExtendedIndex β} {a : Atom} :
    specFor S ⟨A, inl a⟩ = SpecCondition.atom A
      {i | ∃ hi : i < S.max, S.f i hi = ⟨A, inl a⟩}
      {i | ∃ N : NearLitter, a ∈ N ∧ ∃ hi : i < S.max, S.f i hi = ⟨A, inr N⟩} := by
  unfold specFor
  rfl

theorem specFor_inflexibleCoe {S : Support β}
    {A : ExtendedIndex β} {N : NearLitter} (h : InflexibleCoe A N.1) :
    specFor S ⟨A, inr N⟩ = SpecCondition.inflexibleCoe A h.path
      (CodingFunction.code h.t.support h.t (support_supports _))
      (S.comp (h.path.B.cons h.path.hδ) + h.t.support).spec := by
  unfold specFor
  have : Nonempty (InflexibleCoe A N.1) := ⟨h⟩
  rw [dif_pos this, Subsingleton.elim h this.some]
  rfl

theorem specFor_inflexibleBot {S : Support β}
    {A : ExtendedIndex β} {N : NearLitter} (h : InflexibleBot A N.1) :
    specFor S ⟨A, inr N⟩ = SpecCondition.inflexibleBot A h.path
      {i | ∃ hi : i < S.max, S.f i hi = ⟨h.path.B.cons (bot_lt_coe _), inl h.a⟩} := by
  unfold specFor
  have : Nonempty (InflexibleBot A N.1) := ⟨h⟩
  rw [dif_neg, dif_pos this, Subsingleton.elim h this.some]
  rintro ⟨h'⟩
  exact inflexibleBot_inflexibleCoe h h'

theorem specFor_flexible {S : Support β}
    {A : ExtendedIndex β} {N : NearLitter} (h : Flexible A N.1) :
    specFor S ⟨A, inr N⟩ = SpecCondition.flexible A := by
  unfold specFor
  rw [flexible_iff_not_inflexibleBot_inflexibleCoe] at h
  rw [dif_neg (not_nonempty_iff.mpr h.1), dif_neg (not_nonempty_iff.mpr h.2)]

@[simp]
theorem spec_max (S : Support β) : S.spec.max = S.max :=
  rfl

@[simp]
theorem spec_f {S : Support β} (i : κ) (hi : i < S.spec.max) :
    S.spec.f i hi = specFor S (S.f i hi) :=
  rfl

variable [LeLevel β]

theorem specFor_smul_atom {S : Support β} {A : ExtendedIndex β} {a : Atom} {ρ : Allowable β} :
    specFor (ρ • S) ⟨A, inl (Allowable.toStructPerm ρ A • a)⟩ = specFor S ⟨A, inl a⟩ := by
  simp only [Allowable.smul_supportCondition, smul_inl, specFor_atom, Support.smul_f,
    SupportCondition.ext_iff, Support.smul_max, SpecCondition.atom.injEq, true_and]
  constructor
  · ext i
    constructor
    · rintro ⟨hi, rfl, h⟩
      rw [← smul_inl, smul_left_cancel_iff] at h
      exact ⟨hi, rfl, h⟩
    · rintro ⟨hi, rfl, h⟩
      refine ⟨hi, rfl, ?_⟩
      rw [← smul_inl, smul_left_cancel_iff]
      exact h
  · ext i
    constructor
    · rintro ⟨N, hN, hi, rfl, h⟩
      refine ⟨(Allowable.toStructPerm ρ (Support.f S i hi).path)⁻¹ • N, hN, hi, rfl, ?_⟩
      rw [← smul_inr, ← h, inv_smul_smul]
    · rintro ⟨N, hN, hi, rfl, h⟩
      refine ⟨Allowable.toStructPerm ρ (Support.f S i hi).path • N, ?_, hi, rfl, ?_⟩
      · rw [← inv_smul_smul (Allowable.toStructPerm ρ (Support.f S i hi).path) a] at hN
        exact hN
      · rw [← smul_inr, ← h]

theorem specFor_smul_flexible {S : Support β} {A : ExtendedIndex β} {N : NearLitter}
      (h : Flexible A N.1) {ρ : Allowable β} :
    specFor (ρ • S) ⟨A, inr (Allowable.toStructPerm ρ A • N)⟩ = specFor S ⟨A, inr N⟩ := by
  rw [specFor_flexible h, specFor_flexible]
  rw [NearLitterPerm.smul_nearLitter_fst, flexible_smul]
  exact h

theorem specFor_smul_inflexibleBot {S : Support β} {A : ExtendedIndex β} {N : NearLitter}
      (h : InflexibleBot A N.1) {ρ : Allowable β} :
    specFor (ρ • S) ⟨A, inr (Allowable.toStructPerm ρ A • N)⟩ = specFor S ⟨A, inr N⟩ := by
  rw [specFor_inflexibleBot h, specFor_inflexibleBot]
  swap
  · exact h.smul ρ
  simp only [NearLitterPerm.smul_nearLitter_fst, inflexibleBot_smul_path, Support.smul_f,
    inflexibleBot_smul_a, ofBot_smul, Allowable.toStructPerm_apply, Support.smul_max,
    SpecCondition.inflexibleBot.injEq, heq_eq_eq, true_and]
  ext
  constructor
  · rintro ⟨hi, h⟩
    have := congr_arg (ρ⁻¹ • ·) h
    simp only [Allowable.smul_supportCondition, map_inv, Tree.inv_apply, inv_smul_smul,
      NearLitterPerm.smul_nearLitter_fst, inflexibleBot_smul_path, smul_inl,
      SupportCondition.mk.injEq] at this
    exact ⟨hi, SupportCondition.ext _ _ this.1 this.2⟩
  · rintro ⟨hi, h⟩
    refine ⟨hi, ?_⟩
    rw [h]
    rfl

theorem specFor_smul_inflexibleCoe {S : Support β} {A : ExtendedIndex β} {N : NearLitter}
      (h : InflexibleCoe A N.1) {ρ : Allowable β}
      (ih : ∀ γ < β, [LeLevel γ] → ∀ S : Support γ, ∀ ρ : Allowable γ, (ρ • S).spec = S.spec) :
    specFor (ρ • S) ⟨A, inr (Allowable.toStructPerm ρ A • N)⟩ = specFor S ⟨A, inr N⟩ := by
  rw [specFor_inflexibleCoe h, specFor_inflexibleCoe]
  swap
  · exact h.smul ρ
  simp only [NearLitterPerm.smul_nearLitter_fst, inflexibleCoe_smul_path, inflexibleCoe_smul_t,
    SpecCondition.inflexibleCoe.injEq, heq_eq_eq, true_and]
  constructor
  · refine CodingFunction.ext h.t.support ?_ ?_ ?_
    · sorry
    · sorry
    · sorry
  · rw [← ih h.path.δ (coe_lt_coe.mp h.δ_lt_β)
      (S.comp (h.path.B.cons h.path.hδ) + h.t.support) (Allowable.comp (h.path.B.cons h.path.hδ) ρ)]
    simp only [NearLitterPerm.smul_nearLitter_fst, inflexibleCoe_smul_path, Support.smul_add,
      smul_support, Allowable.comp_smul_support_comp]

theorem specFor_smul {β : Λ} [i : LeLevel β]
    {S : Support β} {c : SupportCondition β} {ρ : Allowable β} :
    specFor (ρ • S) (ρ • c) = specFor S c := by
  revert i S c ρ
  have := WellFounded.induction
    (C := fun (β : Λ) => (i : LeLevel β) →
      ∀ (S : Support β) (c : SupportCondition β) (ρ : Allowable β),
      specFor (ρ • S) (ρ • c) = specFor S c)
    (inferInstanceAs (IsWellFounded Λ (· < ·))).wf
  refine this β ?_
  intro β ih i S c ρ
  obtain ⟨A, a | N⟩ := c
  · exact specFor_smul_atom
  obtain (h | ⟨⟨h⟩⟩ | ⟨⟨h⟩⟩) := flexible_cases' A N.1
  · exact specFor_smul_flexible h
  · exact specFor_smul_inflexibleBot h
  · refine specFor_smul_inflexibleCoe h ?_
    intro γ hγ _ S' ρ'
    ext i hσ
    · rfl
    · exact ih γ hγ inferInstance S' (S'.f i hσ) ρ'

theorem smul_spec {β : Λ} [LeLevel β] {S : Support β} {ρ : Allowable β} :
    (ρ • S).spec = S.spec :=
  Spec.ext rfl (fun _ _ _ => specFor_smul)

end ConNF
