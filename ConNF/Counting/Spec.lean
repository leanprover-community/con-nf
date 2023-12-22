import ConNF.Mathlib.Support
import ConNF.FOA.Basic.Flexible
import ConNF.Counting.CodingFunction

/-!
# Specifications
-/

open Quiver Set Sum WithBot

open scoped Classical Cardinal

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions]

section comp

variable {β γ : TypeIndex} {A : Quiver.Path β γ}

open scoped Classical in
noncomputable def SupportCondition.comp (A : Quiver.Path β γ) (c : SupportCondition β)
    (otherwise : SupportCondition γ) : SupportCondition γ :=
  if h : ∃ B : ExtendedIndex γ, c.path = A.comp B then
    ⟨h.choose, c.value⟩
  else
    otherwise

theorem SupportCondition.comp_eq_of_eq_comp {c : SupportCondition β}
    {otherwise : SupportCondition γ} (B : ExtendedIndex γ) (h : c.path = A.comp B) :
    c.comp A otherwise = ⟨B, c.value⟩ := by
  have : ∃ B : ExtendedIndex γ, c.path = A.comp B := ⟨B, h⟩
  have hB : this.choose = B := Path.comp_injective_right A (this.choose_spec.symm.trans h)
  rw [comp, dif_pos this, hB]

theorem SupportCondition.comp_eq_of_not_exists {c : SupportCondition β}
    {otherwise : SupportCondition γ} (h : ¬∃ B : ExtendedIndex γ, c.path = A.comp B) :
    c.comp A otherwise = otherwise :=
  by rw [comp, dif_neg h]

@[simp]
theorem SupportCondition.comp_smul_comp [LeLevel β] [LeLevel γ] (c : SupportCondition β)
    (otherwise : SupportCondition γ) (ρ : Allowable β) :
    Allowable.comp A ρ • (c.comp A otherwise) =
    (ρ • c).comp A (Allowable.comp A ρ • otherwise) := by
  by_cases h : ∃ B : ExtendedIndex γ, c.path = A.comp B
  · obtain ⟨B, h⟩ := h
    rw [comp_eq_of_eq_comp B h, comp_eq_of_eq_comp B (by exact h),
      Allowable.smul_supportCondition, Allowable.smul_supportCondition, h]
    simp only [Allowable.toStructPerm_comp, Tree.comp_apply]
  · rw [comp_eq_of_not_exists h, comp_eq_of_not_exists (by exact h)]

def Support.pathEnumeration (S : Support β) : Enumeration (ExtendedIndex β) :=
  S.enum.image SupportCondition.path

@[simp]
theorem Support.pathEnumeration_f (S : Support β) (i : κ) (hi : i < S.pathEnumeration.max) :
    S.pathEnumeration.f i hi = (S.f i hi).path :=
  rfl

@[simp]
theorem Support.pathEnumeration_smul [LeLevel β] (S : Support β) (ρ : Allowable β) :
    (ρ • S).pathEnumeration = S.pathEnumeration :=
  rfl

def Support.canComp (A : Quiver.Path β γ) (E : Enumeration (ExtendedIndex β)) : Prop :=
  ∃ i : κ, ∃ hi : i < E.max, ∃ C : ExtendedIndex γ, A.comp C = E.f i hi

noncomputable def Support.compIndex (E : Enumeration (ExtendedIndex β)) (h : canComp A E) : κ :=
  E.chooseIndex (fun B => ∃ C, A.comp C = B) h

theorem Support.compIndex_lt (E : Enumeration (ExtendedIndex β)) (h : canComp A E) :
    compIndex E h < E.max :=
  Enumeration.chooseIndex_lt (p := (fun B => ∃ C, A.comp C = B)) h

noncomputable def Support.compIndex_tail (E : Enumeration (ExtendedIndex β)) (h : canComp A E) :
    ExtendedIndex γ :=
  (Enumeration.chooseIndex_spec (p := (fun B => ∃ C, A.comp C = B)) h).choose

theorem Support.compIndex_spec (E : Enumeration (ExtendedIndex β)) (h : canComp A E) :
    A.comp (compIndex_tail E h) = E.f (compIndex E h) (compIndex_lt E h) :=
  (Enumeration.chooseIndex_spec (p := (fun B => ∃ C, A.comp C = B)) h).choose_spec

open scoped Classical in
noncomputable def Support.comp' (A : Quiver.Path β γ) (S : Support β) :
    Enumeration (SupportCondition γ) :=
  if h : canComp A S.pathEnumeration then
    ⟨S.max, fun i hi => (S.f i hi).comp A
      ⟨compIndex_tail S.pathEnumeration h,
        (S.f (compIndex S.pathEnumeration h) (compIndex_lt _ _)).value⟩⟩
  else
    ⟨0, fun _ hi => (κ_not_lt_zero _ hi).elim⟩

variable {S : Support β}

theorem Support.comp'_eq_pos (h : canComp A S.pathEnumeration) :
    S.comp' A = ⟨S.max, fun i hi => (S.f i hi).comp A
      ⟨compIndex_tail S.pathEnumeration h,
        (S.f (compIndex S.pathEnumeration h) (compIndex_lt _ _)).value⟩⟩ :=
  by rw [Support.comp', dif_pos h]

theorem Support.comp'_eq_neg (h : ¬canComp A S.pathEnumeration) :
    S.comp' A = ⟨0, fun _ hi => (κ_not_lt_zero _ hi).elim⟩ :=
  by rw [Support.comp', dif_neg h]

theorem Allowable.comp_smul_support_comp' {β γ : TypeIndex} [LeLevel β] [LeLevel γ]
    (S : Support β) (ρ : Allowable β) (A : Path β γ) :
    Allowable.comp A ρ • S.comp' A = (ρ • S).comp' A := by
  by_cases h : Support.canComp A S.pathEnumeration
  · rw [Support.comp'_eq_pos h, Support.comp'_eq_pos]
    swap
    · exact h
    refine Enumeration.ext _ _ rfl (heq_of_eq ?_)
    ext i hi : 2
    simp only [Enumeration.smul_f, SupportCondition.comp_smul_comp, smul_support_f,
      Support.pathEnumeration_smul]
    refine congr_arg _ ?_
    rw [Allowable.smul_supportCondition, Allowable.smul_supportCondition,
      toStructPerm_comp, Tree.comp_apply, SupportCondition.mk.injEq,
      Support.compIndex_spec S.pathEnumeration h, Support.pathEnumeration_f]
    exact ⟨rfl, rfl⟩
  · push_neg at h
    rw [Support.comp'_eq_neg h, Support.comp'_eq_neg (by rwa [Support.pathEnumeration_smul])]
    refine Enumeration.ext _ _ rfl (heq_of_eq ?_)
    ext i hi : 2
    cases κ_not_lt_zero _ hi

theorem Support.mem_of_mem_symmDiff_comp (A : Quiver.Path β γ) (S : Support β) (B : ExtendedIndex γ)
    (N₁ N₂ : NearLitter) (a : Atom) :
    N₁.1 = N₂.1 → a ∈ (N₁ : Set Atom) ∆ N₂ →
    ⟨B, inr N₁⟩ ∈ S.comp' A → ⟨B, inr N₂⟩ ∈ S.comp' A → ⟨B, inl a⟩ ∈ S.comp' A := by
  intro hN a hN₁ hN₂
  by_cases h : Support.canComp A S.pathEnumeration
  · rw [Support.comp'_eq_pos h] at hN₁ hN₂ ⊢
    sorry
  · rw [Support.comp'_eq_neg h] at hN₁ hN₂ ⊢
    sorry

noncomputable def Support.comp (A : Quiver.Path β γ) (S : Support β) : Support γ :=
  ⟨S.comp' A, mem_of_mem_symmDiff_comp A S⟩

theorem Allowable.comp_smul_support_comp {β γ : TypeIndex} [LeLevel β] [LeLevel γ]
    (S : Support β) (ρ : Allowable β) (A : Path β γ) :
    Allowable.comp A ρ • S.comp A = (ρ • S).comp A := by
  ext : 1
  simp only [Support.comp, Allowable.smul_mk_support, Allowable.comp_smul_support_comp']

end comp

variable {β : Λ}

mutual
  inductive SpecCondition : Λ → Type u
    | atom {β : Λ} (A : ExtendedIndex β) (others : Set κ) (nearLitters : Set κ) :
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

/-

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
  simp only [Allowable.smul_supportCondition, smul_inl, specFor_atom, Enumeration.smul_f,
    SupportCondition.ext_iff, Enumeration.smul_max, SpecCondition.atom.injEq, true_and]
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
      refine ⟨(Allowable.toStructPerm ρ (Enumeration.f S i hi).path)⁻¹ • N, hN, hi, rfl, ?_⟩
      rw [← smul_inr, ← h, inv_smul_smul]
    · rintro ⟨N, hN, hi, rfl, h⟩
      refine ⟨Allowable.toStructPerm ρ (Enumeration.f S i hi).path • N, ?_, hi, rfl, ?_⟩
      · rw [← inv_smul_smul (Allowable.toStructPerm ρ (Enumeration.f S i hi).path) a] at hN
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
  simp only [NearLitterPerm.smul_nearLitter_fst, inflexibleBot_smul_path, Enumeration.smul_f,
    inflexibleBot_smul_a, ofBot_smul, Allowable.toStructPerm_apply, Enumeration.smul_max,
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
    · rw [CodingFunction.mem_code]
      refine ⟨Allowable.comp (h.path.B.cons h.path.hδ) ρ⁻¹, ?_⟩
      simp only [NearLitterPerm.smul_nearLitter_fst, inflexibleCoe_smul_path, map_inv, smul_support,
        inv_smul_smul]
    · simp only [inflexibleCoe_smul_path, CodingFunction.mem_code_self]
    · have := CodingFunction.code_smul h.t.support h.t
          (Allowable.comp (h.path.B.cons h.path.hδ) ρ) ?_ ?_
      · simp only [smul_support, this]
      · rw [Enumeration.smul_carrier]
        exact (support_supports h.t).smul' (Allowable.comp (h.path.B.cons h.path.hδ) ρ)
      · exact support_supports h.t
  · rw [← ih h.path.δ (coe_lt_coe.mp h.δ_lt_β)
      (S.comp (h.path.B.cons h.path.hδ) + h.t.support) (Allowable.comp (h.path.B.cons h.path.hδ) ρ)]
    simp only [NearLitterPerm.smul_nearLitter_fst, inflexibleCoe_smul_path, Enumeration.smul_add,
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

-/

end ConNF
