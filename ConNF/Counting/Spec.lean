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

open scoped Classical in
noncomputable def SupportCondition.comp (c : SupportCondition β) {γ : TypeIndex}
    (A : Path (β : TypeIndex) γ) (otherwise : SupportCondition γ) : SupportCondition γ :=
  if h : ∃ B : ExtendedIndex γ, c.path = A.comp B then
    ⟨h.choose, c.value⟩
  else
    otherwise

noncomputable def Support.comp (S : Support β) {γ : TypeIndex} (A : Path (β : TypeIndex) γ) :
    Support γ :=
  if h : ∃ B : ExtendedIndex γ, ∃ x : Atom ⊕ NearLitter, ⟨A.comp B, x⟩ ∈ S then
    ⟨S.max, fun i hi => (S.f i hi).comp A ⟨h.choose, h.choose_spec.choose⟩⟩
  else
    ⟨0, fun _ hi => (κ_not_lt_zero _ hi).elim⟩

instance : WellFoundedRelation Λ where
  rel := (· < ·)
  wf := IsWellFounded.wf

instance : WellFoundedRelation Bool where
  rel := (· < ·)
  wf := IsWellFounded.wf

open scoped Classical in
mutual
  noncomputable def specFor {β : Λ} (S : Support β) : SupportCondition β → SpecCondition β
    | ⟨A, inl a⟩ => SpecCondition.atom A
        {i | ∃ hi : i < S.max, S.f i hi = ⟨A, inl a⟩}
        {i | ∃ N : NearLitter, a ∈ N ∧ ∃ hi : i < S.max, S.f i hi = ⟨A, inr N⟩}
    | ⟨A, inr N⟩ =>
        if h : Nonempty (InflexibleCoe A N.1) then
          SpecCondition.inflexibleCoe A h.some.path
            (CodingFunction.code h.some.t.support h.some.t (support_supports _))
            (have : h.some.path.δ < β := coe_lt_coe.mp (h.some.δ_lt_β);
              spec (S.comp (h.some.path.B.cons h.some.path.hδ) + h.some.t.support))
        else if h : Nonempty (InflexibleBot A N.1) then
          SpecCondition.inflexibleBot A h.some.path
            {i | ∃ hi : i < S.max, S.f i hi = ⟨h.some.path.B.cons (bot_lt_coe _), inl h.some.a⟩}
        else
          SpecCondition.flexible A

  noncomputable def spec {β : Λ} (S : Support β) : Spec β :=
    Spec.mk S.max (fun i hi => specFor S (S.f i hi))
end
termination_by
  specFor β S c => (β, false)
  spec β S => (β, true)

end ConNF
