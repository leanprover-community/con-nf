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

inductive SpecComponent (β : Λ) : Type u
  | atom (A : ExtendedIndex β) (others : Set κ) (nearLitters : Set κ) :
      SpecComponent β
  | flexible (A : ExtendedIndex β) (others : Set κ) :
      SpecComponent β
  | inflexibleCoe (A : ExtendedIndex β) (h : InflexibleCoePath A)
      (χ : CodingFunction h.δ) (r : κ → κ) :
      SpecComponent β
  | inflexibleBot (A : ExtendedIndex β) (h : InflexibleBotPath A) (atoms : Set κ) :
      SpecComponent β

inductive Spec : Λ → Type u
  | mk {β : Λ} (cond : Enumeration (SpecComponent β))
      (lower : ∀ {γ : Λ}, (γ : TypeIndex) < β → Path (β : TypeIndex) γ → Spec γ)
      (r : ∀ {γ : Λ}, (γ : TypeIndex) < β → Path (β : TypeIndex) γ → κ → κ) : Spec β

def Spec.cond : Spec β → Enumeration (SpecComponent β)
  | mk cond _ _ => cond

def Spec.lower : Spec β → ∀ {γ : Λ}, (γ : TypeIndex) < β → Path (β : TypeIndex) γ → Spec γ
  | mk _ lower _ => lower

def Spec.r : Spec β → ∀ {γ : Λ}, (γ : TypeIndex) < β → Path (β : TypeIndex) γ → κ → κ
  | mk _ _ r => r

inductive SpecifiesC (σ : Spec β) (S : Support β)
    (lS : ∀ {γ : Λ}, (hγ : (γ : TypeIndex) < β) → (A : Path (β : TypeIndex) γ) → Support γ) :
    SpecComponent β → Address β → Prop
  | atom (A : ExtendedIndex β) (a : Atom) :
    SpecifiesC σ S lS
      (SpecComponent.atom A
        {i | ∃ hi : i < S.max, S.f i hi = ⟨A, inl a⟩}
        {i | ∃ N : NearLitter, a ∈ N ∧ ∃ hi : i < S.max, S.f i hi = ⟨A, inr N⟩})
      ⟨A, inl a⟩
  | flexible (A : ExtendedIndex β)
    (N : NearLitter) (h : Flexible A N.1) :
    SpecifiesC σ S lS
      (SpecComponent.flexible A
        {i | ∃ hi : i < S.max, ∃ N', S.f i hi = ⟨A, inr N'⟩ ∧ N'.1 = N.1})
      ⟨A, inr N⟩
  | inflexibleCoe (A : ExtendedIndex β)
    (N : NearLitter) (h : InflexibleCoe A N.1) (r : κ → κ)
    (hr : ∀ i < h.t.support.max, r i < (lS (h.path.δ_lt_β) (h.path.B.cons h.path.hδ)).max)
    (hS : ∀ (i : κ) (hit : i < h.t.support.max),
      h.t.support.f i hit = (lS (h.path.δ_lt_β) (h.path.B.cons h.path.hδ)).f (r i) (hr i hit)) :
    SpecifiesC σ S lS
      (SpecComponent.inflexibleCoe A h.path
        (CodingFunction.code h.t.support h.t (support_supports _)) r)
      ⟨A, inr N⟩
  | inflexibleBot (A : ExtendedIndex β)
    (N : NearLitter) (h : InflexibleBot A N.1) :
    SpecifiesC σ S lS
      (SpecComponent.inflexibleBot A h.path
        {i | ∃ hi : i < S.max, S.f i hi = ⟨h.path.B.cons (bot_lt_coe _), inl h.a⟩})
      ⟨A, inr N⟩

/-- TODO: We really should make this definition much earlier. -/
def Address.comp {β γ : TypeIndex} (A : Quiver.Path β γ) (c : Address γ) : Address β :=
  ⟨A.comp c.1, c.2⟩

inductive Spec.Specifies : ∀ {β : Λ}, Spec β → Support β → Prop
  | mk {β : Λ} (σ : Spec β) (S : Support β)
    (max_eq_max : σ.cond.max = S.max)
    (lS : ∀ {γ : Λ}, (γ : TypeIndex) < β → Path (β : TypeIndex) γ → Support γ)
    (hlS₁ : ∀ {γ : Λ} (hγ : (γ : TypeIndex) < β) (A : Path (β : TypeIndex) γ),
      ∀ i < (lS hγ A).max, σ.r hγ A i < S.max)
    (hlS₂ : ∀ {γ : Λ} (hγ : (γ : TypeIndex) < β) (A : Path (β : TypeIndex) γ)
      (i : κ) (hi : i < (lS hγ A).max),
      ((lS hγ A).f i hi).comp A = S.f (σ.r hγ A i) (hlS₁ hγ A i hi))
    (hlS₃ : ∀ {γ : Λ} (hγ : (γ : TypeIndex) < β) (A : Path (β : TypeIndex) γ),
      (σ.lower hγ A).Specifies (lS hγ A))
    (cond : ∀ (i : κ) (hiσ : i < σ.cond.max) (hiS : i < S.max),
      SpecifiesC σ S lS (σ.cond.f i hiσ) (S.f i hiS)) :
    σ.Specifies S

variable {σ : Spec β} {S : Support β}
  {lS : ∀ {γ : Λ}, (hγ : (γ : TypeIndex) < β) → (A : Path (β : TypeIndex) γ) → Support γ}

theorem specifiesC_atom_right_iff (σc : SpecComponent β) (A : ExtendedIndex β) (a : Atom) :
    SpecifiesC σ S lS σc ⟨A, inl a⟩ ↔
      σc = SpecComponent.atom A
        {i | ∃ hi : i < S.max, S.f i hi = ⟨A, inl a⟩}
        {i | ∃ N : NearLitter, a ∈ N ∧ ∃ hi : i < S.max, S.f i hi = ⟨A, inr N⟩} := by
  constructor
  · rintro ⟨⟩
    rfl
  · rintro rfl
    exact SpecifiesC.atom A a

theorem specifiesC_flexible_right_iff (σc : SpecComponent β)
    (A : ExtendedIndex β) (N : NearLitter) (hN : Flexible A N.1) :
    SpecifiesC σ S lS σc ⟨A, inr N⟩ ↔
      σc = SpecComponent.flexible A
        {i | ∃ hi : i < S.max, ∃ N', S.f i hi = ⟨A, inr N'⟩ ∧ N'.1 = N.1} := by
  constructor
  · intro h
    cases h
    case flexible => rfl
    case inflexibleCoe r h hr hS =>
      rw [flexible_iff_not_inflexibleBot_inflexibleCoe] at hN
      exact hN.2.elim h
    case inflexibleBot h =>
      rw [flexible_iff_not_inflexibleBot_inflexibleCoe] at hN
      exact hN.1.elim h
  · rintro rfl
    exact SpecifiesC.flexible A N hN

theorem specifiesC_inflexibleCoe_right_iff (σc : SpecComponent β)
    (A : ExtendedIndex β) (N : NearLitter) (hN : InflexibleCoe A N.1) :
    SpecifiesC σ S lS σc ⟨A, inr N⟩ ↔
      ∃ (r : κ → κ)
      (hr : ∀ i < hN.t.support.max, r i < (lS (hN.path.δ_lt_β) (hN.path.B.cons hN.path.hδ)).max),
      (∀ (i : κ) (hit : i < hN.t.support.max), hN.t.support.f i hit =
        (lS (hN.path.δ_lt_β) (hN.path.B.cons hN.path.hδ)).f (r i) (hr i hit)) ∧
      σc = SpecComponent.inflexibleCoe A hN.path
        (CodingFunction.code hN.t.support hN.t (support_supports _)) r := by
  constructor
  · intro h
    cases h
    case flexible h' =>
      rw [flexible_iff_not_inflexibleBot_inflexibleCoe] at h'
      exact h'.2.elim hN
    case inflexibleCoe r h hr hS =>
      cases Subsingleton.elim hN h
      exact ⟨r, hr, hS, rfl⟩
    case inflexibleBot h =>
      cases inflexibleBot_inflexibleCoe h hN
  · rintro ⟨r, hr, hS, rfl⟩
    exact SpecifiesC.inflexibleCoe A N hN r hr hS

theorem specifiesC_inflexibleBot_right_iff (σc : SpecComponent β)
    (A : ExtendedIndex β) (N : NearLitter) (hN : InflexibleBot A N.1) :
    SpecifiesC σ S lS σc ⟨A, inr N⟩ ↔
      σc = SpecComponent.inflexibleBot A hN.path
        {i | ∃ hi : i < S.max, S.f i hi = ⟨hN.path.B.cons (bot_lt_coe _), inl hN.a⟩} := by
  constructor
  · intro h
    cases h
    case flexible h' =>
      rw [flexible_iff_not_inflexibleBot_inflexibleCoe] at h'
      exact h'.1.elim hN
    case inflexibleCoe _ h _ _ =>
      cases inflexibleBot_inflexibleCoe hN h
    case inflexibleBot h =>
      cases Subsingleton.elim hN h
      rfl
  · rintro ⟨r, hr, hS, rfl⟩
    exact SpecifiesC.inflexibleBot A N hN

end ConNF
