import ConNF.Foa.Approximation.NearLitterApprox

open Quiver Set Sum

open scoped Cardinal Pointwise

universe u

namespace ConNF

variable [Params.{u}]

/-!
# Structural approximations
-/

/-- A `β`-structural approximation is a product that assigns a near-litter approximation to each
`β`-extended index. -/
abbrev StructApprox :=
  Tree NearLitterApprox

namespace StructApprox

def Approximates {β : TypeIndex} (π₀ : StructApprox β) (π : StructPerm β) : Prop :=
  ∀ A, (π₀ A).Approximates (π A)

def ExactlyApproximates {β : TypeIndex} (π₀ : StructApprox β) (π : StructPerm β) : Prop :=
  ∀ A, (π₀ A).ExactlyApproximates (π A)

variable {α : Λ} [BasePositions] [FoaAssumptions α]

def Free {β : Iic α} (π₀ : StructApprox β) : Prop :=
  ∀ A, (π₀ A).Free α A

theorem Approximates.comp {β γ : TypeIndex} {π₀ : StructApprox β} {π : StructPerm β}
    (h : π₀.Approximates π) (A : Path β γ) :
    StructApprox.Approximates (π₀.comp A) (Tree.comp A π) :=
  fun B => h (A.comp B)

theorem ExactlyApproximates.comp {β γ : TypeIndex} {π₀ : StructApprox β} {π : StructPerm β}
    (h : π₀.ExactlyApproximates π) (A : Path β γ) :
    StructApprox.ExactlyApproximates (π₀.comp A) (Tree.comp A π) :=
  fun B => h (A.comp B)

/-!
# Induction on support conditions
-/


/-- The inductive hypothesis used to construct the induced action of an approximation in the
freedom of action theorem. -/
structure Hypothesis {β : Iic α} (c : SupportCondition β) where
  atomImage : ∀ A a, ⟨A, inl a⟩ <[α] c → Atom
  nearLitterImage : ∀ A N, ⟨A, inr N⟩ <[α] c → NearLitter

namespace Hypothesis

variable {β : Iic α}

def fixMap :
    PSum (Σ' _ : ExtendedIndex β, Atom) (Σ' _ : ExtendedIndex β, NearLitter) → SupportCondition β
  | PSum.inl ⟨A, a⟩ => ⟨A, inl a⟩
  | PSum.inr ⟨A, N⟩ => ⟨A, inr N⟩

def fixWf :
    WellFoundedRelation
      (PSum (Σ' _ : ExtendedIndex β, Atom) (Σ' _ : ExtendedIndex β, NearLitter)) :=
  ⟨InvImage (Relation.TransGen (Constrains α β)) fixMap,
    InvImage.wf _ (WellFounded.transGen <| constrains_wf α β)⟩

mutual
  /-- Construct the fixed-point functions `fix_atom` and `fix_near_litter`.
  This is used to compute the induced action of an approximation on all atoms and near-litters. -/
  noncomputable def fixAtom (Fa : ∀ (A : ExtendedIndex β) (a), Hypothesis ⟨A, inl a⟩ → Atom)
      (FN : ∀ (A : ExtendedIndex β) (N), Hypothesis ⟨A, inr N⟩ → NearLitter) :
      ExtendedIndex β → Atom → Atom
    | A, a => Fa A a ⟨fun B b _ => fixAtom Fa FN B b, fun B N _ => fixNearLitter Fa FN B N⟩
  /-- Construct the fixed-point functions `fix_atom` and `fix_near_litter`.
  This is used to compute the induced action of an approximation on all atoms and near-litters. -/
  noncomputable def fixNearLitter (Fa : ∀ (A : ExtendedIndex β) (a), Hypothesis ⟨A, inl a⟩ → Atom)
      (FN : ∀ (A : ExtendedIndex β) (N), Hypothesis ⟨A, inr N⟩ → NearLitter) :
      ExtendedIndex β → NearLitter → NearLitter
    | A, N => FN A N ⟨fun B b _ => fixAtom Fa FN B b, fun B N _ => fixNearLitter Fa FN B N⟩
end
termination_by' fixWf

theorem fixAtom_eq (Fa FN) (A : ExtendedIndex β) (a : Atom) :
    fixAtom Fa FN A a =
      Fa A a ⟨fun B b _ => fixAtom Fa FN B b, fun B N _ => fixNearLitter Fa FN B N⟩ :=
  by rw [fixAtom]

theorem fixNearLitter_eq (Fa FN) (A : ExtendedIndex β) (N : NearLitter) :
    fixNearLitter Fa FN A N =
      FN A N ⟨fun B b _ => fixAtom Fa FN B b, fun B N _ => fixNearLitter Fa FN B N⟩ :=
  by rw [fixNearLitter]

end Hypothesis

end StructApprox

end ConNF
