import ConNF.Foa.Basic.Constrains

open Quiver Set Sum

open scoped Cardinal Pointwise

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α]

/-!
# Induction on support conditions
-/

/-- The inductive hypothesis used to construct the induced action of an approximation in the
freedom of action theorem. -/
structure HypAction {β : Iic α} (c : SupportCondition β) where
  atomImage : ∀ A a, ⟨A, inl a⟩ <[α] c → Atom
  nearLitterImage : ∀ A N, ⟨A, inr N⟩ <[α] c → NearLitter

namespace HypAction

variable {β : Iic α}

instance : WellFoundedRelation (SupportCondition β) :=
  ⟨_, WellFounded.transGen <| constrains_wf α β⟩

mutual
  /-- Construct the fixed-point functions `fix_atom` and `fix_near_litter`.
  This is used to compute the induced action of an approximation on all atoms and near-litters. -/
  noncomputable def fixAtom (Fa : ∀ (A : ExtendedIndex β) (a), HypAction ⟨A, inl a⟩ → Atom)
      (FN : ∀ (A : ExtendedIndex β) (N), HypAction ⟨A, inr N⟩ → NearLitter) :
      ExtendedIndex β → Atom → Atom
    | A, a => Fa A a ⟨fun B b _ => fixAtom Fa FN B b, fun B N _ => fixNearLitter Fa FN B N⟩
  /-- Construct the fixed-point functions `fix_atom` and `fix_near_litter`.
  This is used to compute the induced action of an approximation on all atoms and near-litters. -/
  noncomputable def fixNearLitter (Fa : ∀ (A : ExtendedIndex β) (a), HypAction ⟨A, inl a⟩ → Atom)
      (FN : ∀ (A : ExtendedIndex β) (N), HypAction ⟨A, inr N⟩ → NearLitter) :
      ExtendedIndex β → NearLitter → NearLitter
    | A, N => FN A N ⟨fun B b _ => fixAtom Fa FN B b, fun B N _ => fixNearLitter Fa FN B N⟩
end
termination_by
  fixAtom A n => SupportCondition.mk A (inl n)
  fixNearLitter A N => SupportCondition.mk A (inr N)

theorem fixAtom_eq (Fa FN) (A : ExtendedIndex β) (a : Atom) :
    fixAtom Fa FN A a =
      Fa A a ⟨fun B b _ => fixAtom Fa FN B b, fun B N _ => fixNearLitter Fa FN B N⟩ :=
  by rw [fixAtom]

theorem fixNearLitter_eq (Fa FN) (A : ExtendedIndex β) (N : NearLitter) :
    fixNearLitter Fa FN A N =
      FN A N ⟨fun B b _ => fixAtom Fa FN B b, fun B N _ => fixNearLitter Fa FN B N⟩ :=
  by rw [fixNearLitter]

end HypAction

end ConNF
