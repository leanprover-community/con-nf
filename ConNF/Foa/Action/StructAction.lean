import ConNF.Foa.Basic.Flexible
import ConNF.Foa.Approximation.StructApprox
import ConNF.Foa.Action.NearLitterAction

open Cardinal Quiver Set Sum WithBot

open scoped Cardinal Classical Pointwise

universe u

namespace ConNF

variable [Params.{u}]

/-!
# Tree actions
-/

/-- A `β`-structural action is a product that assigns a near-litter action to each `β`-extended
index. -/
abbrev StructAction :=
  Tree NearLitterAction

namespace StructAction

def Lawful {β : TypeIndex} (φ : StructAction β) : Prop :=
  ∀ B, (φ B).Lawful

/-- This structural action maps flexible litters to flexible litters. -/
def MapFlexible {α : Λ} [BasePositions] [Phase2Assumptions α] {β : Iio α} (φ : StructAction β) :
    Prop :=
  ∀ (L : Litter) (B hL), Flexible α L B → Flexible α (((φ B).litterMap L).get hL).1 B

section Precise

def Precise {β : TypeIndex} (φ : StructAction β) : Prop :=
  ∀ B, (φ B).Precise

variable {α : Λ} [BasePositions] [Phase2Assumptions α] {β : Iio α} (φ : StructAction β)

noncomputable def complete (hφ : φ.Lawful) : StructApprox β := fun B => (φ B).complete (hφ B) B

theorem complete_apply (hφ : φ.Lawful) (B : ExtendedIndex β) :
    φ.complete hφ B = (φ B).complete (hφ B) B :=
  rfl

theorem smul_atom_eq {hφ : φ.Lawful} {π : StructPerm β} (hπ : (φ.complete hφ).ExactlyApproximates π)
    {a : Atom} {B : ExtendedIndex β} (ha : ((φ B).atomMap a).Dom) :
    Tree.comp B π • a = ((φ B).atomMap a).get ha := by
  have := (φ B).smul_atom_eq (hπ B) ha
  rw [Tree.ofBot_smul] at this
  exact this

theorem smul_toNearLitter_eq_of_precise {hφ : φ.Lawful} (hφp : φ.Precise) {π : StructPerm β}
    (hπ : (φ.complete hφ).ExactlyApproximates π) {L : Litter} {B : ExtendedIndex β}
    (hL : ((φ B).litterMap L).Dom)
    (hπL : Tree.comp B π • L = (((φ B).litterMap L).get hL).1) :
    Tree.comp B π • L.toNearLitter = ((φ B).litterMap L).get hL := by
  have := (φ B).smul_toNearLitter_eq_of_preciseAt (hπ B) hL (hφp B hL) ?_
  · rw [Tree.ofBot_smul] at this
    exact this
  · rw [Tree.ofBot_smul]
    exact hπL

theorem smul_nearLitter_eq_of_precise {hφ : φ.Lawful} (hφp : φ.Precise) {π : StructPerm β}
    (hπ : (φ.complete hφ).ExactlyApproximates π) {N : NearLitter} {B : ExtendedIndex β}
    (hN : ((φ B).litterMap N.1).Dom)
    (hπL : Tree.comp B π • N.1 = (((φ B).litterMap N.1).get hN).1) :
    ((Tree.comp B π • N : NearLitter) : Set Atom) =
      (((φ B).litterMap N.1).get hN : Set Atom) ∆
        (Tree.comp B π • litterSet N.1 ∆ N) := by
  have := (φ B).smul_nearLitter_eq_of_preciseAt (hπ B) hN (hφp B hN) ?_
  · rw [Tree.ofBot_smul] at this
    exact this
  · rw [Tree.ofBot_smul]
    exact hπL

end Precise

variable {α : Λ} [BasePositions] [Phase2Assumptions α] {β : Iio α}

instance {β : TypeIndex} : PartialOrder (StructAction β)
    where
  le φ ψ := ∀ B, φ B ≤ ψ B
  le_refl φ B := le_rfl
  le_trans φ ψ χ h₁ h₂ B := (h₁ B).trans (h₂ B)
  le_antisymm φ ψ h₁ h₂ := funext fun B => le_antisymm (h₁ B) (h₂ B)

theorem Lawful.le {β : TypeIndex} {φ ψ : StructAction β} (h : φ.Lawful) (hψ : ψ ≤ φ) : ψ.Lawful :=
  fun B => (h B).le (hψ B)

theorem le_comp {β γ : TypeIndex} {φ ψ : StructAction β} (h : φ ≤ ψ) (A : Path β γ) :
    φ.comp A ≤ ψ.comp A := fun B => h (A.comp B)

theorem Lawful.comp {β γ : TypeIndex} {φ : StructAction β} (h : φ.Lawful) (A : Path β γ) :
    Lawful (φ.comp A) := fun B =>
  { atomMap_injective := (h (A.comp B)).atomMap_injective
    litterMap_injective := (h (A.comp B)).litterMap_injective
    atom_mem := (h (A.comp B)).atom_mem }

end StructAction

end ConNF
