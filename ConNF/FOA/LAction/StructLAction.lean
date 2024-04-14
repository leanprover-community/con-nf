import ConNF.FOA.Basic.Flexible
import ConNF.FOA.Approx.StructApprox
import ConNF.FOA.LAction.Complete

open Cardinal Quiver Set Sum WithBot

open scoped Cardinal Classical Pointwise symmDiff

universe u

namespace ConNF

variable [Params.{u}]

/-!
# Structural actions
-/

/-- A `β`-structural action is a product that assigns a base litter action to each `β`-extended
index. -/
abbrev StructLAction :=
  Tree BaseLAction

namespace StructLAction

def Lawful {β : TypeIndex} (φ : StructLAction β) : Prop :=
  ∀ B, (φ B).Lawful

def Approximates (ψ : StructLAction β) (π : StructPerm β) : Prop :=
  ∀ A, (ψ A).Approximates (π A)

/-- This structural action maps flexible litters to flexible litters. -/
def MapFlexible [Level] [BasePositions] [FOAAssumptions] {β : Λ} (φ : StructLAction β) :
    Prop :=
  ∀ (B) (L : Litter) (hL), Flexible B L → Flexible B (((φ B).litterMap L).get hL).1

section Precise

def Precise {β : TypeIndex} (φ : StructLAction β) : Prop :=
  ∀ B, (φ B).Precise

variable [Level] [BasePositions] [FOAAssumptions] {β : Λ} (φ : StructLAction β)

noncomputable def complete (hφ : φ.Lawful) : StructApprox β := fun B => (φ B).complete (hφ B) B

theorem complete_apply (hφ : φ.Lawful) (B : ExtendedIndex β) :
    φ.complete hφ B = (φ B).complete (hφ B) B :=
  rfl

theorem smul_atom_eq {hφ : φ.Lawful} {π : StructPerm β} (hπ : (φ.complete hφ).ExactlyApproximates π)
    {a : Atom} {B : ExtendedIndex β} (ha : ((φ B).atomMap a).Dom) :
    π B • a = ((φ B).atomMap a).get ha :=
  (φ B).smul_atom_eq (hπ B) ha

theorem smul_toNearLitter_eq_of_precise {hφ : φ.Lawful} (hφp : φ.Precise) {π : StructPerm β}
    (hπ : (φ.complete hφ).ExactlyApproximates π) {L : Litter} {B : ExtendedIndex β}
    (hL : ((φ B).litterMap L).Dom)
    (hπL : π B • L = (((φ B).litterMap L).get hL).1) :
    π B • L.toNearLitter = ((φ B).litterMap L).get hL :=
  (φ B).smul_toNearLitter_eq_of_preciseAt (hπ B) hL (hφp B hL) hπL

theorem smul_nearLitter_eq_of_precise {hφ : φ.Lawful} (hφp : φ.Precise) {π : StructPerm β}
    (hπ : (φ.complete hφ).ExactlyApproximates π) {N : NearLitter} {B : ExtendedIndex β}
    (hN : ((φ B).litterMap N.1).Dom)
    (hπL : π B • N.1 = (((φ B).litterMap N.1).get hN).1) :
    ((π B • N : NearLitter) : Set Atom) =
      (((φ B).litterMap N.1).get hN : Set Atom) ∆
        (Tree.comp B π • litterSet N.1 ∆ N) :=
  (φ B).smul_nearLitter_eq_of_preciseAt (hπ B) hN (hφp B hN) hπL

end Precise

variable [Level] [BasePositions] [FOAAssumptions] {β : Λ}

instance {β : TypeIndex} : PartialOrder (StructLAction β)
    where
  le φ ψ := ∀ B, φ B ≤ ψ B
  le_refl φ B := le_rfl
  le_trans φ ψ χ h₁ h₂ B := (h₁ B).trans (h₂ B)
  le_antisymm φ ψ h₁ h₂ := funext fun B => le_antisymm (h₁ B) (h₂ B)

theorem Lawful.le {β : TypeIndex} {φ ψ : StructLAction β} (h : φ.Lawful) (hψ : ψ ≤ φ) : ψ.Lawful :=
  fun B => (h B).le (hψ B)

theorem le_comp {β γ : TypeIndex} {φ ψ : StructLAction β} (h : φ ≤ ψ) (A : Path β γ) :
    φ.comp A ≤ ψ.comp A := fun B => h (A.comp B)

theorem Lawful.comp {β γ : TypeIndex} {φ : StructLAction β} (h : φ.Lawful) (A : Path β γ) :
    Lawful (φ.comp A) := fun B =>
  { atomMap_injective := (h (A.comp B)).atomMap_injective
    litterMap_injective := (h (A.comp B)).litterMap_injective
    atom_mem := (h (A.comp B)).atom_mem }

end StructLAction

end ConNF
