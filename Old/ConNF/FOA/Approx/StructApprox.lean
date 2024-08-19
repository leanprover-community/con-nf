import ConNF.FOA.Approx.BaseApprox

/-!
# Structural approximations

In this file, we define structural approximations, which are trees of base approximations.

## Main declarations

* `ConNF.StructApprox`: A tree of base approximations.
-/

open Quiver Set Sum

open scoped Cardinal Pointwise

universe u

namespace ConNF

variable [Params.{u}]

/-- A *`β`-structural approximation* is a tree of base approximations. -/
abbrev StructApprox :=
  Tree BaseApprox

namespace StructApprox

/-! The notions of approximation and exact approximation are defined "branchwise". -/

def Approximates {β : TypeIndex} (π₀ : StructApprox β) (π : StructPerm β) : Prop :=
  ∀ A, (π₀ A).Approximates (π A)

def ExactlyApproximates {β : TypeIndex} (π₀ : StructApprox β) (π : StructPerm β) : Prop :=
  ∀ A, (π₀ A).ExactlyApproximates (π A)

variable [Level] [BasePositions] [FOAAssumptions]

/-- A structural approximation is said to be *free* if its derivative along any path `A` is
`A`-free. -/
def Free {β : Λ} (π₀ : StructApprox β) : Prop :=
  ∀ A, (π₀ A).Free A

theorem Approximates.comp {β γ : TypeIndex} {π₀ : StructApprox β} {π : StructPerm β}
    (h : π₀.Approximates π) (A : Path β γ) :
    StructApprox.Approximates (π₀.comp A) (Tree.comp A π) :=
  fun B => h (A.comp B)

theorem ExactlyApproximates.comp {β γ : TypeIndex} {π₀ : StructApprox β} {π : StructPerm β}
    (h : π₀.ExactlyApproximates π) (A : Path β γ) :
    StructApprox.ExactlyApproximates (π₀.comp A) (Tree.comp A π) :=
  fun B => h (A.comp B)

end StructApprox

end ConNF
