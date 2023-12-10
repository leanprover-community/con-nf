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

variable [BasePositions] [Level] [FoaAssumptions]

def Free {β : Iic α} (π₀ : StructApprox β) : Prop :=
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
