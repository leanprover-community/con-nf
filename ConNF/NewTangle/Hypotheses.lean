import ConNF.Fuzz.Hypotheses

/-!
# Hypotheses for constructing tangles

In this file we state the conditions required to generate the `fuzz` maps at all levels below a
given proper type index `α : Λ`. Using these inductive hypotheses we can build the types of tangles
and allowable permutations at level `α`. However, with such weak hypotheses (in particular, the lack
of any coherence between type levels) we cannot prove many facts about these new types.

## Main declarations

* `ConNF.TangleDataLt`: The `TangleData` for each `β < α`.
* `ConNF.PositionedTanglesLt`: The `PositionedTangles` for each `β < α`.
* `ConNF.TypedObjectsLt`: The `TypedObjects` for each `β < α`.
-/

open Function WithBot

open scoped Pointwise

universe u

namespace ConNF

variable [Params.{u}]

variable (α : Λ)

/-- The `TangleData` for each `β < α`. -/
class TangleDataLt (α : Λ) where
  data : ∀ β : Λ, [IsLt β α] → TangleData β

noncomputable instance TangleDataLt.toTangleData [TangleDataLt α] :
    ∀ β : TypeIndex, [IsLt β α] → TangleData β
  | ⊥, _ => Bot.tangleData
  | (β : Λ), _ => TangleDataLt.data α β

/-- The `PositionedTangles` for each `β < α`. -/
class PositionedTanglesLt (α : Λ) [TangleDataLt α] where
  data : ∀ β : Λ, [IsLt β α] → PositionedTangles β

noncomputable instance PositionedTanglesLt.toPositionedTangles
    [TangleDataLt α] [PositionedTanglesLt α] : ∀ β : TypeIndex, [IsLt β α] → PositionedTangles β
  | ⊥, _ => Bot.positionedTangles
  | (β : Λ), _ => PositionedTanglesLt.data β

/-- The `TypedObjects` for each `β < α`. -/
abbrev TypedObjectsLt (α : Λ) [TangleDataLt α] :=
  ∀ β : Λ, [IsLt β α] → TypedObjects β

end ConNF
