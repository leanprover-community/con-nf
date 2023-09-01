import ConNF.Fuzz.Hypotheses

/-!
# Hypotheses for constructing tangles

In this file we state the conditions required to generate the `fuzz` maps at all levels below a
given proper type index `α : Λ`. Using these inductive hypotheses we can build the types of tangles
and allowable permutations at level `α`. However, with such weak hypotheses (in particular, the lack
of any coherence between type levels) we cannot prove many facts about these new types.

## Main declarations

* `ConNF.TangleDataIio`: The `TangleData` for each `β < α`.
* `ConNF.PositionedTanglesIio`: The `PositionedTangles` for each `β < α`.
* `ConNF.TypedObjectsIio`: The `TypedObjects` for each `β < α`.
-/

open Function Set WithBot

open scoped Pointwise

universe u

namespace ConNF

variable [Params.{u}]

variable (α : Λ)

/-- The `TangleData` for each `β < α`. -/
class TangleDataIio (α : Λ) where
  data : ∀ β : Iio α, TangleData β

section TangleDataIio

variable [TangleDataIio α]

noncomputable instance TangleDataIio.toTangleData : ∀ β : IioBot α, TangleData β
  | ⟨⊥, _⟩ => Bot.tangleData
  | ⟨(β : Λ), hβ⟩ => TangleDataIio.data ⟨β, coe_lt_coe.1 hβ⟩

noncomputable instance TangleDataIio.toTangleData' (β : Iio α) : TangleData β :=
  show TangleData (iioCoe β) by infer_instance

noncomputable instance TangleDataIio.toTangleData'' (β : TypeIndex) (hβ : β < α) :
    TangleData (show IioBot α from ⟨β, hβ⟩) :=
  TangleDataIio.toTangleData α ⟨β, hβ⟩

noncomputable instance TangleDataIio.toTangleData''' (β : Λ) (hβ : (β : TypeIndex) < α) :
    TangleData (show IioBot α from ⟨β, hβ⟩) :=
  TangleDataIio.toTangleData α ⟨β, hβ⟩

end TangleDataIio

/-- The `PositionedTangles` for each `β < α`. -/
class PositionedTanglesIio (α : Λ) [TangleDataIio α] where
  data : ∀ β : Iio α, PositionedTangles β

section PositionedTanglesIio

variable [TangleDataIio α] [PositionedTanglesIio α]

noncomputable instance PositionedTanglesIio.toPositionedTangles :
    ∀ β : IioBot α, PositionedTangles β
  | ⟨⊥, _⟩ => Bot.positionedTangles
  | ⟨(β : Λ), hβ⟩ => PositionedTanglesIio.data ⟨β, coe_lt_coe.1 hβ⟩

noncomputable instance PositionedTanglesIio.toPositionedTangles' (β : Iio α) :
    PositionedTangles β :=
  show PositionedTangles (iioCoe β) by infer_instance

end PositionedTanglesIio

/-- The `TypedObjects` for each `β < α`. -/
abbrev TypedObjectsIio (α : Λ) [TangleDataIio α] :=
  ∀ β : Iio α, TypedObjects β

end ConNF
