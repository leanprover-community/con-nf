import ConNF.Fuzz.Hypotheses

open Function Set WithBot

open scoped Pointwise

universe u

namespace ConNF

variable [Params.{u}]

variable (α : Λ)

/-- The core tangle data below phase `α`. -/
class TangleDataIio (α : Λ) where
  data : ∀ β : Iio α, TangleData β

section TangleDataIio

variable [TangleDataIio α]

noncomputable instance TangleDataIio.toTangleData : ∀ β : IioBot α, TangleData β
  | ⟨⊥, _⟩ => Bot.corePositionedTypedObjects
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

/-- The positioned tangle data below phase `α`. -/
class PositionFunctionIio (α : Λ) [TangleDataIio α] where
  data : ∀ β : Iio α, PositionFunction β

section PositionFunctionIio

variable [TangleDataIio α] [PositionFunctionIio α]

noncomputable instance PositionFunctionIio.toPositionFunction :
    ∀ β : IioBot α, PositionFunction β
  | ⟨⊥, _⟩ => Bot.positionedPositionedTypedObjects
  | ⟨(β : Λ), hβ⟩ => PositionFunctionIio.data ⟨β, coe_lt_coe.1 hβ⟩

noncomputable instance PositionFunctionIio.toPositionFunction' (β : Iio α) :
    PositionFunction β :=
  show PositionFunction (iioCoe β) by infer_instance

end PositionFunctionIio

/-- The almost tangle data below phase `α`. -/
abbrev TypedObjectsIio (α : Λ) [TangleDataIio α] :=
  ∀ β : Iio α, TypedObjects β

end ConNF
