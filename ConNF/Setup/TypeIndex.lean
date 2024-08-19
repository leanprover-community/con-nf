import ConNF.Setup.Params

/-!
# Type indices

In this file, we declare the notion of a type index, and prove some of its basic properties.

## Main declarations

* `ConNF.TypeIndex`: The type of type indices.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}]

/-- Either the base type or a proper type index (an inhabitant of `Λ`).
The base type is written `⊥`. -/
@[reducible]
def TypeIndex :=
  WithBot Λ

@[simp]
protected theorem TypeIndex.type :
    type ((· < ·) : TypeIndex → TypeIndex → Prop) = type ((· < ·) : Λ → Λ → Prop) := by
  rw [type_withBot]
  exact one_add_of_omega_le <| omega_le_of_isLimit Λ_type_isLimit

@[simp]
protected theorem TypeIndex.card :
    #TypeIndex = #Λ := by
  have := congr_arg Ordinal.card TypeIndex.type
  rwa [card_type, card_type] at this

end ConNF
