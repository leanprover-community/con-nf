import Mathlib.Combinatorics.Quiver.Path
import ConNF.BaseType.Params

/-!
# Indices

In this file, we create instances for various facts about comparisons between type indices,
and also define extended type indices.

## Main declarations

* `ConNF.ExtendedIndex`: The type of extended type indices from a given base type index.
-/

open Cardinal Function Quiver Quiver.Path Set WithBot

open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}]

/-- The current level of the structure we are building. -/
class Level where
  (α : Λ)

export Level (α)

variable [Level]

/-- The type index `β` is less than our current level. -/
class LtLevel (β : TypeIndex) : Prop where
  elim : β < α

instance {β : Λ} [inst : LtLevel (Option.some β)] : LtLevel β := inst

instance : LtLevel ⊥ where
  elim := bot_lt_coe α

class LeLevel (β : TypeIndex) : Prop where
  elim : β ≤ α

instance {β : TypeIndex} [LtLevel β] : LeLevel β where
  elim := LtLevel.elim.le

instance {β : Λ} [inst : LeLevel (Option.some β)] : LeLevel β := inst

variable {α : TypeIndex}

/-- We define the type of paths from certain types to lower types as elements of this quiver. -/
instance : Quiver TypeIndex :=
  ⟨(· > ·)⟩

/-- A (finite) path from the type `α` to the base type.
This is a way that we can perceive extensionality, iteratively descending to lower
types in the hierarchy until we reach the base type.
As `Λ` is well-ordered, there are no infinite descending paths. -/
def ExtendedIndex (α : TypeIndex) :=
  Quiver.Path α ⊥

/-- If there is a path between `α` and `β`, we must have `β ≤ α`.
The case `β = α` can occur with the nil path. -/
theorem le_of_path : ∀ {β : TypeIndex}, Path α β → β ≤ α
  | _, nil => le_rfl
  | _, cons p f => (le_of_lt f).trans <| le_of_path p

theorem path_eq_nil : ∀ p : Path α α, p = nil
  | nil => rfl
  | cons p f => ((le_of_path p).not_lt f).elim

theorem ExtendedIndex.length_ne_zero {α : Λ} (A : ExtendedIndex α) : A.length ≠ 0 := by
  intro h
  cases Quiver.Path.eq_of_length_zero A h

/-- There are at most `Λ` `α`-extended type indices. -/
@[simp]
theorem mk_extendedIndex (α : TypeIndex) : #(ExtendedIndex α) ≤ #Λ := by
  refine le_trans ((Cardinal.le_def _ _).2 ⟨⟨toList, toList_injective (α : TypeIndex) ⊥⟩⟩) ?_
  convert mk_list_le_max _ using 1
  simp only [mk_typeIndex, max_eq_right, aleph0_le_mk]

/-- If `β < γ`, we have a path directly between the two types in the opposite order.
Note that the `⟶` symbol (long right arrow) is not the normal `→` (right arrow),
even though monospace fonts often display them similarly. -/
instance ltToHom (β γ : Λ) : Coe (β < γ) ((γ : TypeIndex) ⟶ β) :=
  ⟨coe_lt_coe.2⟩

instance : (α : TypeIndex) → Inhabited (ExtendedIndex α)
  | ⊥ => ⟨nil⟩
  | (α : Λ) => ⟨Hom.toPath <| WithBot.bot_lt_coe α⟩

/-- There exists an `α`-extended type index. --/
theorem mk_extendedIndex_ne_zero (α : TypeIndex) : #(ExtendedIndex α) ≠ 0 :=
  Cardinal.mk_ne_zero _

end ConNF
