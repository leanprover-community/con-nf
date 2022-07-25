import mathlib.quiver
import phase0.params

open cardinal quiver
open_locale cardinal

universe u

namespace con_nf
variables [params.{u}]

/-- We define the type of paths from certain types to lower types as elements of this quiver. -/
instance quiver : quiver type_index := ⟨(>)⟩

/-- A (finite) path from the type α to the base type.
This can be seen as a way that we can perceive extensionality, iteratively descending to lower
types in the hierarchy until we reach the base type.
This plays the role of an extended type index in the paper. -/
def extended_index (α : type_index) := quiver.path α ⊥

/-- If there is a path between `α` and `β`, we must have `β ≤ α`.
The case `β = α` can occur with the nil path. -/
lemma le_of_path {α : type_index} : Π {β : type_index}, path α β → β ≤ α
| β (path.cons A B) := le_trans (le_of_lt B) $ le_of_path A
| β path.nil := le_rfl

lemma path_nil {α : type_index} (A : path α α) : A = path.nil :=
begin
  obtain - | ⟨β, _, B, hβ⟩ := A, refl,
  exfalso, exact not_lt_of_le (le_of_path B) hβ,
end

/-- There are at most `Λ` `α`-extended type indices. -/
@[simp] lemma mk_extended_index (α : type_index) : #(extended_index α) ≤ #Λ :=
begin
  refine le_trans ((cardinal.le_def _ _).mpr ⟨path.to_list_embedding (α : type_index) ⊥⟩) _,
  convert mk_list_le_max _ using 1, simp, rw max_eq_right Λ_limit.aleph_0_le
end

/-- If `β < γ`, we have a path directly between the two types in the opposite order.
Note that the `⟶` symbol (long right arrow) is not the normal `→` (right arrow),
even though monospace fonts often display them similarly. -/
instance coe_lt_to_hom (β γ : Λ) : has_lift_t (β < γ) ((γ : type_index) ⟶ β) :=
⟨λ h, by { unfold hom, simp, exact h }⟩

/-- The direct path from the base type to `α`. -/
def extended_index.direct (α : Λ) : extended_index α := quiver.hom.to_path $ with_bot.bot_lt_coe α

instance extended_index_inhabited_coe (α : Λ) : inhabited (extended_index α) :=
⟨extended_index.direct α⟩

instance extended_index_inhabited_bot : inhabited (extended_index ⊥) :=
⟨path.nil⟩

instance extended_index_inhabited (α : type_index) : inhabited (extended_index α) :=
⟨with_bot.rec_bot_coe path.nil extended_index.direct α⟩

/-- There exists an `α`-extended type index. --/
lemma mk_extended_index_ne_zero (α : type_index) : #(extended_index α) ≠ 0 := cardinal.mk_ne_zero _

/-- For our purposes, we let any monoid act trivially on extended type indices. -/
instance {α : Type*} [monoid α] {β : type_index} : mul_action α (extended_index β) :=
{ smul := λ _, id, one_smul := λ _, rfl, mul_smul := λ _ _ _, rfl }

end con_nf
