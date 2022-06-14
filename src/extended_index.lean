import combinatorics.quiver.basic
import combinatorics.quiver.path
import params
import pretangle

universe u

namespace con_nf
variables [params.{u}]

open params

/-- We define the type of paths from certain types to lower types
as elements of this quiver. -/
instance has_paths : quiver type_index := ⟨(>)⟩

/-- A (finite) path from the type α to the base type.
This can be seen as a way that we can perceive extensionality, iteratively descending to lower
types in the hierarchy until we reach the base type. -/
def index_path (α : Λ) := quiver.path (α : type_index) ⊥

/-- If `β < γ`, we have a path directly between the two types in the opposite order. -/
instance coe_lt_to_hom (β γ : Λ) : has_lift_t (β < γ) ((γ : type_index) ⟶ β) :=
⟨λ h, by { unfold quiver.hom, simp, exact h }⟩

/-- The direct path from the base type to `α`. -/
def direct_index_path (α : Λ) : index_path α :=
quiver.hom.to_path $ with_bot.bot_lt_coe α

/-- A proper type index, together with a path from the base type.
This plays the role of an extended type index in the paper. -/
def extended_index := Σ (α : Λ), index_path α

namespace extended_index

/-- Merge the two lowest arrows on the path.
Suppose the path were `γ → β → α → ⊥`.
This function then returns `γ → β → ⊥`.
If the path contained only one arrow, return `none`. -/
def drop_min : extended_index → option extended_index
| ⟨a, quiver.path.cons (quiver.path.cons b f) g⟩ := some ⟨a, quiver.path.cons b begin
  unfold quiver.hom at f g ⊢,
  transitivity, exact f, exact g
end⟩
| ⟨a, quiver.path.cons quiver.path.nil _⟩ := none

example (α β γ : Λ) (hαβ : α < β) (hβγ : β < γ) :
drop_min ⟨γ, quiver.path.cons (quiver.path.cons (quiver.hom.to_path (↑hβγ)) (↑hαβ : (β : type_index) ⟶ α)) (with_bot.bot_lt_coe α)⟩ =
some ⟨γ, quiver.path.cons (quiver.hom.to_path (↑hβγ)) (with_bot.bot_lt_coe β)⟩ := rfl

end extended_index

end con_nf
