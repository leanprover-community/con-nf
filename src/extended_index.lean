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
types in the hierarchy until we reach the base type.
This plays the role of an extended type index in the paper. -/
def extended_index (α : Λ) := quiver.path (α : type_index) ⊥

/-- If `β < γ`, we have a path directly between the two types in the opposite order.
Note that the `⟶` symbol (long right arrow) is not the normal `→` (right arrow),
even though monospace fonts often display them similarly. -/
instance coe_lt_to_hom (β γ : Λ) : has_lift_t (β < γ) ((γ : type_index) ⟶ β) :=
⟨λ h, by { unfold quiver.hom, simp, exact h }⟩

/-- The direct path from the base type to `α`. -/
def extended_index.direct (α : Λ) : extended_index α :=
quiver.hom.to_path $ with_bot.bot_lt_coe α

namespace extended_index

variable {α : Λ}

/-- The smallest type in this extended type index, excluding the base type. -/
def min : extended_index α → Λ
| (@quiver.path.cons V _ a (some b) c path₁ path₂) := b
| (@quiver.path.cons V _ a none c path₁ path₂) := begin
  exfalso, unfold quiver.hom at path₂, simp at path₂, exact path₂
end

/-- Merge the two lowest arrows on the path.
Suppose the path were `γ → β → α → ⊥`.
This function then returns `γ → β → ⊥`.
If the path contained only one arrow, return `none`. -/
def drop_min : extended_index α → option (extended_index α)
| (quiver.path.cons (quiver.path.cons b f) g) := some (quiver.path.cons b begin
  unfold quiver.hom at f g ⊢,
  transitivity, exact f, exact g
end)
| (quiver.path.cons quiver.path.nil _) := none

lemma drop_min_length_succ_eq_length (A : extended_index α) :
∀ A' ∈ A.drop_min, (A' : extended_index α).length + 1 = A.length :=
begin
  intros A' hA',
  simp at hA',
  cases A with i _ path₁ hom₁,
  cases path₁ with j _ path₂ hom₂,
  { exfalso, unfold drop_min at hA', simp at hA', exact hA' },
  { unfold drop_min at hA', simp at hA' ⊢, rw ← hA', simp }
end

lemma drop_min_length_lt_length (A : extended_index α) :
∀ A' ∈ A.drop_min, (A' : extended_index α).length < A.length :=
begin
  intros A' hA',
  have := drop_min_length_succ_eq_length A A' hA',
  rw ← this, simp
end

example (α β γ : Λ) (hαβ : α < β) (hβγ : β < γ) :
drop_min (quiver.path.cons (quiver.path.cons (quiver.hom.to_path (↑hβγ)) (↑hαβ : (β : type_index) ⟶ α)) (with_bot.bot_lt_coe α) : extended_index γ) =
some (quiver.path.cons (quiver.hom.to_path (↑hβγ)) (with_bot.bot_lt_coe β) : extended_index γ) := rfl

def lt : extended_index α → extended_index α → Prop
| A := λ B, A.min < B.min ∨ A.min = B.min ∧
  ∃ A' ∈ A.drop_min, ∀ B' ∈ B.drop_min,
    have (A' : extended_index α).length < A.length :=
      drop_min_length_lt_length A A' (by assumption),
    lt A' B'
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ A, A.length)⟩]}

-- TODO: Do we want all extended indices to be well-ordered, or just all extended indices of a given α?
instance : has_lt (extended_index α) := ⟨lt⟩
instance extended_index.is_well_order : is_well_order (extended_index α) (<) := sorry
instance : has_well_founded (extended_index α) := ⟨_, extended_index.is_well_order.wf⟩
instance : has_le (extended_index α) := ⟨λ A B, A < B ∨ A = B⟩

end extended_index

end con_nf
