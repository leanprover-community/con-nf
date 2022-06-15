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

/-- If `β < γ`, we have a path directly between the two types in the opposite order.
Note that the `⟶` symbol (long right arrow) is not the normal `→` (right arrow),
even though monospace fonts often display them similarly. -/
instance coe_lt_to_hom (β γ : Λ) : has_lift_t (β < γ) ((γ : type_index) ⟶ β) :=
⟨λ h, by { unfold quiver.hom, simp, exact h }⟩

/-- The direct path from the base type to `α`. -/
def index_path.direct (α : Λ) : index_path α :=
quiver.hom.to_path $ with_bot.bot_lt_coe α

/-- A proper type index, together with a path from the base type.
This plays the role of an extended type index in the paper. -/
def extended_index := Σ (α : Λ), index_path α

namespace extended_index

/-- The smallest type in this extended type index, excluding the base type. -/
def min : extended_index → Λ
| ⟨α, @quiver.path.cons V _ a b c path₁ path₂⟩ := begin
  cases b,
  { exfalso, unfold quiver.hom at path₂, simp at path₂, exact path₂ },
  { exact b }
end

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

lemma drop_min_length_lt_length (A : extended_index) :
∀ A' ∈ A.drop_min, (A' : extended_index).snd.length < A.snd.length :=
begin
  intros A' hA',
  simp at hA',
  sorry
end

example (α β γ : Λ) (hαβ : α < β) (hβγ : β < γ) :
drop_min ⟨γ, quiver.path.cons (quiver.path.cons (quiver.hom.to_path (↑hβγ)) (↑hαβ : (β : type_index) ⟶ α)) (with_bot.bot_lt_coe α)⟩ =
some ⟨γ, quiver.path.cons (quiver.hom.to_path (↑hβγ)) (with_bot.bot_lt_coe β)⟩ := rfl

def lt : extended_index → extended_index → Prop
| A := λ B, A.min < B.min ∨ A.min = B.min ∧
  ∃ A' ∈ A.drop_min, ∀ B' ∈ B.drop_min,
    have (A' : extended_index).snd.length < A.snd.length :=
      drop_min_length_lt_length A A' (by assumption),
    lt A' B'
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ A, A.snd.length)⟩]}

instance : has_lt extended_index := ⟨lt⟩
instance extended_index.is_well_order : is_well_order extended_index (<) := sorry
instance : has_well_founded extended_index := ⟨_, extended_index.is_well_order.wf⟩
instance : has_le extended_index := ⟨λ A B, A < B ∨ A = B⟩

end extended_index

end con_nf
