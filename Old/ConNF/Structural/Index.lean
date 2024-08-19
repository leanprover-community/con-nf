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

/-- The current level of the structure we are building. This is registered as a class so that Lean
can find it easily. -/
class Level where
  (α : Λ)

export Level (α)

variable [Level]

/-- The type index `β` is less than our current level. This is listed as a class so that Lean can
find this hypothesis without having to include the type `β < α` in the goal state. -/
class LtLevel (β : TypeIndex) : Prop where
  elim : β < α

instance {β : Λ} [inst : LtLevel (Option.some β)] : LtLevel β := inst

instance : LtLevel ⊥ where
  elim := bot_lt_coe α

/-- The type index `β` is at most our current level. This is listed as a class so that Lean can
find this hypothesis without having to include the type `β < α` in the goal state. -/
class LeLevel (β : TypeIndex) : Prop where
  elim : β ≤ α

instance : LeLevel α where
  elim := le_rfl

instance {β : TypeIndex} [LtLevel β] : LeLevel β where
  elim := LtLevel.elim.le

instance {β : Λ} [inst : LeLevel (Option.some β)] : LeLevel β := inst

variable {α : TypeIndex}

/-- We define the type of paths from certain types to lower types as inhabitants of this quiver. -/
instance : Quiver TypeIndex :=
  ⟨(· > ·)⟩

/-- A (finite) path from the type `α` to the base type. This is a way that we can perceive
extensionality, iteratively descending to lower types in the hierarchy until we reach the base type.
As `Λ` is well-ordered, there are no infinite descending paths. -/
def ExtendedIndex (α : TypeIndex) :=
  Quiver.Path α ⊥

/-- If there is a path between `α` and `β`, we must have `β ≤ α`.
The case `β = α` can occur with the nil path. -/
theorem le_of_path : ∀ {β : TypeIndex}, Path α β → β ≤ α
  | _, nil => le_rfl
  | _, cons p f => (le_of_lt f).trans <| le_of_path p

/-- Paths from a type index to itself must be the nil path. -/
theorem path_eq_nil : ∀ p : Path α α, p = nil
  | nil => rfl
  | cons p f => ((le_of_path p).not_lt f).elim

/-- Extended indices cannot be the nil path. -/
theorem ExtendedIndex.length_ne_zero {α : Λ} (A : ExtendedIndex α) : A.length ≠ 0 := by
  intro h
  cases Quiver.Path.eq_of_length_zero A h

/-- There are at most `Λ` `α`-extended type indices. -/
@[simp]
theorem mk_extendedIndex_le (α : TypeIndex) : #(ExtendedIndex α) ≤ #Λ := by
  refine le_trans ((Cardinal.le_def _ _).2 ⟨⟨toList, toList_injective (α : TypeIndex) ⊥⟩⟩) ?_
  convert mk_list_le_max _ using 1
  simp only [mk_typeIndex, max_eq_right, aleph0_le_mk]

instance {α : TypeIndex} : Quiver { γ // γ ≤ α } :=
  ⟨(· > ·)⟩

/-- Casts a path to use entries of the form `{ γ // γ ≤ α }` rather than arbitrary type indices.
The unnecessary argument `h` is here so that `castPath h` is a non-dependent function. -/
def castPath : {α β : TypeIndex} → (h : β ≤ α) →
    Path α β → Path (⟨α, le_rfl⟩ : { γ // γ ≤ α }) ⟨β, h⟩
  | α, _, _, .nil => .nil
  | α, β, _, .cons p h' => .cons (castPath (le_of_path p) p) h'

theorem castPath_injective {α β : TypeIndex} (h : β ≤ α) :
    Function.Injective (castPath h) := by
  intro p q hpq
  induction p with
  | nil =>
    cases path_eq_nil q
    rfl
  | cons p h' ih =>
    rw [castPath] at hpq
    cases q with
    | nil =>
      rw [castPath] at hpq
      cases hpq
    | cons q h'' =>
      rw [castPath] at hpq
      simp only [cons.injEq, Subtype.mk.injEq] at hpq
      cases hpq.1
      simp only [heq_eq_eq, and_true, true_and] at hpq
      cases ih _ hpq
      rfl

/-- There are less than `cf(μ)` `α`-extended type indices. -/
@[simp]
theorem mk_extendedIndex_lt_cof_μ (α : TypeIndex) : #(ExtendedIndex α) < (#μ).ord.cof := by
  refine (mk_le_of_injective (castPath_injective (show ⊥ ≤ α from bot_le))).trans_lt ?_
  refine lt_of_le_of_lt ((Cardinal.le_def _ _).2 ⟨⟨toList, toList_injective _ _⟩⟩) ?_
  refine (mk_list_le_max _).trans_lt ?_
  rw [max_lt_iff]
  constructor
  · exact Params.aleph0_lt_mk_κ.trans_le Params.κ_le_μ_ord_cof
  · exact card_Iic_lt_typeIndex α

/-- There are less than `cf(μ)` `α`-extended type indices. -/
@[simp]
theorem mk_extendedIndex_lt_μ (α : TypeIndex) : #(ExtendedIndex α) < #μ :=
  (mk_extendedIndex_lt_cof_μ α).trans_le (Ordinal.cof_ord_le #μ)

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
