import mathlib.quiver
import mathlib.with_bot
import phase0.params

open cardinal function quiver quiver.path set with_bot
open_locale cardinal

universe u

namespace con_nf
variables [params.{u}]

section Iio
variables {α β : Λ}

instance coe_Iio : has_coe_t (Iio α) (Iio (α : type_index)) := ⟨λ β, ⟨β.1, coe_lt_coe.2 β.2⟩⟩

@[simp] lemma Iio.coe_mk (β : Λ) (hβ : β < α) :
  ((⟨β, hβ⟩ : Iio α) : Iio (α : type_index)) = ⟨β, coe_lt_coe.2 hβ⟩ := rfl

lemma Iio.coe_injective : injective (coe : Iio α → Iio (α : type_index)) :=
begin
  rintro ⟨β, hβ⟩ ⟨γ, hγ⟩ h,
  simp only [Iio.coe_mk, subtype.mk_eq_mk] at h,
  have := with_bot.coe_injective h,
  subst this,
end

@[simp] lemma Iio.coe_inj {β γ : Iio α} : (β : Iio (α : type_index)) = γ ↔ β = γ :=
Iio.coe_injective.eq_iff

variables {hβ : (β : type_index) ∈ Iio (α : type_index)}

instance : has_bot (Iio (α : type_index)) := ⟨⟨⊥, bot_lt_coe _⟩⟩
instance : inhabited (Iio (α : type_index)) := ⟨⊥⟩

@[simp] lemma bot_ne_mk_coe : (⊥ : Iio (α : type_index)) ≠ ⟨β, hβ⟩ :=
ne_of_apply_ne subtype.val bot_ne_coe

@[simp] lemma mk_coe_ne_bot : (⟨β, hβ⟩ : Iio (α : type_index)) ≠ ⊥ :=
ne_of_apply_ne subtype.val coe_ne_bot

end Iio

variables {α : type_index}

/-- We define the type of paths from certain types to lower types as elements of this quiver. -/
instance quiver : quiver type_index := ⟨(>)⟩

/-- A (finite) path from the type α to the base type.
This can be seen as a way that we can perceive extensionality, iteratively descending to lower
types in the hierarchy until we reach the base type.
This plays the role of an extended type index in the paper. -/
def extended_index (α : type_index) := quiver.path α ⊥

/-- If there is a path between `α` and `β`, we must have `β ≤ α`.
The case `β = α` can occur with the nil path. -/
lemma le_of_path : Π {β : type_index}, path α β → β ≤ α
| β nil := le_rfl
| β (cons p f) := (le_of_lt f).trans $ le_of_path p

lemma path_eq_nil : ∀ p : path α α, p = nil
| nil := rfl
| (cons p f) := ((le_of_path p).not_lt f).elim

/-- There are at most `Λ` `α`-extended type indices. -/
@[simp] lemma mk_extended_index (α : type_index) : #(extended_index α) ≤ #Λ :=
begin
  refine le_trans ((cardinal.le_def _ _).mpr ⟨path.to_list_embedding (α : type_index) ⊥⟩) _,
  convert mk_list_le_max _ using 1, simp, rw max_eq_right Λ_limit.aleph_0_le
end

/-- If `β < γ`, we have a path directly between the two types in the opposite order.
Note that the `⟶` symbol (long right arrow) is not the normal `→` (right arrow),
even though monospace fonts often display them similarly. -/
instance lt_to_hom (β γ : Λ) : has_lift_t (β < γ) ((γ : type_index) ⟶ β) := ⟨coe_lt_coe.2⟩

/-- The direct path from the base type to `α`. -/
def type_index.extend : Π α : type_index, extended_index α
| ⊥ := nil
| (α : Λ) := hom.to_path $ with_bot.bot_lt_coe α

instance (α : type_index) : inhabited (extended_index α) := ⟨α.extend⟩

/-- There exists an `α`-extended type index. --/
lemma mk_extended_index_ne_zero (α : type_index) : #(extended_index α) ≠ 0 := cardinal.mk_ne_zero _

/-- For our purposes, we let any monoid act trivially on extended type indices. -/
instance {M : Type*} [monoid M] : mul_action M (extended_index α) :=
{ smul := λ _, id, one_smul := λ _, rfl, mul_smul := λ _ _ _, rfl }

end con_nf
