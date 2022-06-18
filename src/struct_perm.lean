import litter
import type_index

/-!
# Structural permutations

In this file, we define the ambient groups of *structural permutations*.  These will later have
recursively-constructed subgroups of *semi-allowable* and *allowable permutations* which will act on
tangles; we define these larger ambient groups in advance in order to set up their infrastructure of
derivatives and so on independently of the recursion.
-/

open equiv equiv.perm with_bot

universe u

namespace con_nf
variable [params.{u}]

open params

/-- A *structural permutation* on a proper type index is defined by its derivatives,
as well as its permutation on atoms. -/
/- Note: perhaps should be constructed directly as *groups*, not just types. -/
def struct_perm : Π (β : type_index), Type u
| none := near_litter_perm
| β := Π γ < β, struct_perm γ
using_well_founded { dec_tac := `[assumption] }

namespace struct_perm

-- TODO(zeramorphic): Write this up when Π types on Props can be formed into groups in mathlib.
instance group_instance : Π β, group (struct_perm β) := sorry

/-- Obtains the atom permutation given by a prestructural permutation. -/
def to_near_litter_perm : Π {β : type_index} (π : struct_perm β), near_litter_perm
| none π := by { unfold struct_perm at π, exact π }
| (some β) π := by { unfold struct_perm at π,
  have := π none (by simp), unfold struct_perm at this, exact this }

/-- Obtains the permutations on lower types induced by a prestructural permutation. -/
def lower_struct_perm : Π {β : type_index} (π : struct_perm β) (γ < β), struct_perm γ
| none π γ γ_lt_β := by { exfalso, simp at γ_lt_β, exact γ_lt_β }
| (some β) π γ γ_lt_β := by { unfold struct_perm at π, exact π γ γ_lt_β }

/-- The derivative of a structural permutation at any lower level. -/
def derivative {β : type_index} :
Π {γ : type_index} (A : quiver.path (β : type_index) γ), struct_perm β → struct_perm γ
| _ quiver.path.nil := id
| δ (quiver.path.cons p_βδ lt_γδ) := λ π, lower_struct_perm (derivative p_βδ π) _ lt_γδ

end struct_perm

structure support_condition (α : Λ) :=
(source : atom ⊕ Σ' s i, is_near_litter i s)
(path : extended_index α)

structure potential_support (α : Λ) :=
(carrier : set (support_condition α))
(small : small carrier)

/-- Structural permutations act on support conditions. -/
instance struct_perm_scalar (α : Λ) : has_scalar (struct_perm α) (support_condition α) :=
⟨λ π₀, begin
  rintro ⟨c, path⟩,
  refine ⟨_, path⟩,
  cases c,
  { left, exact π₀.to_near_litter_perm.atom_perm c },
  { right, obtain ⟨s, i, h⟩ := c,
    exact ⟨
      ⇑π₀.to_near_litter_perm.atom_perm⁻¹ ⁻¹' s,
      π₀.to_near_litter_perm.litter_perm i,
      π₀.to_near_litter_perm.near h⟩ }
end⟩

-- TODO(zeramorphic): Complete this when the group instance for structural permutations is written.
instance struct_perm_action (α : Λ) : mul_action (struct_perm α) (support_condition α) := sorry

section support_declaration

variables {α : Λ} {H : Type*} [monoid H] {τ : Type*} [mul_action H τ]

/-- Given `x ∈ τ` and `S` any set of `α`-support conditions, we say `S` supports `x` if every
`π ∈ H` that fixes every element of `S` also fixes `x`.

We do not constrain here that `φ` be a group homomorphism, but this is required later. -/
def supports (φ : H → struct_perm α) (x : τ) (S : set (support_condition α)) :=
∀ (π : H), (∀ s ∈ S, (φ π) • s = s) → π • x = x

/-- A *support for `x`* is a potential support that supports `x`. -/
structure support (φ : H → struct_perm α) (x : τ)
extends potential_support α :=
(supports : supports φ x carrier)

/-- An element of `τ` is *symmetric* if it has some (small) support. -/
def symmetric (φ : H → struct_perm α) (x : τ) : Prop
:= nonempty $ support φ x

end support_declaration

end con_nf
