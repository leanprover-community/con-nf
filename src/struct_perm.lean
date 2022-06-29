import extended_index
import group_theory.group_action.sigma
import group_theory.group_action.sum
import litter
import mathlib.group

/-!
# Structural permutations

In this file, we define the ambient groups of *structural permutations*.  These will later have
recursively-constructed subgroups of *semi-allowable* and *allowable permutations* which will act on
tangles; we define these larger ambient groups in advance in order to set up their infrastructure of
derivatives and so on independently of the recursion.
-/

open cardinal equiv equiv.perm with_bot
open_locale cardinal

noncomputable theory

universe u

namespace con_nf
variable [params.{u}]

open params

/-- A *structural permutation* on a proper type index is defined by its derivatives,
as well as its permutation on atoms. -/
/- Note: perhaps should be constructed directly as *groups*, not just types. -/
def struct_perm : Π α : type_index, Type u
| ⊥ := near_litter_perm
| (α : Λ) := Π β : type_index, β < α → struct_perm β
using_well_founded { dec_tac := `[assumption] }

noncomputable! instance : Π α, inhabited (struct_perm α)
| ⊥ := by { unfold struct_perm, exact near_litter_perm.inhabited }
| (α : Λ) := by { unfold struct_perm,
  exact @pi.inhabited _ _ (λ β, @pi.inhabited _ _ $ λ _ : β < ↑α, struct_perm.inhabited β) }
using_well_founded { dec_tac := `[assumption] }

namespace struct_perm
variables {α : type_index}

noncomputable! instance struct_perm.group : Π α, group (struct_perm α)
| ⊥ := by { unfold struct_perm, exact near_litter_perm.group }
| (α : Λ) := by { unfold struct_perm,
  exact @pi.group _ _ (λ β, @pi.group_Prop _ _ $ λ _ : β < ↑α, struct_perm.group β) }
using_well_founded { dec_tac := `[assumption] }

/-- Obtains the atom permutation given by a prestructural permutation. -/
def to_near_litter_perm : Π {α}, struct_perm α → near_litter_perm
| ⊥ π := by { unfold struct_perm at π, exact π }
| (α : Λ) π := by { unfold struct_perm at π,
  have := π ⊥ (with_bot.bot_lt_coe _), unfold struct_perm at this, exact this }

@[simp] lemma to_near_litter_perm_one : Π {α}, (1 : struct_perm α).to_near_litter_perm = 1
| ⊥ := sorry
| (α : Λ) := sorry

@[simp] lemma to_near_litter_perm_mul :
  Π {α} (f g : struct_perm α),
    (f  * g).to_near_litter_perm = f.to_near_litter_perm * g.to_near_litter_perm
| ⊥ := sorry
| (α : Λ) := sorry

/-- `to_near_litter_perm` as a monoid homomorphism. -/
@[simps] def to_near_litter_perm_hom : struct_perm α →* near_litter_perm :=
{ to_fun := to_near_litter_perm,
  map_one' := to_near_litter_perm_one,
  map_mul' := to_near_litter_perm_mul }

/-- Obtains the permutations on lower types induced by a prestructural permutation. -/
def lower : Π {α} (π : struct_perm α) (β < α), struct_perm β
| ⊥ π β β_lt_α := by { exfalso, simp at β_lt_α, exact β_lt_α }
| (α : Λ) π β β_lt_α := by { unfold struct_perm at π, exact π β β_lt_α }

/-- The derivative of a structural permutation at any lower level. -/
def derivative :
  Π {β} (A : quiver.path (α) β), struct_perm α → struct_perm β
| _ quiver.path.nil := id
| γ (quiver.path.cons p_αγ lt_βγ) := λ π, (derivative p_αγ π).lower _ lt_βγ

end struct_perm

/-- A support condition is an atom or a near-litter together with an extended type index. -/
@[derive inhabited] def support_condition (α : Λ) : Type u :=
(atom ⊕ near_litter) × extended_index α

/-- There are `μ` support conditions. -/
@[simp] lemma mk_support_condition (α : Λ) : #(support_condition α) = #μ :=
begin
  simp only [support_condition, mk_prod, mk_sum, mk_atom, lift_id, mk_near_litter],
  rw add_eq_left (κ_regular.aleph_0_le.trans κ_le_μ) le_rfl,
  exact mul_eq_left (κ_regular.aleph_0_le.trans κ_le_μ)
    (le_trans (mk_extended_index α) $ le_of_lt $ lt_trans Λ_lt_κ κ_lt_μ) (mk_ne_zero _),
end

/-- A potential support is a small set of support conditions. -/
structure potential_support (α : Λ) :=
(carrier : set (support_condition α))
(small : small carrier)

/-- There are `μ` potential supports. -/
@[simp] lemma mk_potential_support (α : Λ) : #(potential_support α) = #μ :=
begin
  have : potential_support α ≃ {S : set (support_condition α) // small S},
  { refine ⟨λ s, ⟨s.carrier, s.small⟩, λ s, ⟨s.val, s.property⟩, _, _⟩; intro x; cases x; simp },
  obtain ⟨e⟩ := cardinal.eq.1 (mk_support_condition α),
  refine le_antisymm _ ⟨⟨λ m, ⟨{e.symm m}, by simp⟩, λ a b h, by { simp at h, exact h }⟩⟩,
  have lt_cof_eq_μ : #{S : set (support_condition α) // #S < (#μ).ord.cof} = #μ,
  { convert mk_subset_mk_lt_cof μ_strong_limit.2 using 1,
    have := mk_subtype_of_equiv (λ S, # ↥S < (#μ).ord.cof) (equiv.set.congr e),
    convert this using 1,
    suffices : ∀ S, # ↥S = # ↥(set.congr e S), { simp_rw this },
    intro S, rw cardinal.eq, exact ⟨equiv.image _ _⟩ },
  rw [mk_congr this, ←lt_cof_eq_μ],
  exact cardinal.mk_subtype_mono (λ S (h : _ < _), h.trans_le κ_le_μ_cof),
end

/-- Structural permutations act on atoms. -/
instance mul_action_atom (α : Λ) : mul_action (struct_perm α) atom :=
mul_action.comp_hom _ struct_perm.to_near_litter_perm_hom

/-- Structural permutations act on near-litters. -/
instance mul_action_near_litter (α : Λ) : mul_action (struct_perm α) near_litter :=
mul_action.comp_hom _ struct_perm.to_near_litter_perm_hom

/-- Structural permutations act (trivially) on extended type indices. -/
instance mul_action_extended_index (α : Λ) : mul_action (struct_perm α) (extended_index α) :=
{ smul := λ _, id, one_smul := λ _, rfl, mul_smul := λ _ _ _, rfl }

instance mul_action_support_condition (α : Λ) : mul_action (struct_perm α) (support_condition α) :=
prod.mul_action

section support_declaration

variables {α : Λ} {H τ : Type u} [monoid H] [mul_action H τ]

/-- Given `x ∈ τ` and `S` any set of `α`-support conditions, we say `S` supports `x` if every
`π ∈ H` that fixes every element of `S` also fixes `x`.

We do not constrain here that `φ` be a group homomorphism, but this is required later. -/
def supports (φ : H → struct_perm α) (x : τ) (S : set (support_condition α)) :=
∀ π, (∀ s ∈ S, φ π • s = s) → π • x = x

/-- A *support for `x`* is a potential support that supports `x`. -/
structure support (φ : H → struct_perm α) (x : τ) extends potential_support α :=
(supports : supports φ x carrier)

/-- An element of `τ` is *symmetric* if it has some (small) support. -/
def symmetric (φ : H → struct_perm α) (x : τ) : Prop := nonempty $ support φ x

/-- There are at most `μ` supports for a given `x : τ`. -/
@[simp] lemma mk_support_le (φ : H → struct_perm α) (x : τ) : #(support φ x) ≤ #μ :=
begin
  have : support φ x ≃ {S : potential_support α // supports φ x S.carrier},
  { refine ⟨λ S, ⟨S.1, S.2⟩, λ S, ⟨S.1, S.2⟩, _, _⟩; intro x; dsimp; cases x; simp },
  rw [cardinal.mk_congr this, ←mk_potential_support α],
  exact mk_subtype_le _,
end

end support_declaration
end con_nf
