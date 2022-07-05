import extended_index
import group_theory.group_action.sum
import litter
import mathlib.group_action
import mathlib.support
import pretangle

/-!
# Structural permutations

In this file, we define the ambient groups of *structural permutations*.  These will later have
recursively-constructed subgroups of *semi-allowable* and *allowable permutations* which will act on
tangles; we define these larger ambient groups in advance in order to set up their infrastructure of
derivatives and so on independently of the recursion.
-/

open cardinal equiv equiv.perm quiver with_bot
open_locale cardinal pointwise

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

@[simp] lemma struct_perm.bot_def : struct_perm ⊥ = near_litter_perm := by { unfold struct_perm }

@[simp] lemma struct_perm.coe_def {α : Λ} :
  struct_perm α = Π β : type_index, β < α → struct_perm β :=
by { unfold struct_perm }

def near_litter_perm.to_struct_perm (π : near_litter_perm) : struct_perm ⊥ :=
cast struct_perm.bot_def.symm π

def struct_perm.mk {α : Λ} (lower : Π β : type_index, β < α → struct_perm β) : struct_perm α :=
cast struct_perm.coe_def.symm lower

-- TODO(zeramorphic): write some api

namespace struct_perm
variables {α : type_index}

noncomputable! instance group : Π α, group (struct_perm α)
| ⊥ := cast (by rw struct_perm.bot_def) near_litter_perm.group
| (α : Λ) := cast (by rw struct_perm.coe_def)
  (@pi.group _ _ (λ β, @pi.group_Prop _ _ $ λ _ : β < ↑α, group β))
using_well_founded { dec_tac := `[assumption] }

lemma group_bot :
  struct_perm.group ⊥ = cast (by rw struct_perm.bot_def) near_litter_perm.group :=
by { unfold struct_perm.group }

lemma group_coe (α : Λ) : struct_perm.group α = cast (by rw struct_perm.coe_def)
  (@pi.group _ _ (λ β, @pi.group_Prop _ _ $ λ _ : β < ↑α, struct_perm.group β)) :=
by { unfold struct_perm.group }

lemma one_to_struct_perm_aux : cast struct_perm.bot_def (1 : struct_perm ⊥) = 1 :=
begin
  unfold has_one.one,
  convert cast_eq _ _; try { simp },
  rw group_bot, simp,
end

lemma one_to_struct_perm : (1 : near_litter_perm).to_struct_perm = (1 : struct_perm ⊥) :=
by { unfold near_litter_perm.to_struct_perm, rw ← one_to_struct_perm_aux, simp }

lemma mk_one_aux (α : Λ) : cast struct_perm.coe_def (1 : struct_perm α) = 1 :=
begin
  unfold has_one.one,
  convert cast_eq _ _; try { simp },
  rw group_coe, simp
end

@[simp] lemma mk_one (α : Λ) : mk 1 = (1 : struct_perm α) :=
by { unfold mk, rw ← mk_one_aux, simp }

/-- Obtains the atom permutation given by a structural permutation. -/
def to_near_litter_perm : Π {α}, struct_perm α → near_litter_perm
| ⊥ π := by { unfold struct_perm at π, exact π }
| (α : Λ) π := by { unfold struct_perm at π,
  have := π ⊥ (with_bot.bot_lt_coe _), unfold struct_perm at this, exact this }

@[simp] lemma to_near_litter_perm_one : Π {α}, (1 : struct_perm α).to_near_litter_perm = 1
| ⊥ := sorry
| (α : Λ) := sorry

@[simp] lemma to_near_litter_perm_mul :
  Π {α} (f g : struct_perm α),
    (f * g).to_near_litter_perm = f.to_near_litter_perm * g.to_near_litter_perm
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

@[simp] lemma one_lower : Π (α β : type_index) (hβ : β < α),
  (1 : struct_perm α).lower β hβ = (1 : struct_perm β)
| ⊥ β hβ := by { exfalso, simp only [not_lt_bot] at hβ, exact hβ }
| (α : Λ) β hβ := by { unfold lower, rw ← mk_one, unfold mk, simpa }

@[simp] lemma mul_lower : Π (α β : type_index) (hβ : β < α) (π₁ π₂ : struct_perm α),
  (π₁ * π₂).lower β hβ = π₁.lower β hβ * π₂.lower β hβ
| ⊥ β hβ π₁ π₂ := by { exfalso, simp only [not_lt_bot] at hβ, exact hβ }
| (α : Λ) β hβ π₁ π₂ := sorry

/-- The derivative of a structural permutation at any lower level. -/
def derivative : Π {β} (A : path α β), struct_perm α → struct_perm β
| _ path.nil := id
| γ (path.cons p_αγ lt_βγ) := λ π, (derivative p_αγ π).lower _ lt_βγ

/-- Structural permutations act on atoms. -/
instance mul_action_atom (α : Λ) : mul_action (struct_perm α) atom :=
mul_action.comp_hom _ to_near_litter_perm_hom

/-- Structural permutations act on near-litters. -/
instance mul_action_near_litter (α : Λ) : mul_action (struct_perm α) near_litter :=
mul_action.comp_hom _ to_near_litter_perm_hom

-- TODO: Why can't the equation compiler handle my sorried proofs (the `funext` call breaks things)?
instance mul_action_pretangle : Π (α : Λ), mul_action (struct_perm α) (pretangle α)
| α := {
  smul := λ π t, pretangle.mk (π • t.atom_extension) (λ β hβ, begin
    letI := mul_action_pretangle β,
    exact π.lower β (coe_lt_coe.mpr hβ) • t.extension β hβ,
  end),
  one_smul := λ t, begin
    unfold has_smul.smul,
    convert pretangle.eta t,
    { simp },
    sorry { refine funext (λ β, funext (λ hβ, _)),
      letI := mul_action_pretangle β, rw one_lower, dsimp only, unfold has_smul.smul,
      convert set.image_id _,
      ext t,
      exact one_smul (struct_perm β) t }
  end,
  mul_smul := λ π₁ π₂ t, begin
    unfold has_smul.smul, refine congr (congr rfl _) _,
    { rw pretangle.atom_extension_mk, rw set.image_image, refine set.image_congr' (λ a, _),
      rw [has_smul.comp.smul, has_smul.comp.smul, has_smul.comp.smul,
        mul_hom_class.map_mul, mul_smul] },
    sorry { refine funext (λ β, funext (λ hβ, _)),
      letI := mul_action_pretangle β,
      dsimp only, rw [mul_lower, mul_smul], simp }
  end
}
using_well_founded { dec_tac := `[assumption] }

end struct_perm

/-- A support condition is an atom or a near-litter together with an extended type index. -/
@[derive [inhabited, mul_action near_litter_perm, mul_action (struct_perm ‹Λ›)]]
def support_condition (α : Λ) : Type u := (atom ⊕ near_litter) × extended_index α

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

instance (α : Λ) : set_like (potential_support α) (support_condition α) :=
{ coe := potential_support.carrier,
  coe_injective' := λ s t h, by { cases s, cases t, congr' } }

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

section support_declaration

variables {α : Λ} {H τ : Type u} [monoid H] [mul_action H τ]

/-- A *support for `x`* is a potential support that supports `x`. -/
structure support (φ : H → struct_perm α) (x : τ) extends potential_support α :=
(supports : supports φ carrier x)

/-- An element of `τ` is *symmetric* if it has some (small) support. -/
def symmetric (φ : H → struct_perm α) (x : τ) : Prop := nonempty $ support φ x

/-- There are at most `μ` supports for a given `x : τ`. -/
@[simp] lemma mk_support_le (φ : H → struct_perm α) (x : τ) : #(support φ x) ≤ #μ :=
begin
  have : support φ x ≃ {S : potential_support α // supports φ S.carrier x},
  { refine ⟨λ S, ⟨S.1, S.2⟩, λ S, ⟨S.1, S.2⟩, _, _⟩; intro x; dsimp; cases x; simp },
  rw [cardinal.mk_congr this, ←mk_potential_support α],
  exact mk_subtype_le _,
end

end support_declaration
end con_nf
