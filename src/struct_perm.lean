import extended_index
import group_theory.group_action.sum
import litter
import logic.equiv.transfer_instance
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

namespace struct_perm
section
variables {α β : Λ} {γ : type_index}

noncomputable! instance : Π α, inhabited (struct_perm α)
| ⊥ := by { unfold struct_perm, exact near_litter_perm.inhabited }
| (α : Λ) := by { unfold struct_perm,
  exact @pi.inhabited _ _ (λ β, @pi.inhabited _ _ $ λ _ : β < ↑α, inhabited β) }
using_well_founded { dec_tac := `[assumption] }

/-- The "identity" equivalence between `near_litter_perm` and `struct_perm ⊥`. -/
def to_bot : near_litter_perm ≃ struct_perm ⊥ := equiv.cast $ by { unfold struct_perm }

/-- The "identity" equivalence between `struct_perm ⊥` and `near_litter_perm`. -/
def of_bot : struct_perm ⊥ ≃ near_litter_perm := equiv.cast $ by { unfold struct_perm }

/-- The "identity" equivalence between `Π β < α, struct_perm β)` and `struct_perm α`. -/
def to_coe : (Π β : type_index, β < α → struct_perm β) ≃ struct_perm α :=
equiv.cast $ by { unfold struct_perm }

/-- The "identity" equivalence between `struct_perm α` and `Π β < α, struct_perm β)`. -/
def of_coe : struct_perm α ≃ Π β : type_index, β < α → struct_perm β :=
equiv.cast $ by { unfold struct_perm }

@[simp] lemma to_bot_symm : to_bot.symm = of_bot := rfl
@[simp] lemma of_bot_symm : of_bot.symm = to_bot := rfl
@[simp] lemma to_coe_symm : to_coe.symm = (of_coe : struct_perm α ≃ _) := rfl
@[simp] lemma of_coe_symm : of_coe.symm = (to_coe : _ ≃ struct_perm α) := rfl
@[simp] lemma to_bot_of_bot (a) : to_bot (of_bot a) = a := by simp [to_bot, of_bot]
@[simp] lemma of_bot_to_bot (a) : of_bot (to_bot a) = a := by simp [to_bot, of_bot]
@[simp] lemma to_coe_of_coe (a : struct_perm α) : to_coe (of_coe a) = a := by simp [to_coe, of_coe]
@[simp] lemma of_coe_to_coe (a) : of_coe (to_coe a : struct_perm α) = a := by simp [to_coe, of_coe]
@[simp] lemma to_bot_inj {a b} : to_bot a = to_bot b ↔ a = b := to_bot.injective.eq_iff
@[simp] lemma of_bot_inj {a b} : of_bot a = of_bot b ↔ a = b := of_bot.injective.eq_iff
@[simp] lemma to_coe_inj {a b} : (to_coe a : struct_perm α) = to_coe b ↔ a = b :=
to_coe.injective.eq_iff
@[simp] lemma of_coe_inj {a b : struct_perm α} : of_coe a = of_coe b ↔ a = b :=
of_coe.injective.eq_iff

@[simp] lemma of_coe_of_coe (hγβ : γ < β) (hβα) (f : struct_perm α) :
  of_coe (of_coe f _ $ hβα) _ hγβ = of_coe f _ (hγβ.trans hβα) :=
sorry

noncomputable! instance group : Π α, group (struct_perm α)
| ⊥ := of_bot.group
| (α : Λ) := @equiv.group _ _ of_coe $ @pi.group _ _ $ λ β,
  @pi.group_Prop _ _ $ λ _ : β < ↑α, group β
using_well_founded { dec_tac := `[assumption] }

@[simps] def to_bot_iso : near_litter_perm ≃* struct_perm ⊥ :=
{ map_mul' := sorry,
  ..to_bot }

@[simps] def to_coe_iso (α : Λ) : (Π β : type_index, β < α → struct_perm β) ≃* struct_perm α :=
{ map_mul' := sorry,
  ..to_coe }

@[simp] lemma to_bot_one : to_bot 1 = 1 := to_bot_iso.map_one
@[simp] lemma of_bot_one : of_bot 1 = 1 := to_bot_iso.symm.map_one
@[simp] lemma to_bot_mul (a b) : to_bot (a * b) = to_bot a * to_bot b := to_bot_iso.map_mul _ _
@[simp] lemma of_bot_mul (a b) : of_bot (a * b) = of_bot a * of_bot b := to_bot_iso.symm.map_mul _ _

@[simp] lemma to_coe_one : (to_coe 1 : struct_perm α) = 1 := (to_coe_iso α).map_one
@[simp] lemma of_coe_one : of_coe (1 : struct_perm α) = 1 := (to_coe_iso α).symm.map_one
@[simp] lemma to_coe_mul (a b) : (to_coe (a * b) : struct_perm α) = to_coe a * to_coe b :=
(to_coe_iso α).map_mul _ _
@[simp] lemma of_coe_mul (a b : struct_perm α) : of_coe (a * b) = of_coe a * of_coe b :=
(to_coe_iso α).symm.map_mul _ _

end

variables {α β γ : type_index}

/-- Obtains the permutations on lower types induced by a structural permutation. -/
def lower : ∀ {α β : type_index}, β ≤ α → struct_perm α →* struct_perm β
| ⊥ ⊥ hβ := monoid_hom.id _
| ⊥ (β : Λ) hβ := (not_coe_le_bot _ hβ).elim
| (α : Λ) β hβ := if h : β = α then by { subst h, exact monoid_hom.id _ } else
  { to_fun := λ f, of_coe f _ $ hβ.lt_of_ne h,
  map_one' := congr_fun₂ of_coe_one _ _,
  map_mul' := λ _ _, congr_fun₂ (of_coe_mul _ _) _ _ }

@[simp] lemma lower_self : lower le_rfl = monoid_hom.id (struct_perm α) :=
by { cases α, { refl }, { exact dif_pos rfl } }

/-- The near-litter permutation associated to a structural permutation. -/
def to_near_litter_perm : struct_perm α →* near_litter_perm :=
to_bot_iso.symm.to_monoid_hom.comp $ lower bot_le

/-- The derivative of a structural permutation at any lower level. -/
noncomputable def derivative : Π {β}, path α β → struct_perm α →* struct_perm β
| _ path.nil := monoid_hom.id _
| γ (path.cons p_αγ hβγ) := (lower hβγ).comp $ derivative p_αγ

/-- Structural permutations act on atoms. -/
instance mul_action_atom (α : Λ) : mul_action (struct_perm α) atom :=
mul_action.comp_hom _ to_near_litter_perm

/-- Structural permutations act on near-litters. -/
instance mul_action_near_litter (α : Λ) : mul_action (struct_perm α) near_litter :=
mul_action.comp_hom _ to_near_litter_perm

-- TODO: Why can't the equation compiler handle my sorried proofs (the `funext` call breaks things)?
instance mul_action_pretangle : Π (α : Λ), mul_action (struct_perm α) (pretangle α)
| α := {
  smul := λ π t, pretangle.mk (π • t.atom_extension) (λ β hβ, begin
    letI := mul_action_pretangle β,
    exact lower (coe_lt_coe.2 hβ).le π • t.extension β hβ,
  end),
  one_smul := λ t, begin
    unfold has_smul.smul,
    convert pretangle.eta t,
    { simp },
    sorry { refine funext (λ β, funext (λ hβ, _)),
      letI := mul_action_pretangle β, rw lower_one, dsimp only, unfold has_smul.smul,
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
      dsimp only, rw [lower_mul, mul_smul], simp }
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
