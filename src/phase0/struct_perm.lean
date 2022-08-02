import group_theory.group_action.sum
import logic.equiv.transfer_instance
import mathlib.group_action
import mathlib.logic
import phase0.index
import phase0.litter
import phase0.pretangle

/-!
# Structural permutations

In this file, we define the ambient groups of *structural permutations*.  These will later have
recursively-constructed subgroups of *semi-allowable* and *allowable permutations* which will act on
tangles; we define these larger ambient groups in advance in order to set up their infrastructure of
derivatives and so on independently of the recursion.
-/

open cardinal equiv quiver quiver.path with_bot
open_locale cardinal pointwise

noncomputable theory

universe u

namespace con_nf
variable [params.{u}]

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

lemma coe_def (α : Λ) : struct_perm ↑α = Π β : type_index, β < α → struct_perm β :=
by unfold struct_perm

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

noncomputable! instance group : Π α, group (struct_perm α)
| ⊥ := of_bot.group
| (α : Λ) := @equiv.group _ _ of_coe $ @pi.group _ _ $ λ β,
  @pi.group_Prop _ _ $ λ _ : β < ↑α, group β
using_well_founded { dec_tac := `[assumption] }

/--  The isomorphism between near-litter permutations and bottom structural permutations. This holds
by definition of `struct_perm`. -/
@[simps] def to_bot_iso : near_litter_perm ≃* struct_perm ⊥ :=
{ map_mul' := λ a b, begin
    rw [show struct_perm.group ⊥ = _, by unfold struct_perm.group],
    congr,
    all_goals { dsimp [to_bot, of_bot], rw [cast_cast, cast_eq] },
  end,
  ..to_bot }

/--  The isomorphism between the product of structural permutations under `α` and `α`-structural
permutations. This holds by definition of `struct_perm`. -/
@[simps] def to_coe_iso (α : Λ) : (Π β : type_index, β < α → struct_perm β) ≃* struct_perm α :=
{ map_mul' := λ a b, begin
    dsimp only [(has_mul.mul), (mul_one_class.mul), (monoid.mul), (div_inv_monoid.mul)],
    have : struct_perm.group α = _,
    unfold struct_perm.group,
    rw this,
    congr,
    dsimp only [(*), (mul_one_class.mul), (monoid.mul), (div_inv_monoid.mul), (group.mul)],
    apply funext, intro i, apply funext, intro i_1,
    have : ∀ z : Π (β : type_index), β < ↑α → struct_perm β, of_coe (to_coe.to_fun z) i i_1 = z i i_1,
    { intro z,
      dsimp [of_coe, to_coe],
      rw [cast_cast, cast_eq] },
    convert rfl,
    exact this _, exact this _,
  end,
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

@[simp] lemma to_near_litter_perm_to_bot (f : near_litter_perm) :
  (to_bot f).to_near_litter_perm = f :=
by simp [to_near_litter_perm]

/-- The derivative of a structural permutation at any lower level. -/
noncomputable def derivative : Π {β}, path α β → struct_perm α →* struct_perm β
| _ nil := monoid_hom.id _
| γ (cons p_αγ hβγ) := (lower $ le_of_lt hβγ).comp $ derivative p_αγ

/-- The derivative along the empty path does nothing. -/
@[simp] lemma derivative_nil (π : struct_perm α) : derivative nil π = π := rfl

/-- The derivative map is functorial. -/
lemma derivative_derivative (π : struct_perm α) (p : path α β) :
  ∀ {γ : type_index} (q : path β γ), derivative q (derivative p π) = derivative (p.comp q) π
| _ nil := by simp only [derivative_nil, comp_nil]
| γ (cons q f) := by simp only [comp_cons, derivative, monoid_hom.coe_comp, function.comp_app,
  derivative_derivative]

/-- The derivative map preserves multiplication. -/
lemma derivative_mul {β} (π₁ π₂ : struct_perm α) (A : path (α : type_index) β) :
  derivative A (π₁ * π₂) = derivative A π₁ * derivative A π₂ := by simp only [map_mul]

section
variables {X : Type*} [mul_action near_litter_perm X]

/-- Structural permutations act on atoms. -/
instance mul_action_of_near_litter_perm : mul_action (struct_perm α) X :=
mul_action.comp_hom _ to_near_litter_perm

@[simp] lemma to_near_litter_perm_smul (f : struct_perm α) (x : X) :
  f.to_near_litter_perm • x = f • x := rfl

@[simp] lemma to_bot_smul (f : near_litter_perm) (x : X) : to_bot f • x = f • x :=
by { change to_near_litter_perm _ • _ = _ • _, rw to_near_litter_perm_to_bot }

end

-- TODO: Why can't the equation compiler handle my sorried proofs (the `funext` call breaks things)?
instance mul_action_pretangle : Π (α : Λ), mul_action (struct_perm α) (pretangle α)
| α :=
{ smul := λ π t, pretangle.mk (π • t.atom_extension) (λ β hβ, begin
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
  end }
using_well_founded { dec_tac := `[assumption] }

@[simp] lemma derivative_cons_nil (α : Λ) (f : struct_perm α) (β : type_index) (hβ : β < α) :
  derivative (cons nil hβ) f = of_coe f β hβ :=
by { unfold derivative lower, rw dif_neg hβ.ne, refl }

lemma ext (α : Λ) (a b : struct_perm α)
  (h : ∀ (β : type_index) (hβ : β < α), derivative (cons nil hβ) a = derivative (cons nil hβ) b) :
  a = b :=
of_coe.injective $ by { ext β hβ, simp_rw ←derivative_cons_nil, exact h _ _ }

end struct_perm
end con_nf
