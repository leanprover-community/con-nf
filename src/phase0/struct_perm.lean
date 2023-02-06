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

open cardinal equiv quiver quiver.path set with_bot
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
def to_bot : near_litter_perm ≃ struct_perm ⊥ := equiv.cast $ by unfold struct_perm

/-- The "identity" equivalence between `struct_perm ⊥` and `near_litter_perm`. -/
def of_bot : struct_perm ⊥ ≃ near_litter_perm := equiv.cast $ by unfold struct_perm

/-- The "identity" equivalence between `Π β < α, struct_perm β` and `struct_perm α`. -/
def to_coe : (Π β : type_index, β < α → struct_perm β) ≃ struct_perm α :=
equiv.cast $ by unfold struct_perm

/-- The "identity" equivalence between `struct_perm α` and `Π β < α, struct_perm β`. -/
def of_coe : struct_perm α ≃ Π β : type_index, β < α → struct_perm β :=
equiv.cast $ by unfold struct_perm

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
  @pi_Prop.group _ _ $ λ _ : β < ↑α, group β
using_well_founded { dec_tac := `[assumption] }

/--  The isomorphism between near-litter permutations and bottom structural permutations. This holds
by definition of `struct_perm`. -/
def to_bot_iso : near_litter_perm ≃* struct_perm ⊥ :=
{ map_mul' := λ a b,
  by { rw [show struct_perm.group ⊥ = _, by unfold struct_perm.group], congr; simp },
  ..to_bot }

@[simp] lemma coe_to_bot_iso : ⇑to_bot_iso = to_bot := rfl
@[simp] lemma coe_to_bot_iso_symm : ⇑to_bot_iso.symm = of_bot := rfl

/--  The isomorphism between the product of structural permutations under `α` and `α`-structural
permutations. This holds by definition of `struct_perm`. -/
def to_coe_iso (α : Λ) : (Π β : type_index, β < α → struct_perm β) ≃* struct_perm α :=
{ map_mul' := λ a b,
    by { rw [show struct_perm.group α = _, by unfold struct_perm.group], congr; simp },
  ..to_coe }

@[simp] lemma coe_to_coe_iso (α : Λ) : ⇑(to_coe_iso α) = to_coe := rfl
@[simp] lemma coe_to_coe_iso_symm (α : Λ) : ⇑(to_coe_iso α).symm = of_coe := rfl

@[simp] lemma to_bot_one : to_bot 1 = 1 := to_bot_iso.map_one
@[simp] lemma of_bot_one : of_bot 1 = 1 := to_bot_iso.symm.map_one
@[simp] lemma to_bot_mul (a b) : to_bot (a * b) = to_bot a * to_bot b := to_bot_iso.map_mul _ _
@[simp] lemma of_bot_mul (a b) : of_bot (a * b) = of_bot a * of_bot b := to_bot_iso.symm.map_mul _ _
@[simp] lemma to_bot_inv (a) : to_bot a⁻¹ = (to_bot a)⁻¹ := to_bot_iso.map_inv _
@[simp] lemma of_bot_inv (a) : of_bot a⁻¹ = (of_bot a)⁻¹ := to_bot_iso.symm.map_inv _

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

@[simp] lemma coe_to_near_litter_perm :
  (to_near_litter_perm : struct_perm ⊥ → near_litter_perm) = of_bot :=
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
by { change to_near_litter_perm _ • _ = _ • _, rw [coe_to_near_litter_perm, of_bot_to_bot] }

@[simp] lemma of_bot_smul (f : struct_perm ⊥) (x : X) : of_bot f • x = f • x :=
by rw [←to_bot_smul, to_bot_of_bot]

lemma smul_near_litter_fst (π : struct_perm α) (N : near_litter) : (π • N).fst = π • N.fst := rfl

end

def proto_smul : Π α : type_index, struct_perm α → pretangle α → pretangle α
| ⊥ := λ π t, pretangle.to_bot $ of_bot π • t.of_bot
| (α : Λ) := λ π t, pretangle.to_coe $ λ β (hβ : β < α), proto_smul β (of_coe π β hβ) '' pretangle.of_coe t β hβ
using_well_founded { dec_tac := `[assumption] }

instance has_smul_pretangle : Π α : type_index, has_smul (struct_perm α) (pretangle α) | α := ⟨proto_smul α⟩

@[simp] lemma of_bot_smul_pretangle (π : struct_perm ⊥) (t : pretangle ⊥) :
  (π • t).of_bot = of_bot π • t.of_bot :=
begin
dsimp [struct_perm.has_smul_pretangle],
have : (proto_smul ⊥) = λ π t, pretangle.to_bot $ of_bot π • t.of_bot,
unfold proto_smul,
rw this,
simp only [pretangle.of_bot_to_bot],
end

@[simp] lemma to_bot_smul_pretangle (π : near_litter_perm) (t : atom) :
   pretangle.to_bot (π • t) = to_bot π • pretangle.to_bot t :=
pretangle.of_bot.injective $
  by simp_rw [of_bot_smul_pretangle, of_bot_to_bot, pretangle.of_bot_to_bot]

@[simp] lemma of_coe_smul_pretangle {α : Λ} (π : struct_perm α) (t : pretangle α) :
  (π • t).of_coe = of_coe π • t.of_coe :=
begin
dsimp [struct_perm.has_smul_pretangle],
unfold proto_smul,
simp only [pretangle.of_coe_to_coe],
refl,
  end

@[simp] lemma to_coe_smul_pretangle {α : Λ} (π : Π β : type_index, β < α → struct_perm β)
  (t : Π β : type_index, β < α → set (pretangle β)) :
  pretangle.to_coe (π • t) = to_coe π • pretangle.to_coe t :=
pretangle.of_coe.injective $
  by simp_rw [of_coe_smul_pretangle, of_coe_to_coe, pretangle.of_coe_to_coe]

protected lemma one_smul : ∀ α (t : pretangle α), (1 : struct_perm α) • t = t
| ⊥ := λ t, pretangle.of_bot.injective $ by simp
| (α : Λ) := λ t, pretangle.of_coe.injective $
    by { ext β hβ : 2, simp [←image_smul, one_smul β, image_id'] }
using_well_founded { dec_tac := `[assumption] }

protected lemma mul_smul :
  ∀ α (π₁ π₂ : struct_perm α) (t : pretangle α), (π₁ * π₂) • t = π₁ • π₂ • t
| ⊥ := λ π₁ π₂ t, pretangle.of_bot.injective $ by simp [mul_action.mul_smul]
| (α : Λ) := λ π₁ π₂ t, pretangle.of_coe.injective $
    by { ext β hβ : 2, simp only [of_coe_smul_pretangle, of_coe_mul, pi.smul_apply', pi.mul_apply,
      pi_Prop.smul_apply', ←image_smul, image_image, ←mul_smul β], refl }
using_well_founded { dec_tac := `[assumption] }

instance mul_action_pretangle : mul_action (struct_perm α) (pretangle α) :=
{ smul := (•),
  one_smul := struct_perm.one_smul _,
  mul_smul := struct_perm.mul_smul _ }

@[simp] lemma derivative_cons_nil (α : Λ) (f : struct_perm α) (β : type_index) (hβ : β < α) :
  derivative (cons nil hβ) f = of_coe f β hβ :=
by { unfold derivative lower, rw dif_neg hβ.ne, refl }

lemma ext (α : Λ) (a b : struct_perm α)
  (h : ∀ (β : type_index) (hβ : β < α), derivative (cons nil hβ) a = derivative (cons nil hβ) b) :
  a = b :=
of_coe.injective $ by { ext β hβ, simp_rw ←derivative_cons_nil, exact h _ _ }

instance : has_faithful_smul (struct_perm ⊥) atom :=
⟨λ f g h, of_bot.injective $ near_litter_perm.ext $ eq_of_smul_eq_smul h⟩

end struct_perm
end con_nf
