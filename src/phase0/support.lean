import mathlib.support
import phase0.struct_perm

/-!
# Supports
-/

open cardinal equiv quiver
open_locale cardinal

noncomputable theory

universe u

namespace con_nf
variables [params.{u}] {α : type_index}

/-- A support condition is an atom or a near-litter together with an extended type index. -/
@[derive [inhabited]]
def support_condition (α : type_index) : Type u := (atom ⊕ near_litter) × extended_index α

/-- The "identity" equivalence between `(atom ⊕ near_litter) × extended_index α` and
`support_condition α`. -/
def to_condition : (atom ⊕ near_litter) × extended_index α ≃ support_condition α := equiv.refl _

/-- The "identity" equivalence between `support_condition α` and
`(atom ⊕ near_litter) × extended_index α`. -/
def of_condition : support_condition α ≃ (atom ⊕ near_litter) × extended_index α := equiv.refl _

/-- There are `μ` support conditions. -/
@[simp] lemma mk_support_condition (α : type_index) : #(support_condition α) = #μ :=
begin
  simp only [support_condition, mk_prod, mk_sum, mk_atom, lift_id, mk_near_litter],
  rw add_eq_left (κ_regular.aleph_0_le.trans κ_le_μ) le_rfl,
  exact mul_eq_left (κ_regular.aleph_0_le.trans κ_le_μ)
    (le_trans (mk_extended_index α) $ le_of_lt $ lt_trans Λ_lt_κ κ_lt_μ) (mk_ne_zero _),
end

namespace struct_perm

instance mul_action_support_condition : mul_action (struct_perm α) (support_condition α) :=
{ smul := λ π c, ⟨derivative c.snd π • c.fst, c.snd⟩,
  one_smul := by { rintro ⟨atoms | Ns, A⟩; unfold has_smul.smul; simp },
  mul_smul := begin
    rintro π₁ π₂ ⟨atoms | Ns, A⟩; unfold has_smul.smul;
    rw derivative_mul; dsimp; rw mul_smul,
  end }

instance mul_action_support_condition' {B : le_index α} {β : type_index} {γ : type_index}
  {hγ : γ < β}
  (A : path (B : type_index) β) :
  mul_action (struct_perm ((lt_index.mk' hγ (B.path.comp A)) : le_index α).index)
    (support_condition γ) :=
struct_perm.mul_action_support_condition

instance mul_action_support_condition_lt_index
  {β γ : type_index} {hγ : γ < β} (A : path α β) :
  mul_action (struct_perm (lt_index.mk' hγ A)) (support_condition γ) :=
struct_perm.mul_action_support_condition

instance mul_action_support_condition_lt_index'
  {β γ : type_index} {hγ : γ < β} (A : path α β) :
  mul_action (struct_perm (lt_index.mk' hγ A : le_index α).index) (support_condition γ) :=
struct_perm.mul_action_support_condition

@[simp] lemma smul_to_condition (π : struct_perm α) (x : (atom ⊕ near_litter) × extended_index α) :
  π • to_condition x = to_condition ⟨derivative x.2 π • x.1, x.2⟩ := rfl

end struct_perm

variables (G : Type*) (α) {τ : Type*} [has_smul G (support_condition α)] [has_smul G τ]

/-- A *support for `x`* is a potential support that supports `x`. -/
structure support (x : τ) :=
(carrier : set (support_condition α))
(supports : supports G carrier x)

/-- A potential support is a small set of support conditions. -/
structure small_support (x : τ) extends support α G x :=
(small : small carrier)

/-- An element of `τ` is *supported* if it has some (not necessarily small) support. -/
def supported (x : τ) : Prop := nonempty $ support α G x

/-- An element of `τ` is *small-supported* if it has some small support. -/
def small_supported (x : τ) : Prop := nonempty $ small_support α G x

instance support.set_like (x : τ) : set_like (support α G x) (support_condition α) :=
{ coe := support.carrier,
  coe_injective' := λ s t h, by { cases s, cases t, congr' } }

instance small_support.set_like (x : τ) : set_like (small_support α G x) (support_condition α) :=
{ coe := λ s, s.carrier,
  coe_injective' := λ s t h, by { obtain ⟨⟨_, _⟩, _⟩ := s, obtain ⟨⟨_, _⟩, _⟩ := t, congr' } }

@[simp] lemma support.carrier_eq_coe {x : τ} {s : support α G x} : s.carrier = s := rfl
@[simp] lemma small_support.carrier_eq_coe {x : τ} {s : small_support α G x} : s.carrier = s := rfl

/-- There are at most `μ` small supports for a given `x : τ`. -/
lemma mk_small_support_le (x : τ) : #(small_support α G x) ≤ #μ :=
 begin
   have : small_support α G x ≃ {S : support α G x // small (S : set (support_condition α))},
   { refine ⟨λ S, ⟨S.1, S.2⟩, λ S, ⟨S.1, S.2⟩, _, _⟩; intro x; dsimp; cases x; simp },
   rw [cardinal.mk_congr this],
   unfold small,
   obtain ⟨e⟩ := cardinal.eq.1 (mk_support_condition α),
   transitivity #{S : support α G x // #S < (#μ).ord.cof},
   { exact cardinal.mk_subtype_mono (λ _, κ_le_μ_cof.trans_lt') },
   transitivity #{S : set (support_condition α) // #S < (#μ).ord.cof},
   { apply @cardinal.mk_le_of_injective _ _ (λ S : {T : support α G x // #T < (#μ).ord.cof},
      (⟨S.1.carrier, S.2⟩ : {S // #↥S < (#μ).ord.cof})),
    rintro ⟨⟨s₁, _⟩, h₁⟩ ⟨⟨s₂, _⟩, h₂⟩ h,
    simp only [subtype.coe_mk] at h,
    subst h },
  convert (mk_subset_mk_lt_cof μ_strong_limit.2).le using 1,
  have := mk_subtype_of_equiv (λ S, # ↥S < (#μ).ord.cof) (set.congr e),
  convert this using 1,
  have : ∀ S, # ↥S = # ↥(set.congr e S) := λ S, cardinal.eq.2 ⟨image _ _⟩,
  simp_rw this,
end

end con_nf
