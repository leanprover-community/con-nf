import mathlib.support
import phase0.struct_perm

/-!
# Supports
-/

open cardinal equiv
open_locale cardinal

noncomputable theory

universe u

namespace con_nf
variables [params.{u}] {α : type_index}

/-- A support condition is an atom or a near-litter together with an extended type index. -/
@[derive [inhabited]]
def support_condition (α : type_index) : Type u := (atom ⊕ near_litter) × extended_index α

/-- There are `μ` support conditions. -/
@[simp] lemma mk_support_condition (α : type_index) : #(support_condition α) = #μ :=
begin
  simp only [support_condition, mk_prod, mk_sum, mk_atom, lift_id, mk_near_litter],
  rw add_eq_left (κ_regular.aleph_0_le.trans κ_le_μ) le_rfl,
  exact mul_eq_left (κ_regular.aleph_0_le.trans κ_le_μ)
    (le_trans (mk_extended_index α) $ le_of_lt $ lt_trans Λ_lt_κ κ_lt_μ) (mk_ne_zero _),
end

instance struct_perm.mul_action : mul_action (struct_perm α) (support_condition α) :=
{ smul := λ π c, ⟨struct_perm.derivative c.snd π • c.fst, c.snd⟩,
  one_smul := by { rintro ⟨atoms | Ns, A⟩; unfold has_smul.smul; simp },
  mul_smul := begin
    rintro π₁ π₂ ⟨atoms | Ns, A⟩; unfold has_smul.smul;
    rw struct_perm.derivative_mul; dsimp; rw mul_smul,
  end }

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

/-- There are `μ` supports for a given `x : τ`. -/
@[simp] lemma mk_potential_support (x : τ) : #(support α G x) = #μ := sorry
-- begin
--   have : potential_support α ≃ {S : set (support_condition α) // small S},
--   { refine ⟨λ s, ⟨s.carrier, s.small⟩, λ s, ⟨s.val, s.property⟩, _, _⟩; intro x; cases x; simp },
--   obtain ⟨e⟩ := cardinal.eq.1 (mk_support_condition α),
--   refine le_antisymm _ ⟨⟨λ m, ⟨{e.symm m}, by simp⟩, λ a b h, by { simp at h, exact h }⟩⟩,
--   have lt_cof_eq_μ : #{S : set (support_condition α) // #S < (#μ).ord.cof} = #μ,
--   { convert mk_subset_mk_lt_cof μ_strong_limit.2 using 1,
--     have := mk_subtype_of_equiv (λ S, # ↥S < (#μ).ord.cof) (set.congr e),
--     convert this using 1,
--     suffices : ∀ S, # ↥S = # ↥(set.congr e S), { simp_rw this },
--     intro S, rw cardinal.eq, exact ⟨image _ _⟩ },
--   rw [mk_congr this, ←lt_cof_eq_μ],
--   exact cardinal.mk_subtype_mono (λ S (h : _ < _), h.trans_le κ_le_μ_cof),
-- end

/-- There are at most `μ` small supports for a given `x : τ`. -/
@[simp] lemma mk_support_le (x : τ) : #(small_support α G x) ≤ #μ :=
 begin
   have : small_support α G x ≃ {S : support α G x // small (S : set (support_condition α))},
   { refine ⟨λ S, ⟨S.1, S.2⟩, λ S, ⟨S.1, S.2⟩, _, _⟩; intro x; dsimp; cases x; simp },
   rw [cardinal.mk_congr this],-- ←mk_potential_support α],
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
