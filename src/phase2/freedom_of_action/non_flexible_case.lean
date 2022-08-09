import phase2.freedom_of_action.constrains
import phase2.freedom_of_action.restriction
import phase2.freedom_of_action.values
import phase2.freedom_of_action.zorn

/-!
For a non-flexible litter `L = f_{γδ}^A(t)`, assume the designated support for `t` already lies in
`σ`. Then, look at `σ` restricted to `γ` - this is allowable by the restriction lemma, and by the
inductive freedom of action assumption extends to `π'`, a `γ`-allowable permutation. We can map `t`
using `π'` to find where `L` is supposed to be sent under `π`. We then add this result to `σ`.
-/

open quiver set sum with_bot

universe u

namespace con_nf
namespace allowable_partial_perm

variables [params.{u}]

open struct_perm spec

variables {α : Λ} [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [typed_positions.{}] [phase_2_assumptions α] {B : le_index α}

variables {B} {σ : allowable_partial_perm B} ⦃β : Λ⦄ ⦃γ : type_index⦄ ⦃δ : Λ⦄

/-- Since the designated support of `t` is included in `σ`, any allowable permutation `π'` that
satisfies `σ` at the lower level gives the same result for the image of `f_map_path hγ hδ t`.
This means that although `π` was chosen arbitrarily, its value is not important, and we could have
chosen any other permutation and arrived at the same value for the image of `f_map_path hγ hδ t`.

Don't prove this unless we need it - it sounds like an important mathematical point but potentially
not for the formalisation itself. -/
lemma non_flexible_union_unique (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
  (C : path (B : type_index) β)
  (t : tangle_path ((lt_index.mk' hγ (B.path.comp C)) : le_index α))
  (π : allowable_path (lt_index.mk' (coe_lt_coe.mpr hδ) (B.path.comp C) : le_index α))
  (hπ : π.to_struct_perm.satisfies $ σ.val.lower (C.cons $ coe_lt_coe.mpr hδ)) :
  ∀ (π' : allowable_path (lt_index.mk' (coe_lt_coe.mpr hδ) (B.path.comp C) : le_index α))
    (hπ' : π'.to_struct_perm.satisfies $ σ.val.lower (C.cons $ coe_lt_coe.mpr hδ)),
    struct_perm.derivative (path.nil.cons $ bot_lt_coe _) π.to_struct_perm •
      (f_map_path hγ hδ t).to_near_litter = struct_perm.derivative (path.nil.cons $ bot_lt_coe _)
        π.to_struct_perm • (f_map_path hγ hδ t).to_near_litter :=
sorry

private noncomputable def new_non_flexible_constraint (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
  {C : path (B : type_index) β}
  (t : tangle_path ((lt_index.mk' hγ (B.path.comp C)) : le_index α))
  {π : allowable_path (lt_index.mk' (coe_lt_coe.mpr hδ) (B.path.comp C) : le_index α)}
  (hπ : π.to_struct_perm.satisfies $ σ.val.lower (C.cons $ coe_lt_coe.mpr hδ)) :
    binary_condition B :=
  (inr ((f_map_path hγ hδ t).to_near_litter,
      struct_perm.derivative (path.nil.cons $ bot_lt_coe _)
        π.to_struct_perm • (f_map_path hγ hδ t).to_near_litter),
      (C.cons $ coe_lt_coe.mpr hδ).cons (bot_lt_coe _))

variables (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ) {C : path (B : type_index) β}
  (t : tangle_path ((lt_index.mk' hγ (B.path.comp C)) : le_index α))
  {π : allowable_path (lt_index.mk' (coe_lt_coe.mpr hδ) (B.path.comp C) : le_index α)}
  (hπ : π.to_struct_perm.satisfies $ σ.val.lower (C.cons $ coe_lt_coe.mpr hδ))

lemma non_flexible_union_one_to_one_forward :
  spec.one_to_one_forward (σ.val ⊔ {new_non_flexible_constraint hγ hδ hγδ t hπ}) :=
sorry

lemma non_flexible_union_one_to_one_backward :
  spec.one_to_one_forward (σ.val ⊔ {new_non_flexible_constraint hγ hδ hγδ t hπ})⁻¹ :=
sorry

lemma non_flexible_union_atom_cond_forward :
  ∀ L C, spec.atom_cond (σ.val ⊔ {new_non_flexible_constraint hγ hδ hγδ t hπ}) L C :=
sorry

lemma non_flexible_union_atom_cond_backward :
  ∀ L C, spec.atom_cond (σ.val ⊔ {new_non_flexible_constraint hγ hδ hγδ t hπ})⁻¹ L C :=
sorry

lemma non_flexible_union_near_litter_cond_forward :
  ∀ N₁ N₂ C, spec.near_litter_cond (σ.val ⊔ {new_non_flexible_constraint hγ hδ hγδ t hπ}) N₁ N₂ C :=
sorry

lemma non_flexible_union_near_litter_cond_backward :
  ∀ N₁ N₂ C,
    spec.near_litter_cond (σ.val ⊔ {new_non_flexible_constraint hγ hδ hγδ t hπ})⁻¹ N₁ N₂ C :=
sorry

lemma non_flexible_union_non_flexible_cond_forward :
  spec.non_flexible_cond B (σ.val ⊔ {new_non_flexible_constraint hγ hδ hγδ t hπ}) :=
begin
  intros hb hg hd hgb hdb hdg hNl hp ht hf π h1,
  unfold struct_perm.satisfies at h1,
  unfold struct_perm.satisfies_cond at h1,
  have h := h1 hf,
  dsimp at h,
  rw ← h,
  sorry
  -- exact unpack_coh_cond hgb hdb hdg hp ht π,
end

lemma non_flexible_union_non_flexible_cond_backward :
  spec.non_flexible_cond B (σ.val ⊔ {new_non_flexible_constraint hγ hδ hγδ t hπ})⁻¹ :=
sorry

lemma non_flexible_union_support_closed_forward :
  (σ.val ⊔ {new_non_flexible_constraint hγ hδ hγδ t hπ}).domain.support_closed B :=
begin
  unfold unary_spec.support_closed,
  simp,
  intros b d g hdb hgb hdg p t2 Nl h1 hPi hsup,
  --see hsup and goal; use similar construction to in restriction.lean.
  sorry,
end

lemma non_flexible_union_support_closed_backward :
  (σ.val ⊔ {new_non_flexible_constraint hγ hδ hγδ t hπ}).range.support_closed B :=
sorry

lemma non_flexible_union_flexible_cond :
  ∀ C, spec.flexible_cond B (σ.val ⊔ {new_non_flexible_constraint hγ hδ hγδ t hπ}) C :=
sorry

lemma non_flexible_union_allowable :
  spec.allowable B (σ.val ⊔ {new_non_flexible_constraint hγ hδ hγδ t hπ}) :=
{ forward :=
  { one_to_one := non_flexible_union_one_to_one_forward hγ hδ hγδ t hπ,
    atom_cond := non_flexible_union_atom_cond_forward hγ hδ hγδ t hπ,
    near_litter_cond := non_flexible_union_near_litter_cond_forward hγ hδ hγδ t hπ,
    non_flexible_cond := non_flexible_union_non_flexible_cond_forward hγ hδ hγδ t hπ,
    support_closed := non_flexible_union_support_closed_forward hγ hδ hγδ t hπ },
  backward :=
  { one_to_one := non_flexible_union_one_to_one_backward hγ hδ hγδ t hπ,
    atom_cond := non_flexible_union_atom_cond_backward hγ hδ hγδ t hπ,
    near_litter_cond := non_flexible_union_near_litter_cond_backward hγ hδ hγδ t hπ,
    non_flexible_cond := non_flexible_union_non_flexible_cond_backward hγ hδ hγδ t hπ,
    support_closed := by { rw spec.domain_inv,
      exact non_flexible_union_support_closed_backward hγ hδ hγδ t hπ } },
  flexible_cond := non_flexible_union_flexible_cond hγ hδ hγδ t hπ }

lemma le_non_flexible_union : σ ≤ ⟨_, non_flexible_union_allowable hγ hδ hγδ t hπ⟩ :=
{ le := le_sup_left,
  all_flex_domain := begin
    rintro L N' C' hN' hσ₁ (hσ₂ | hσ₂),
    { cases hσ₁ hσ₂ },
    { simp only [new_non_flexible_constraint, set_like.mem_coe, spec.mem_singleton,
        prod.mk.inj_iff] at hσ₂,
      exfalso,
      cases hN' hγ hδ hγδ C t,
      { exact h (litter.to_near_litter_injective hσ₂.left.left) },
      { exact h hσ₂.right } }
  end,
  all_flex_range := begin
    rintro L N' C' hN' hσ₁ (hσ₂ | hσ₂),
    { cases hσ₁ hσ₂ },
    { simp only [new_non_flexible_constraint, set_like.mem_coe, spec.mem_singleton,
        prod.mk.inj_iff] at hσ₂,
      exfalso,
      cases hN' hγ hδ hγδ C t,
      { -- This is the unpacked coherence condition on L and f.
        -- We need to change C and t to be the correct parameters here.
        sorry },
      { exact h hσ₂.right } }
  end,
  all_atoms_domain := begin
    rintro a b L ha C hσ₁ (hσ₂ | hσ₂),
    { cases hσ₁ hσ₂ },
    { simpa only [new_non_flexible_constraint, set_like.mem_coe, spec.mem_singleton,
        prod.mk.inj_iff, false_and] using hσ₂ }
  end,
  all_atoms_range := begin
    rintro a b L ha C hσ₁ (hσ₂ | hσ₂),
    { cases hσ₁ hσ₂ },
    { simpa only [new_non_flexible_constraint, set_like.mem_coe, spec.mem_singleton,
        prod.mk.inj_iff, false_and] using hσ₂ }
  end }

lemma exists_ge_non_flexible (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ) {C : path (B : type_index) β}
  (t : tangle_path ((lt_index.mk' hγ (B.path.comp C)) : le_index α))
  (hσ : ∀ c, c ≺ (inr (f_map_path hγ hδ t).to_near_litter,
    (C.cons $ coe_lt_coe.mpr hδ).cons (bot_lt_coe _)) →
    c ∈ σ.val.domain)
  (foa : ∀ (B : lt_index α), freedom_of_action (B : le_index α)) :
  ∃ ρ ≥ σ, (inr (f_map_path hγ hδ t).to_near_litter,
    (C.cons $ coe_lt_coe.mpr hδ).cons (bot_lt_coe _)) ∈
    ρ.val.domain :=
begin
  have hS : ∀ (c : support_condition γ), c ∈ (designated_support_path t).carrier →
    (c.fst, (C.cons hγ).comp c.snd) ∈ σ.val.domain :=
  λ (c : support_condition γ) (hc : c ∈ (designated_support_path t).carrier),
    hσ ⟨c.fst, path.comp (path.cons C hγ) c.snd⟩ (constrains.f_map hγ hδ hγδ C t c hc),
  have := σ.2.lower (C.cons $ coe_lt_coe.2 hδ) ((coe_lt_coe.2 hδ).trans_le (le_of_path C)),
  obtain ⟨π, hπ⟩ := foa (lt_index.mk' (coe_lt_coe.mpr hδ) (B.path.comp C))
    ⟨σ.val.lower (C.cons $ coe_lt_coe.mpr hδ), this⟩,
  have := struct_perm.derivative (path.nil.cons $ bot_lt_coe _) π.to_struct_perm
     • (f_map_path hγ hδ t).to_near_litter,
  refine ⟨_, le_non_flexible_union hγ hδ hγδ t hπ, _⟩,
  rw spec.domain_sup,
  right, simpa only [spec.domain, image_singleton, mem_singleton_iff],
end

end allowable_partial_perm
end con_nf
