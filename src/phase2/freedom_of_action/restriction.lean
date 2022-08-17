import phase2.freedom_of_action.allowable

/-!
# Restriction lemma

We prove the restriction lemma: if `σ` is a partial allowable permutation, then so is `σ`
restricted to a lower path `A`. The proof should be mostly straightforward. The non-trivial bit is
the "co-large or all" on flexible litters: in a proper restriction, `μ`-many non-flexible litters
get freed up and become flexible, so if it was “all”, it becomes "co-large".
-/

noncomputable theory

open cardinal quiver set sum
open_locale cardinal

universe u

namespace con_nf
variables [params.{u}]

open struct_perm spec

variables {α : Λ} [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [typed_positions.{}] [phase_2_assumptions α] {B : le_index α}

section lower
variables {σ : spec B} {β : Λ} (A : path (B : type_index) β) (hβ : (β : type_index) < B)

lemma lower_one_to_one_forward (hσ : σ.allowable B) : (σ.lower A).one_to_one_forward :=
spec.lower_one_to_one _ _ hσ.forward.one_to_one

lemma lower_atom_cond (hσ : σ.allowable B) (L C) : (σ.lower A).atom_cond L C :=
begin
  obtain ⟨N, atom_map, h1, h2, h3⟩ | ⟨hL, hsmall⟩ | ⟨N, hL, hsmall, hmaps⟩ :=
    hσ.forward.atom_cond L (A.comp C),
  { exact spec.atom_cond.all N atom_map h1 h2 h3 },
  exact spec.atom_cond.small_out hL hsmall,
  exact spec.atom_cond.small_in N hL hsmall hmaps,
end

lemma lower_near_litter_cond (hσ : σ.allowable B) (N₁ N₂ C) :
  (σ.lower A).near_litter_cond N₁ N₂ C :=
hσ.forward.near_litter_cond _ _ _

lemma flexible.of_comp (C : extended_index (⟨β, B.path.comp A⟩ : le_index α)) {L : litter} :
  flexible L (A.comp C) → flexible L C :=
begin
  intro hf,
  unfold flexible at hf ⊢,
  simp at hf ⊢,
  intros β γ δ hγ hδ hγδ D hC t,
  have h := hf hγ hδ hγδ (A.comp D) _ (t.lt_index_assoc),
  rwa f_map_path_assoc at h,
  rw hC, rw path.comp_cons, refl,
end

/-- Descending down a proper path `A`, `μ`-many litters become flexible. -/
--make C a parameter?
lemma lower_flexible_co_large (hβ : (B : type_index) ≠ β) :
  #{L : litter // ∃ (C : extended_index (⟨β, B.path.comp A⟩ : le_index α)),
    flexible L C ∧ ¬ flexible L (A.comp C)} = #μ :=
begin
  refine le_antisymm _ _,
  { rw ← mk_litter, exact mk_subtype_le _ },
  sorry
end

lemma lower_flexible_cond (hσ : σ.allowable B) (C : extended_index β) :
  (σ.lower A).flexible_cond (le_index.mk β (B.path.comp A)) C :=
begin
  by_cases hβ : (B : type_index) = β,
  { obtain ⟨B_index, B⟩ := B,
    dsimp at *,
    subst hβ,
    rw [path_eq_nil A, spec.lower_nil σ],
    rw path.comp_nil,
    exact hσ.flexible_cond C },

  -- The existing proof has been modified and simplified into the following structure.

  obtain ⟨hdom, hrge⟩ | ⟨hdom, hrge⟩ := hσ.flexible_cond (A.comp C),
  { refine spec.flexible_cond.co_large _ _,
    { refine le_antisymm _ _,
      { rw hdom, refine mk_subtype_mono _,
        -- This should be an approachable goal, solvable with `flexible.of_comp`.
        sorry },
      { rw ← mk_litter, exact mk_subtype_le _ } },
    { -- Same thing here.
      sorry },
  },
  { refine spec.flexible_cond.co_large _ _,
    -- Why are these goals true?
    -- We shouldn't try to solve these without a firm understanding of the mathematical proof.
    -- It's possible the definition is not quite correct.
    sorry, sorry },

  /- { refine spec.flexible_cond.all _ _,
    { intros L hf,
      have hdom' := hdom L _,
      { unfold spec.lower,
        unfold binary_condition.extend_path,
        unfold spec.domain at hdom' ⊢,
        dsimp at hdom' ⊢,
        obtain ⟨x, hx_1, hx_2⟩ := hdom',
        refine ⟨⟨x.fst, C⟩,_,_⟩,
        { obtain ⟨atoms | Ns, he'⟩ := x,
          { unfold binary_condition.domain at hx_2,
            simp at hx_2,
            exfalso,
            exact hx_2  },
          { unfold binary_condition.domain at hx_2,
            simp at hx_2 ⊢,
            obtain ⟨hx_2,hx_3⟩ := hx_2,
            rw hx_3 at hx_1,
            exact hx_1 } },
        { unfold binary_condition.domain at hx_2 ⊢,
          simp at hx_2 ⊢,
          exact and.elim_left hx_2 } },
      {
        sorry
        -- exact flexible.of_comp _ _ _ L hf,
      } },
    { intros L hf,
      have hrge' := hrge L _,
      { unfold spec.lower,
        unfold binary_condition.extend_path,
        unfold spec.range at hrge' ⊢,
        dsimp at hrge' ⊢,
        obtain ⟨x, hx_1, hx_2⟩ := hrge',
        refine ⟨⟨x.fst, C⟩,_,_⟩,
        { obtain ⟨atoms | Ns, he'⟩ := x,
          { unfold binary_condition.range at hx_2,
            simp at hx_2,
            exfalso,
            exact hx_2 },
          { unfold binary_condition.range at hx_2,
            simp at hx_2 ⊢,
            obtain ⟨hx_2,hx_3⟩ := hx_2,
            rw hx_3 at hx_1,
            exact hx_1 } },
        { unfold binary_condition.range at hx_2 ⊢,
          simp at hx_2 ⊢,
          obtain ⟨hx_2,hx_3⟩ := hx_2,
          exact hx_2 } },
      {
        sorry
        -- exact flexible.of_comp _ _ _ L hf,
      } } }, -/
end

lemma lower_non_flexible_cond (hσ : σ.allowable B) :
  (σ.lower A).non_flexible_cond (le_index.mk β (B.path.comp A)) :=
begin
  unfold spec.non_flexible_cond,
  intros β' γ δ hγ hδ hγδ N C t hf π hπ,
  unfold struct_perm.satisfies struct_perm.satisfies_cond at hπ,
  have h := hπ hf,
  dsimp only [sum.elim_inr] at h,
  rw ← h,
  rw ← smul_f_map_path ((B.path.comp A).comp C) hγ hδ hγδ _ t,
  convert near_litter_perm.smul_to_near_litter_eq _ _ using 1,
  unfold to_near_litter_perm,
  simp only [lower_self, monoid_hom.comp_id, allowable_path.to_struct_perm_derivative_comp,
    mul_equiv.coe_to_monoid_hom, coe_to_bot_iso_symm, of_bot_smul],
  rw [← allowable_path.to_struct_perm_derivative_comp, allowable_path.smul_to_struct_perm,
    allowable_path.derivative_comp, allowable_path.derivative_comp,
    allowable_path.smul_derivative_bot],
end

lemma lower_domain_closed (hσ : σ.allowable B) :
  (σ.lower A).domain.support_closed (le_index.mk β (B.path.comp A)) :=
begin
  intros β' γ' δ' hγ' hδ' hγδ' C t ht π hsup,
  have := hσ.forward.support_closed hγ' hδ' hγδ' (A.comp C)
    (t.lt_index_assoc) _ (π.lt_index_assoc) _,
  rwa allowable_path.lt_index_assoc_smul at this,
  rwa f_map_path_assoc,
  rintros c hc,
  have := @hsup c _,
  { rwa allowable_path.lt_index_assoc_smul_support_condition, },
  { rwa [unary_spec.lower, set.mem_set_of, ← path.comp_cons, support_condition.extend_path,
      path.comp_assoc] at hc, }
end

namespace spec

protected lemma allowable.lower (hσ : σ.allowable B) ⦃β : Λ⦄ (A : path (B : type_index) β)
  (hβ : (β : type_index) < B) :
  (σ.lower A).allowable (le_index.mk β (B.path.comp A)) :=
{ forward :=
  { one_to_one := lower_one_to_one_forward A hσ,
    atom_cond := lower_atom_cond A hσ,
    near_litter_cond := lower_near_litter_cond A hσ,
    non_flexible_cond := lower_non_flexible_cond A hσ,
    support_closed := lower_domain_closed A hσ },
  backward :=
  { one_to_one := by { rw ←lower_inv, exact lower_one_to_one_forward A hσ.inv },
    atom_cond := by { rw ←lower_inv, exact lower_atom_cond A hσ.inv },
    near_litter_cond := by { rw ←lower_inv, exact lower_near_litter_cond A hσ.inv },
    non_flexible_cond := by { rw ←lower_inv, exact lower_non_flexible_cond A hσ.inv },
    support_closed := by { rw ←lower_inv, exact lower_domain_closed A hσ.inv } },
  flexible_cond := lower_flexible_cond A hσ }

end spec
end lower
end con_nf
