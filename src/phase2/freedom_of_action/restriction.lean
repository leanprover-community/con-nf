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
  refine spec.atom_cond.small_out _ _,
  { convert hL using 1,
    refine iff.to_eq _,
    simp_rw mem_domain,
    split; rintro ⟨⟨_ | ⟨x, y⟩, C⟩, hbin,  ⟨⟩⟩,
    { exact ⟨_, hbin, rfl⟩ },
    { exact ⟨(inr (L.to_near_litter, y), C), hbin, rfl⟩ } },
  swap,
  refine spec.atom_cond.small_in N hL _ hmaps,
  all_goals { convert hsmall, sorry },
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
  intros b d g hgb hdb hdg p t,
  have h1 := hf hgb hdb hdg (A.comp p),
  --wants to be t next, but will need to apply a conversion lemma to make lean see path_assoc.,
  sorry,
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

/-lemma unpack_coh_cond ⦃β : Λ⦄
  ⦃γ : type_index⦄
  ⦃δ : Λ⦄
  (hγβ : γ < ↑β)
  (hδβ : δ < β)
  (hδγ : γ ≠ ↑δ)
  (p : path ↑B ↑β)
  (t : tangle_path ↑(lt_index.mk' hγβ (B.path.comp p)))
  (π : allowable_path B) :
    derivative ((p.cons $ coe_lt_coe.mpr hδβ).cons (bot_lt_coe _)) π.to_struct_perm •
    (f_map_path hγβ hδβ t).to_near_litter =
    (f_map_path hγβ hδβ $ (π.derivative_comp B p).derivative hγβ
    {index := ↑β, path := B.path.comp p} • t).to_near_litter :=
begin
   sorry,
end-/

/-(allowable_derivative_comm : Π (A : le_index α) {γ : type_index} (hγ : γ < A.index)
  (π : allowable A.index),
  (allowable_derivative A hγ π).to_struct_perm =
    struct_perm.derivative (path.cons path.nil hγ) π.to_struct_perm)-/

lemma lower_non_flexible_cond (hσ : σ.allowable B) :
  (σ.lower A).non_flexible_cond (le_index.mk β (B.path.comp A)) :=
begin
  unfold spec.non_flexible_cond,
  intros b g d hgb hdb hgd Nl p t h1 π' h2,

  unfold struct_perm.satisfies at h2,
  unfold struct_perm.satisfies_cond at h2,
  have h := h2 h1,
  simp at h,
  rw ← h,

  --repeat unpacked_coherence lemma,
  --ok, I prove directly, but will refactor into a lemma later.

  --this works nicely
  have hc := smul_f_map_path ((B.path.comp A).comp p) hgb hdb hgd
  (π'.derivative_comp {index := β, path := B.path.comp A} p) t,
  rw ← hc,

  --this part in progress; am trying to work out the difference between
  --allowable and allowable_path, and if it matters

  have g1 := allowable_path.smul_to_struct_perm π' (f_map_path hgb hdb t),
  --I now need associativity of the action and 'to_near_litter' to make progress

  have := phase_2_assumptions.allowable_derivative_comm
  ({index := β, path := (B.path.comp A)}) _ π'; sorry,
end

/--
This proof is painful because we need to show in many places that path composition is associative.
Does anyone have any better ideas for how to complete this proof?
-/
lemma lower_domain_closed (hσ : σ.allowable B) :
  (σ.lower A).domain.support_closed (le_index.mk β (B.path.comp A)) :=
begin
  intros β' γ' δ' hγ' hδ' hγδ' C t ht π hsup,
  convert hσ.forward.support_closed hγ' hδ' hγδ' (A.comp C) (cast _ t) _ (cast _ π) (cast _ hsup)
    using 1; dsimp only,
  { rw quiver.path.comp_assoc, },
  { congr' 1,
    { rw quiver.path.comp_assoc, },
    { sorry, },
    { sorry, },
    { sorry, },
    { sorry, } },
  { rw ← cast_eq_iff_heq, },
  { rw quiver.path.comp_assoc, },
  { sorry },
  { rw quiver.path.comp_assoc, },
  { refine pi_congr _, intro c, sorry },
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
