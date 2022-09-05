import phase2.freedom_of_action.constrains
import phase2.freedom_of_action.values
import phase2.freedom_of_action.zorn

/-!
# Maximality proof: Near-litter case

Suppose that for a near-litter, its associated litter is already defined in `σ`, along with all of
the atoms in the symmetric difference with that litter. Then, the place the litter is supposed to
map to is already defined, and we simply add that to `σ`.
-/

open cardinal set sum
open_locale cardinal

universe u

namespace con_nf
namespace allowable_spec

variables [params.{u}]

open struct_perm spec

variables {α : Λ} [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [typed_positions.{}] [phase_2_assumptions α] {B : le_index α}

variables (σ : allowable_spec B) (N : near_litter) (A : extended_index B)

private noncomputable def near_litter_image (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain) :
    near_litter :=
  ⟨(near_litter_value σ A N.fst.to_near_litter hNL).fst,
    (near_litter_value σ A N.fst.to_near_litter hNL).snd.val ∆
      range (λ (a : {a // a ∈ litter_set N.fst ∆ ↑(N.snd)}),
        atom_value σ A a (ha a a.property)),
    begin
      rw [is_near_litter, is_near, small, ← symm_diff_assoc],
      exact (mk_union_le _ _).trans_lt
        (add_lt_of_lt κ_regular.aleph_0_le
          (lt_of_le_of_lt (mk_le_mk_of_subset $ diff_subset _ _)
            (near_litter_value σ A N.fst.to_near_litter hNL).snd.property)
          (lt_of_le_of_lt (mk_le_mk_of_subset $ diff_subset _ _)
            (lt_of_le_of_lt mk_range_le N.snd.property))),
    end⟩

/-- The `near_litter_image` of a near-litter behaves like it should under `σ`. -/
lemma near_litter_image_atom_spec (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain)
  (a b : atom) (h : (inl (a, b), A) ∈ σ.val) :
  b ∈ (near_litter_image σ N A hN hNL ha).2.val ↔ a ∈ N.snd.val :=
begin
  split,
  { rintro (⟨h₁, h₂⟩ | ⟨⟨c, hc⟩, hb⟩),
    { rw mem_value_iff_value_mem (inl_mem_range h) at h₁,
      rw atom_value_eq_of_mem_inv h at h₁,
      contrapose! h₂,
      refine ⟨⟨a, or.inl ⟨h₁, h₂⟩⟩, _⟩,
      dsimp only,
      rw atom_value_eq_of_mem,
      exact h, },
    { dsimp only at hc,
      rw ← atom_value_eq_of_mem h at hc,
      cases atom_value_injective hc,
      contrapose! hb,
      rw mem_value_iff_value_mem (inl_mem_range h),
      rw atom_value_eq_of_mem_inv h,
      cases c.property with hcp hcp,
      { exact hcp.1, },
      { cases hb hcp.1, } } },
  { intro ha,
    by_cases haN : a ∈ litter_set N.fst,
    { left, split,
      { rw mem_value_iff_value_mem (inl_mem_range h),
        rw atom_value_eq_of_mem_inv h,
      exact haN, },
      { rintro ⟨c, hc⟩,
        rw ← atom_value_eq_of_mem h at hc,
        cases atom_value_injective hc,
        cases c.property with hcp hcp,
        { exact hcp.2 ha, },
        { exact hcp.2 haN, }, } },
    { right,
      refine ⟨⟨⟨a, or.inr ⟨ha, haN⟩⟩, atom_value_eq_of_mem h⟩, _⟩,
      rw mem_value_iff_value_mem (inl_mem_range h),
      rw atom_value_eq_of_mem_inv h,
      exact haN, } }
end

lemma near_litter_image_spec (hNin : (inr N, A) ∈ σ.val.domain)
  (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain) :
  (inr (N, near_litter_image σ N A hN hNL ha), A) ∈ σ.val :=
begin
  unfold near_litter_image,
  rw mem_domain at hNin hNL,
  obtain ⟨⟨_ | ⟨N, N'⟩, C⟩, hNN', ⟨⟩⟩ := hNin,
  obtain ⟨⟨_ | ⟨L, M⟩, A⟩, hL, ⟨⟩⟩ := hNL,
  obtain ⟨M', hM, symm, hsy, hsd⟩ := σ.prop.forward.near_litter_cond N N' A hNN',
  have := (σ.prop.backward.one_to_one A).near_litter _ hL hM,
  subst this,
  have : ∀ a, symm a = atom_value σ A a (inl_mem_domain (hsy a))
    := λ b, (σ.prop.backward.one_to_one A).atom _ (hsy b)
      (atom_value_spec σ A b (inl_mem_domain (hsy b))),
  have that := congr_arg range (funext this).symm,
  convert hNN',
  obtain ⟨N', atoms, hN'⟩ := N',
  dsimp only at hsd, subst hsd,
  have key : near_litter_value σ A N.fst.to_near_litter (inr_mem_domain hL) = M :=
    (σ.prop.backward.one_to_one A).near_litter _
      (near_litter_value_spec σ A N.fst.to_near_litter (inr_mem_domain hL)) hL,
  have : (near_litter_value σ A N.fst.to_near_litter (inr_mem_domain hL)).fst = N',
  { rw key,
    refine is_near_litter.unique M.2.2 _,
    unfold is_near_litter is_near small at hN' ⊢,
    rw ← symm_diff_assoc at hN',
    have : ∀ (S T : set atom), # (S ∆ T : set atom) ≤ # (S ∪ T : set atom),
    { unfold symm_diff,
      intros S T,
      refine cardinal.mk_le_mk_of_subset _,
      simp only [sup_eq_union, union_subset_iff],
      exact ⟨λ x hx, or.inl hx.1, λ x hx, or.inr hx.1⟩ },
    specialize this (litter_set N' ∆ M.snd.val ∆ range symm) (range symm),
    rw [symm_diff_assoc, symm_diff_self, symm_diff_bot] at this,
    exact (this.trans $ cardinal.mk_union_le _ _).trans_lt (cardinal.add_lt_of_lt
      κ_regular.aleph_0_le hN' $ cardinal.mk_range_le.trans_lt N.2.2) },
  subst this,
  exact sigma.mk.inj_iff.2 ⟨rfl, heq_of_eq $ subtype.mk_eq_mk.2 $
    congr_arg2 _ (by { rw ←key, refl }) that⟩
end

lemma near_litter_image_spec_reverse (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain)
  (P : near_litter)
  (hP : (inr (P, near_litter_image σ N A hN hNL ha), A) ∈ σ.val) :
    P = N :=
begin
  -- I'm pretty certain this has to be true but can't find any easy way to prove it.
  sorry
end

noncomputable def new_near_litter_cond
  (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain) : spec B :=
{(inr (N, near_litter_image σ N A hN hNL ha), A)}

@[simp] lemma mem_new_near_litter_cond_iff
  (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain)
  (c : binary_condition B) :
  c ∈ σ.val ⊔ new_near_litter_cond σ N A hN hNL ha ↔
    c ∈ σ.val ∨ c = (inr (N, near_litter_image σ N A hN hNL ha), A) :=
by simp only [new_near_litter_cond, mem_sup, mem_mk, spec.mem_singleton]

@[simp] lemma mem_new_near_litter_cond_inv_iff
  (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain)
  (c : binary_condition B) :
  c ∈ (σ.val ⊔ new_near_litter_cond σ N A hN hNL ha)⁻¹ ↔
    c ∈ σ.val⁻¹ ∨ c = (inr (near_litter_image σ N A hN hNL ha, N), A) :=
begin
  simp only [new_near_litter_cond, subtype.val_eq_coe, spec.mem_inv, mem_sup,
    mem_mk, mem_singleton_iff],
  rw [spec.mem_singleton, inv_eq_iff_inv_eq, binary_condition.inv_def, binary_condition.inv_def,
    sum.map_inr, prod.swap],
  exact ⟨λ h, or.elim h or.inl (λ h, or.inr h.symm), λ h, or.elim h or.inl (λ h, or.inr h.symm)⟩,
end

lemma near_litter_union_one_to_one_forward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain) :
  spec.one_to_one_forward (σ.val ⊔ new_near_litter_cond σ N A hN hNL ha) :=
begin
  refine λ C, ⟨λ a b hb c hc, _, λ M P hP Q hQ, _⟩,
  { rw [mem_set_of, mem_new_near_litter_cond_iff] at hb hc,
    simp only [subtype.val_eq_coe, prod.mk.inj_iff, false_and, or_false] at hb hc,
    exact (σ.prop.forward.one_to_one C).atom a hb hc },
  { simp only [new_near_litter_cond, spec.mem_mk, subtype.val_eq_coe, mem_set_of_eq, mem_sup,
      mem_singleton_iff, prod.mk.inj_iff] at hP hQ,
    obtain hP | ⟨⟨rfl, rfl⟩, rfl⟩ := hP; obtain hQ | ⟨⟨rfl, h₂⟩, h₃⟩ := hQ,
    { exact (σ.property.forward.one_to_one C).near_litter M hP hQ },
    { exact near_litter_image_spec_reverse σ N A hN hNL ha P hP, },
    { exact (near_litter_image_spec_reverse σ N A hN hNL ha Q hQ).symm, },
    { refl }, }
end

lemma near_litter_union_one_to_one_backward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain) :
  spec.one_to_one_forward (σ.val ⊔ new_near_litter_cond σ N A hN hNL ha)⁻¹ :=
begin
  refine λ C, ⟨λ a b hb c hc, _, λ M P hP Q hQ, _⟩,
  { rw [mem_set_of, mem_new_near_litter_cond_inv_iff] at hb hc,
    simp only [mem_set_of, mem_new_near_litter_cond_inv_iff, subtype.val_eq_coe, inl_mem_inv,
      prod.swap_prod_mk, prod.mk.inj_iff, false_and, or_false] at hb hc,
    exact (σ.prop.backward.one_to_one C).atom a hb hc },
  { rw [mem_set_of, mem_new_near_litter_cond_inv_iff] at hP hQ,
    obtain hP | ⟨⟨rfl, rfl⟩, rfl⟩ := hP; obtain hQ | ⟨⟨rfl, h₂⟩, h₃⟩ := hQ,
    { exact (σ.property.backward.one_to_one C).near_litter M hP hQ },
    { exact ((σ.property.backward.one_to_one A).near_litter _
        (near_litter_image_spec σ N A (inr_mem_range hP) hN hNL ha) hP).symm, },
    { exact ((σ.property.backward.one_to_one A).near_litter _
        (near_litter_image_spec σ N A (inr_mem_range hQ) hN hNL ha) hQ), },
    { refl, }, }
end

lemma near_litter_union_atom_cond_forward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain) :
  ∀ L C, spec.atom_cond (σ.val ⊔ new_near_litter_cond σ N A hN hNL ha) L C :=
begin
  intros L C,
  obtain ⟨L', hL, atom_map, hin, himg⟩ | ⟨hL, hLsmall⟩ | ⟨L', hL, hLsmall, hmaps⟩ := σ.prop.forward.atom_cond L C,
  { exact spec.atom_cond.all L' (or.inl hL) atom_map (λ a H, or.inl $ hin a H) himg },
  refine spec.atom_cond.small_out _ _,
  { rw mem_domain,
    rintro ⟨⟨_ | ⟨N, M⟩, _⟩, hb, hdom⟩; cases hdom,
    refine or.rec (hL ∘ inr_mem_domain) (λ h, _) hb,
    cases mem_singleton_iff.1 h,
    simpa only using hN },
  swap,
  refine spec.atom_cond.small_in L' (or.inl hL) _
      (λ a b hab, or.rec (λ h, hmaps h) (λ h, by cases h) hab),
  all_goals { convert hLsmall using 1,
    refine ext (λ x, ⟨λ hx, ⟨hx.1, _⟩, λ hx, ⟨hx.1, _⟩⟩),
    { have := hx.2,
      rw mem_domain at this,
      obtain ⟨b, hb, hdom⟩ := this,
      rw mem_new_near_litter_cond_iff at hb,
      cases hb,
      { obtain ⟨as | Ns, C⟩ := b; cases hdom, convert inl_mem_domain hb, },
      { cases hb, cases hdom, } },
    { have := hx.2,
      rw mem_domain at this,
      obtain ⟨⟨as | Ns, C⟩, hb, hdom⟩ := this; cases hdom,
      exact or.inl (mem_domain_of_mem hb), } }
end

lemma near_litter_union_atom_cond_backward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain) :
  ∀ L C, spec.atom_cond (σ.val ⊔ new_near_litter_cond σ N A hN hNL ha)⁻¹ L C :=
begin
  intros L C,
  obtain ⟨L', hL, atom_map, hin, himg⟩ | ⟨hL, hLsmall⟩ | ⟨L', hL, hLsmall, hmaps⟩ := σ⁻¹.prop.forward.atom_cond L C,
  { exact spec.atom_cond.all L' (or.inl hL) atom_map (λ a H, or.inl $ hin a H) himg },
  { by_cases hLN : A = C ∧ L.to_near_litter = near_litter_image σ N A hN hNL ha,
    { refine spec.atom_cond.small_in N _ _ _,
      { rw mem_new_near_litter_cond_inv_iff, right, rw hLN.2, simp_rw hLN.1, },
      { convert hLsmall,
        ext a,
        simp_rw [spec.mem_domain, spec.mem_inv, mem_new_near_litter_cond_iff],
        split,
        { rintro ⟨⟨as | Ns, C⟩, hc₁, hc₂⟩; cases hc₂,
          cases hc₁,
          exact ⟨⟨inl as, C⟩, hc₁, hc₂⟩,
          cases hc₁, },
        { rintro ⟨c, hc₁, hc₂⟩,
          exact ⟨c, or.inl hc₁, hc₂⟩, } },
      { intros a b,
        rw mem_new_near_litter_cond_inv_iff,
        rintro (h | h),
        { cases hLN.1,
          rw ← near_litter_image_atom_spec σ N A hN hNL ha b a h,
          rw ← hLN.2,
          refl, },
        { cases h, } } },
    refine spec.atom_cond.small_out _ _,
    { rw mem_domain,
      rintro ⟨⟨_ | ⟨N, M⟩, _⟩, hb, hdom⟩; cases hdom,
      refine or.rec (λ h, hL (inr_mem_range h)) (λ h, _) hb,
      rw new_near_litter_cond at h,
      simp only [binary_condition.inv_def, map_inr, prod.swap_prod_mk, coe_singleton,
        mem_singleton_iff, prod.mk.inj_iff] at h,
      obtain ⟨⟨rfl, hLM : L.to_near_litter = near_litter_image σ M A hN hNL ha⟩, rfl⟩ := h,
      push_neg at hLN,
      exact hLN rfl hLM, },
    convert hLsmall using 1,
    refine ext (λ x, ⟨λ hx, ⟨hx.1, _⟩, λ hx, ⟨hx.1, _⟩⟩),
    { have := hx.2,
      rw mem_domain at this ⊢,
      obtain ⟨b, hb, hdom⟩ := this,
      refine ⟨b, or.rec id (λ h, _) hb, hdom⟩,
      obtain ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ := b;
      simp only [mem_singleton_iff, has_inv.inv, sum.elim_inl, sum.elim_inr] at h; cases h,
      cases hdom },
    { have := hx.2,
      rw mem_domain at this ⊢,
      obtain ⟨b, hb, hdom⟩ := this,
      refine ⟨b, or.inl hb, hdom⟩ } },
  { refine spec.atom_cond.small_in L' (or.inl hL) _
      (λ a b hab, or.rec (λ h, hmaps h) (λ h, by cases h) hab),
    convert hLsmall using 1,
    refine ext (λ x, ⟨λ hx, ⟨hx.1, _⟩, λ hx, ⟨hx.1, _⟩⟩),
    { have := hx.2,
      rw mem_domain at this ⊢,
      obtain ⟨b, hb, hdom⟩ := this,
      refine ⟨b, or.rec id (λ h, _) hb, hdom⟩,
      obtain ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ := b;
      simp only [mem_singleton_iff, has_inv.inv, sum.elim_inl, sum.elim_inr] at h; cases h,
      cases hdom },
    { have := hx.2,
      rw mem_domain at this ⊢,
      obtain ⟨b, hb, hdom⟩ := this,
      refine ⟨b, or.inl hb, hdom⟩ } }
end

lemma near_litter_union_near_litter_cond_forward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain) :
  ∀ N₁ N₂ C, spec.near_litter_cond
    (σ.val ⊔ new_near_litter_cond σ N A hN hNL ha) N₁ N₂ C :=
begin
  rintro N₁ N₂ C (h | h),
  { obtain ⟨M, hM₁, sd, hsd₁, hsd₂⟩ := σ.property.forward.near_litter_cond N₁ N₂ C h,
    exact ⟨M, or.inl hM₁, sd, λ a, or.inl (hsd₁ a), hsd₂⟩ },
  cases h,
  rw mem_domain at hNL,
  obtain ⟨⟨atoms | ⟨N₃, N₄⟩, C⟩, hc₁, hc₂⟩ := hNL; cases hc₂,
  refine ⟨N₄, or.inl hc₁, λ a, atom_value σ A a (ha a a.property), _, _⟩,
  { exact λ a, or.inl (atom_value_spec σ A a (ha a a.property)) },
  { suffices : near_litter_value σ A N.fst.to_near_litter (inr_mem_domain hc₁) = N₄,
    { convert rfl; rw ←this; refl },
    have := near_litter_value_spec σ A N.fst.to_near_litter (inr_mem_domain hc₁),
    exact (σ.property.backward.one_to_one A).near_litter N.fst.to_near_litter this hc₁ }
end

lemma near_litter_union_near_litter_cond_backward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain) :
  ∀ N₁ N₂ C, spec.near_litter_cond
    (σ.val ⊔ new_near_litter_cond σ N A hN hNL ha)⁻¹ N₁ N₂ C :=
begin
  rintro N₁ N₂ C (h | h),
  { obtain ⟨M, hM₁, sd, hsd₁, hsd₂⟩ := σ.property.backward.near_litter_cond N₁ N₂ C h,
    exact ⟨M, or.inl hM₁, sd, λ a, or.inl (hsd₁ a), hsd₂⟩ },
  sorry
end

lemma near_litter_union_non_flex_cond_forward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain) :
  spec.non_flex_cond B (σ.val ⊔ new_near_litter_cond σ N A hN hNL ha) :=
begin
  rintro β δ γ hγ hδ hγδ N₁ C t (ht | ht) ρ hρ,
  { exact σ.property.forward.non_flex_cond hγ hδ hγδ N₁ C t ht ρ
      (hρ.mono $ subset_union_left _ _) },
  cases ht, cases hN rfl,
end

lemma near_litter_union_non_flex_cond_backward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain) :
  spec.non_flex_cond B (σ.val ⊔ new_near_litter_cond σ N A hN hNL ha)⁻¹ :=
begin
  rintro β γ δ hγ hδ hγδ N₁ C t ht ρ hρ,
  rw mem_new_near_litter_cond_inv_iff at ht,
  cases ht,
  { exact σ.property.backward.non_flex_cond hγ hδ hγδ N₁ C t ht ρ
      (hρ.mono $ subset_union_left _ _) },
  simp only [prod.mk.inj_iff] at ht,
  cases ht.1.2,
  have ht' := congr_arg sigma.fst ht.1.1,
  unfold litter.to_near_litter at ht',
  unfold near_litter_image at ht',
  dsimp only at ht',
  cases ht.2,
  have := @hρ (inr (σ.near_litter_value
    ((C.cons (with_bot.coe_lt_coe.mpr hδ)).cons (with_bot.bot_lt_coe _)) N.fst.to_near_litter hNL,
    N.fst.to_near_litter),
    ((quiver.path.nil : quiver.path (β : type_index) β).cons (with_bot.coe_lt_coe.mpr hδ)).cons (with_bot.bot_lt_coe _)) _,
  rw satisfies_cond_near_litters at this,
  have := (near_litter_perm.smul_fst _ _).symm.trans (congr_arg sigma.fst this),
  rw [← allowable_path.to_struct_perm_derivative_comp ⟨β, B.path.comp C⟩,
    allowable_path.derivative_comp, to_near_litter_perm_smul,
    allowable_path.smul_to_struct_perm] at this,
  rw [← smul_f_map_path _ _ _ hγδ, ht', ← allowable_path.smul_derivative_bot
    (ρ.derivative (with_bot.coe_lt_coe.mpr hδ)) (with_bot.bot_lt_coe δ)],
  exact this.symm,
  { have := near_litter_value_spec σ
      ((C.cons (with_bot.coe_lt_coe.mpr hδ)).cons (with_bot.bot_lt_coe _))
      N.fst.to_near_litter hNL,
    rw lower_inv,
    rw inr_mem_inv,
    exact or.inl this, },
end

lemma near_litter_union_support_closed_forward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain) :
  (σ.val ⊔ new_near_litter_cond σ N A hN hNL ha).domain.support_closed B :=
begin
  intros β δ γ hγ hδ hγδ C t ht,
  rw mem_domain at ht,
  obtain ⟨⟨_ | ⟨_, N'⟩, _⟩, hc₁, hc₂⟩ := ht; cases hc₂,
  rw mem_new_near_litter_cond_iff at hc₁,
  cases hc₁,
  { exact (σ.property.forward.support_closed hγ hδ hγδ C t (inr_mem_domain hc₁)).mono
      (subset_union_left _ _) },
  { cases hc₁,
    cases hN rfl, },
end

lemma near_litter_union_support_closed_backward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain) :
  (σ.val ⊔ new_near_litter_cond σ N A hN hNL ha).range.support_closed B :=
begin
  intros β δ γ hγ hδ hγδ C t ht,
  rw spec.mem_range at ht,
  obtain ⟨⟨_ | ⟨N', _⟩, _⟩, hc₁, hc₂⟩ := ht; cases hc₂,
  rw mem_new_near_litter_cond_iff at hc₁,
  cases hc₁,
  { exact (σ.property.backward.support_closed hγ hδ hγδ C t (inr_mem_range hc₁)).mono
      (subset_union_left _ _)  },
  { -- The definition of support-closed is probably talking about the wrong group of allowable
    -- permutations.
    sorry }
end

lemma near_litter_union_flex_cond (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain)
  (image_not_flex :
    ∀ L, litter_set L = (near_litter_image σ N A hN hNL ha).snd.val → ¬ flex L A) (C) :
  spec.flex_cond B (σ.val ⊔ new_near_litter_cond σ N A hN hNL ha) C :=
begin
  obtain (⟨hdom, hrge⟩ | ⟨hdom, hrge⟩) := σ.property.flex_cond C,
  { refine spec.flex_cond.co_large _ _,
    { convert hdom, ext L, split; rintro ⟨hC₁, hC₂⟩; refine ⟨hC₁, λ h, _⟩,
      { rw spec.domain_sup at hC₂, exact hC₂ (or.inl h) },
      { rw spec.domain_sup at h,
        cases h,
        { exact hC₂ h },
        { rw spec.mem_domain at h,
          obtain ⟨c, hc₁, hc₂⟩ := h,
          cases hc₁, cases hc₂,
          exact hN rfl } } },
    { convert hrge, ext L, split; rintro ⟨hC₁, hC₂⟩; refine ⟨hC₁, λ h, _⟩,
      { rw spec.range_sup at hC₂, exact hC₂ (or.inl h) },
      { rw spec.mem_range at h,
        obtain ⟨⟨_ | ⟨N₁, N₂⟩, D⟩, hc₁, hc₂⟩ := h; cases hc₂,
        rw mem_new_near_litter_cond_iff at hc₁,
        cases hc₁,
        { rw spec.mem_range at hC₂,
          exact hC₂ ⟨_, hc₁, rfl⟩, },
        simp only [prod.mk.inj_iff] at hc₁,
        cases hc₁.2,
        exact image_not_flex L (congr_arg (λ N : near_litter, N.2.val) hc₁.1.2) hC₁, } } },
  { refine spec.flex_cond.all (λ L hL, _) (λ L hL, _),
    { rw spec.domain_sup, exact or.inl (hdom L hL) },
    { rw spec.range_sup, exact or.inl (hrge L hL) } }
end

lemma near_litter_union_allowable (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain)
  (image_not_flex :
    ∀ L, litter_set L = (near_litter_image σ N A hN hNL ha).snd.val → ¬ flex L A) :
  spec.allowable B (σ.val ⊔ new_near_litter_cond σ N A hN hNL ha) :=
{ forward :=
  { one_to_one := near_litter_union_one_to_one_forward σ N A hN hNL ha,
    atom_cond := near_litter_union_atom_cond_forward σ N A hN hNL ha,
    near_litter_cond := near_litter_union_near_litter_cond_forward σ N A hN hNL ha,
    non_flex_cond := near_litter_union_non_flex_cond_forward σ N A hN hNL ha,
    support_closed := near_litter_union_support_closed_forward σ N A hN hNL ha },
  backward :=
  { one_to_one := near_litter_union_one_to_one_backward σ N A hN hNL ha,
    atom_cond := near_litter_union_atom_cond_backward σ N A hN hNL ha,
    near_litter_cond := near_litter_union_near_litter_cond_backward σ N A hN hNL ha,
    non_flex_cond := near_litter_union_non_flex_cond_backward σ N A hN hNL ha,
    support_closed := by { rw spec.domain_inv,
      exact near_litter_union_support_closed_backward σ N A hN hNL ha } },
  flex_cond := near_litter_union_flex_cond σ N A hN hNL ha image_not_flex }

/-- We take the additional hypothesis that the near-litter that we're mapping do does not happen
to be a flexible litter. This will always be true, but it is convenient to assume at this point. -/
lemma le_near_litter_union (hN : litter_set N.fst ≠ N.snd)
  (hNL : (inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (inl a, A) ∈ σ.val.domain)
  (image_not_flex :
    ∀ L, litter_set L = (near_litter_image σ N A hN hNL ha).snd.val → ¬ flex L A) :
  σ ≤ ⟨σ.val ⊔ new_near_litter_cond σ N A hN hNL ha,
    near_litter_union_allowable σ N A hN hNL ha image_not_flex⟩ := {
  le := subset_union_left _ _,
  all_flex_domain := begin
    rintro L N' C hN' hσ₁ (hσ₂ | hσ₂),
    { cases hσ₁ hσ₂ },
    { cases hσ₂, cases hN rfl }
  end,
  all_flex_range := begin
    rintro L N' C hN' hσ₁ (hσ₂ | hσ₂),
    { cases hσ₁ hσ₂ },
    { simp only [new_near_litter_cond, coe_singleton, mem_singleton_iff, prod.mk.inj_iff] at hσ₂,
      obtain ⟨⟨rfl, hσ₂⟩, rfl⟩ := hσ₂,
      cases image_not_flex L _ hN',
      rw ←hσ₂,
      refl }
  end,
  all_atoms_domain := begin
    intros b₁ b₂ L hb₁ C hC₁ hC₂ c hc',
    cases hC₂,
    { cases hC₁ hC₂ },
    { exfalso, simpa only [new_near_litter_cond, coe_singleton, mem_singleton_iff,
        prod.mk.inj_iff, false_and] using hC₂ },
  end,
  all_atoms_range := begin
    intros b₁ b₂ L hb₁ C hC₁ hC₂ c hc',
    cases hC₂,
    { cases hC₁ hC₂ },
    { exfalso, simpa only [new_near_litter_cond, coe_singleton, mem_singleton_iff,
        prod.mk.inj_iff, false_and] using hC₂ },
  end }

/-- If everything that constrains a near litter lies in `σ`, we can add the near litter to `σ`,
giving a new allowable partial permutation `ρ ≥ σ`. -/
lemma exists_ge_near_litter (hN : litter_set N.fst ≠ N.snd)
  (hσ : ∀ c, c ≺ (⟨inr N, A⟩ : support_condition B) → c ∈ σ.val.domain) :
  ∃ ρ ≥ σ, (⟨inr N, A⟩ : support_condition B) ∈ ρ.val.domain :=
begin
  have hNL := hσ (inr N.fst.to_near_litter, A) (constrains.near_litter N hN A),
  have ha := λ a ha, hσ (inl a, A) (constrains.symm_diff N a ha A),
  by_cases image_not_flex :
    ∀ L, litter_set L = (near_litter_image σ N A hN hNL ha).snd.val → ¬ flex L A,
  { refine ⟨_, le_near_litter_union σ N A hN hNL ha image_not_flex, _⟩,
    rw mem_domain,
    refine ⟨_, mem_union_right _ rfl, rfl⟩, },
  { -- Seek a contradiction (discuss this with Peter).
    push_neg at image_not_flex,
    obtain ⟨L, hL₁, hL₂⟩ := image_not_flex,
    sorry }
end

end allowable_spec
end con_nf
