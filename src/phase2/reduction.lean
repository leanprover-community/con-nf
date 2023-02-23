import phase2.flexible

/-!
# Reductions of supports
-/

universe u

open mul_action quiver set sum with_bot
open_locale cardinal

namespace con_nf
variables [params.{u}] (α : Λ) [position_data.{}] [phase_2_assumptions α]

variables (β : Λ) (G : Type*) {τ : Type*} [has_smul G (support_condition β)] [has_smul G τ]

variables {β G} {x : τ}

/-- A support condition is *reduced* if it is an atom or a litter. -/
@[mk_iff] inductive reduced {β : type_index} : support_condition β → Prop
| mk_atom (a : atom) (B : extended_index β) : reduced (inl a, B)
| mk_litter (L : litter) (B : extended_index β) : reduced (inr L.to_near_litter, B)

/-- The *reduction* of a set of support conditions is the downward closure of the set under
the constrains relation, but we only keep reduced conditions. -/
def reduction (S : set (support_condition β)) : set (support_condition β) :=
{c | ∃ d ∈ S, relation.refl_trans_gen (constrains α β) c d} ∩ set_of reduced

lemma reduction_singleton (c : support_condition β) :
  reduction α {c} = ({c} ∪ {d | relation.trans_gen (constrains α β) d c}) ∩ set_of reduced :=
by simp only [reduction, mem_singleton_iff, exists_prop, exists_eq_left,
  relation.refl_trans_gen_iff_eq_or_trans_gen, set_of_or, set_of_eq_eq_singleton']

lemma reduction_singleton_of_not_reduced (c : support_condition β) (hc : ¬reduced c) :
  reduction α {c} = {d | relation.trans_gen (constrains α β) d c} ∩ {d | reduced d} :=
begin
  simp only [reduction_singleton, inter_distrib_right, union_eq_right_iff_subset,
    subset_inter_iff, inter_subset_right, and_true],
  rintros d ⟨hd, hd'⟩,
  cases hd,
  cases hc hd',
end

lemma small_constrains (c : support_condition β) : small {d | d ≺[α] c} :=
begin
  obtain ⟨a | N, A⟩ := c,
  { simp only [constrains_atom, set_of_eq_eq_singleton, small_singleton], },
  simp_rw constrains_iff,
  refine small.union _ (small.union _ (small.union _ (small.union _ _)));
    rw small_set_of,
  { simp only [prod.mk.inj_iff, false_and, and_false,
      exists_false, set_of_false, small_empty], },
  { simp only [ne.def, prod.mk.inj_iff, exists_eq_right_right'],
    by_cases litter_set N.fst = N.snd,
    simp only [h, eq_self_iff_true, not_true, false_and, set_of_false, small_empty],
    simp only [h, not_false_iff, true_and, set_of_eq_eq_singleton, small_singleton], },
  { simp only [prod.mk.inj_iff, exists_eq_right_right'],
    have : small {c : support_condition β | ∃ a, a ∈ litter_set N.fst ∆ N.snd ∧ c = (inl a, A)},
    { refine lt_of_le_of_lt _ N.2.prop,
      refine ⟨⟨λ c, ⟨_, c.2.some_spec.1⟩, _⟩⟩,
      rintros ⟨c, hc⟩ ⟨d, hd⟩,
      simp only [subtype.val_eq_coe, subtype.mk_eq_mk],
      intro h,
      rw [hc.some_spec.2, hd.some_spec.2, h], },
    convert this using 1,
    ext ⟨a | N, A⟩ : 1,
    { simp only [mem_set_of_eq, prod.mk.inj_iff],
      split,
      { rintro ⟨_, a', h₁, h₂, rfl⟩,
        exact ⟨a', h₁, h₂⟩, },
      { rintro ⟨a', h₁, h₂⟩,
        exact ⟨N, a', h₁, h₂, rfl⟩, } },
    { simp only [mem_set_of_eq, prod.mk.inj_iff, false_and, and_false, exists_false], }, },
  { by_cases ∃ ⦃γ : Iic α⦄ ⦃δ : Iio α⦄ ⦃ε : Iio α⦄ (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ)
      (hδε : δ ≠ ε) (B : path (β : type_index) γ) (t : tangle δ),
      N = (f_map (coe_ne_coe.mpr $ coe_ne' hδε) t).to_near_litter ∧
      A = (B.cons (coe_lt hε)).cons (bot_lt_coe _),
    { obtain ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ := h,
      refine lt_of_le_of_lt _ (designated_support t).small,
      suffices : #{a : support_condition β | ∃ c : designated_support t,
        a = ⟨c.val.fst, (B.cons (coe_lt hδ)).comp c.val.snd⟩} ≤ #(designated_support t),
      { refine le_trans (cardinal.mk_subtype_le_of_subset _) this,
        rintros x ⟨_, _, _, _, _, _, _, _, c, hc, rfl, h⟩,
        simp only [prod.mk.inj_iff, litter.to_near_litter_injective.eq_iff, f_map] at h,
        cases subtype.coe_inj.mp (coe_inj.mp h.1.2.1),
        cases subtype.coe_inj.mp h.1.2.2,
        cases choose_wf_injective h.1.1,
        cases subtype.coe_inj.mp (coe_inj.mp
          (path.obj_eq_of_cons_eq_cons (path.heq_of_cons_eq_cons h.2).eq)),
        cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons h.2).eq).eq,
        exact ⟨⟨c, hc⟩, rfl⟩, },
      refine ⟨⟨λ a, a.prop.some, _⟩⟩,
      intros a b h,
      refine subtype.coe_inj.mp _,
      simp only [subtype.val_eq_coe] at h,
      rw [a.prop.some_spec, b.prop.some_spec],
      simp only [h, subtype.val_eq_coe], },
    { refine small_of_forall_not_mem _,
      rintro x ⟨γ, δ, ε, hδ, hε, hδε, B, t, c, hN, rfl, hA⟩,
      simp only [prod.mk.inj_iff] at hA,
      refine h ⟨γ, δ, ε, hδ, hε, hδε, B, t, hA⟩, }, },
  { refine subsingleton.small _,
    rintros ⟨c, C⟩ ⟨γ, ε, hε, C', a, hc₁, hc₂⟩ ⟨d, D⟩ ⟨γ, ε, hε, D', b, hd₁, hd₂⟩,
    simp only [prod.mk.inj_iff] at hc₁ hc₂ hd₁ hd₂,
    rw [hc₁.1, hc₁.2, hd₁.1, hd₁.2],
    rw [hc₂.1, hc₂.2, litter.to_near_litter_injective.eq_iff] at hd₂,
    cases subtype.coe_inj.mp (coe_inj.mp (path.obj_eq_of_cons_eq_cons hd₂.2)),
    cases subtype.coe_inj.mp (coe_inj.mp (path.obj_eq_of_cons_eq_cons
      (path.heq_of_cons_eq_cons hd₂.2).eq)),
    cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons hd₂.2).eq).eq,
    rw (f_map_injective bot_ne_coe).eq_iff at hd₂,
    cases hd₂.1,
    refl, },
end

def nth_reduction (S : set (support_condition β)) : ℕ → set (support_condition β)
| 0 := S
| (n + 1) := {c | ∃ d, d ∈ nth_reduction n ∧ c ≺[α] d}

lemma small_nth_reduction {S : set (support_condition β)} {n : ℕ} (h : small S) :
  small (nth_reduction α S n) :=
begin
  induction n with n hn,
  exact h,
  rw nth_reduction,
  simp_rw [← exists_prop, subtype.exists', set_of_exists],
  refine small_Union hn _,
  rintro ⟨c, hc⟩,
  exact small_constrains α c,
end

lemma mem_nth_reduction_iff {S : set (support_condition β)} {n : ℕ}
  {c : support_condition β} :
  c ∈ nth_reduction α S n ↔
  ∃ l, list.chain (constrains α β) c l ∧ l.length = n ∧ (c :: l).last (list.cons_ne_nil _ _) ∈ S :=
begin
  induction n with n hn generalizing c,
  { rw nth_reduction,
    split,
    { intro h,
      exact ⟨[], list.chain.nil, rfl, h⟩, },
    { rintro ⟨l, h₁, h₂, h₃⟩,
      rw list.length_eq_zero at h₂,
      cases h₂,
      exact h₃, }, },
  { simp only [nth_reduction, mem_set_of_eq],
    split,
    { rintro ⟨d, hd₁, hd₂⟩,
      obtain ⟨l, hl₁, hl₂, hl₃⟩ := hn.mp hd₁,
      refine ⟨d :: l, list.chain.cons hd₂ hl₁, _, _⟩,
      { rw [list.length_cons, hl₂], },
      { rw list.last_cons,
        exact hl₃, }, },
    { rintro ⟨_ | ⟨d, l⟩, hl₁, hl₂, hl₃⟩,
      { cases hl₂, },
      obtain _ | ⟨hcd, hl₁⟩ := hl₁,
      rw list.last_cons at hl₃,
      have := hn.mpr ⟨l, hl₁, nat.succ.inj hl₂, hl₃⟩,
      exact ⟨d, this, hcd⟩, }, },
end

lemma reduction_eq_Union {S : set (support_condition β)} :
  {c | ∃ d ∈ S, relation.refl_trans_gen (constrains α β) c d} = ⋃ n, nth_reduction α S n :=
begin
  refine subset_antisymm _ _,
  { rintros c ⟨d, hdS, hd⟩,
    obtain ⟨l, hl, rfl⟩ := list.exists_chain_of_relation_refl_trans_gen hd,
    rw mem_Union,
    refine ⟨l.length, _⟩,
    rw mem_nth_reduction_iff,
    refine ⟨l, hl, rfl, hdS⟩, },
  { intros c hc,
    rw mem_Union at hc,
    obtain ⟨i, hc⟩ := hc,
    rw mem_nth_reduction_iff at hc,
    obtain ⟨l, hl₁, hl₂, hl₃⟩ := hc,
    exact ⟨(c :: l).last (list.cons_ne_nil _ _), hl₃,
      list.relation_refl_trans_gen_of_exists_chain l hl₁ rfl⟩, },
end

lemma reduction_small' {S : set (support_condition β)} (h : small S) :
  small {c | ∃ d ∈ S, relation.refl_trans_gen (constrains α β) c d} :=
begin
  rw reduction_eq_Union,
  have : small ⋃ (n : ulift ℕ), nth_reduction α S n.down,
  { refine small_Union _ (λ _, small_nth_reduction α h),
    rw cardinal.mk_denumerable,
    exact Λ_limit.aleph_0_le.trans_lt Λ_lt_κ, },
  { convert this using 1,
    ext x : 1,
    simp only [mem_Union, ulift.exists], },
end

lemma reduction_small {S : set (support_condition β)} (h : small S) :
  small (reduction α S) :=
lt_of_le_of_lt (cardinal.mk_subtype_le_of_subset (λ c hc, hc.1)) (reduction_small' α h)

end con_nf
