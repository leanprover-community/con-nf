import phase2.constrains

/-!
# Strong supports
A support is *strong* if its near-litters are disjoint, and it is downward-closed under `≺`.
-/

universe u

open mul_action quiver set sum with_bot
open_locale cardinal

namespace con_nf
variables [params.{u}] (α : Λ) [position_data.{}] [phase_2_assumptions α]

variables (β : Λ) (G : Type*) {τ : Type*} [has_smul G (support_condition β)] [has_smul G τ]

structure strong_support (x : τ) extends support β G x :=
(closed : ∀ c d : support_condition β, c ≺[α] d → d ∈ carrier → c ∈ carrier)
(litter_set_eq : ∀ N A, (⟨inr N, A⟩ : support_condition β) ∈ carrier → litter_set N.fst = N.snd)

variables {β G} {x : τ}

def constrains_closure (S : set (support_condition β)) : set (support_condition β) :=
{c | (∀ N : near_litter, c.1 = inr N → litter_set N.fst = N.snd) ∧
  ∃ d ∈ S, relation.refl_trans_gen (constrains α β) c d}

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

def nth_constrains_closure (S : set (support_condition β)) : ℕ → set (support_condition β)
| 0 := S
| (n + 1) := {c | ∃ d, d ∈ nth_constrains_closure n ∧ c ≺[α] d}

lemma small_nth_constrains_closure {S : set (support_condition β)} {n : ℕ} (h : small S) :
  small (nth_constrains_closure α S n) :=
begin
  induction n with n hn,
  exact h,
  rw nth_constrains_closure,
  simp_rw [← exists_prop, subtype.exists', set_of_exists],
  refine small_Union hn _,
  rintro ⟨c, hc⟩,
  exact small_constrains α c,
end

lemma mem_nth_constrains_closure_iff {S : set (support_condition β)} {n : ℕ}
  {c : support_condition β} :
  c ∈ nth_constrains_closure α S n ↔
  ∃ l, list.chain (constrains α β) c l ∧ l.length = n ∧ (c :: l).last (list.cons_ne_nil _ _) ∈ S :=
begin
  induction n with n hn generalizing c,
  { rw nth_constrains_closure,
    split,
    { intro h,
      exact ⟨[], list.chain.nil, rfl, h⟩, },
    { rintro ⟨l, h₁, h₂, h₃⟩,
      rw list.length_eq_zero at h₂,
      cases h₂,
      exact h₃, }, },
  { simp only [nth_constrains_closure, mem_set_of_eq],
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

lemma constrains_closure_eq_Union {S : set (support_condition β)} :
  {c | ∃ d ∈ S, relation.refl_trans_gen (constrains α β) c d} = ⋃ n, nth_constrains_closure α S n :=
begin
  refine subset_antisymm _ _,
  { rintros c ⟨d, hdS, hd⟩,
    obtain ⟨l, hl, rfl⟩ := list.exists_chain_of_relation_refl_trans_gen hd,
    rw mem_Union,
    refine ⟨l.length, _⟩,
    rw mem_nth_constrains_closure_iff,
    refine ⟨l, hl, rfl, hdS⟩, },
  { intros c hc,
    rw mem_Union at hc,
    obtain ⟨i, hc⟩ := hc,
    rw mem_nth_constrains_closure_iff at hc,
    obtain ⟨l, hl₁, hl₂, hl₃⟩ := hc,
    exact ⟨(c :: l).last (list.cons_ne_nil _ _), hl₃,
      list.relation_refl_trans_gen_of_exists_chain l hl₁ rfl⟩, },
end

lemma constrains_closure_small' {S : set (support_condition β)} (h : small S) :
  small {c | ∃ d ∈ S, relation.refl_trans_gen (constrains α β) c d} :=
begin
  rw constrains_closure_eq_Union,
  have : small ⋃ (n : ulift ℕ), nth_constrains_closure α S n.down,
  { refine small_Union _ (λ _, small_nth_constrains_closure α h),
    rw cardinal.mk_denumerable,
    exact Λ_limit.aleph_0_le.trans_lt Λ_lt_κ, },
  { convert this using 1,
    ext x : 1,
    simp only [mem_Union, ulift.exists], },
end

lemma constrains_closure_small {S : set (support_condition β)} (h : small S) :
  small (constrains_closure α S) :=
lt_of_le_of_lt (cardinal.mk_subtype_le_of_subset (λ c hc, hc.2)) (constrains_closure_small' α h)

/-- We need a hypothesis on the action of `G` on support conditions. -/
lemma constrains_closure_supports {S : set (support_condition β)} (h : supports G S x) :
  supports G (constrains_closure α S) x :=
sorry

/-- This actually is false.
Consider the case where `c` has some near-litter in a designated support, and `d` is an inflexible
litter. Of course, the litter near the near-litter referenced by `c` is in `S`.  -/
lemma constrains_closure_closed {S : set (support_condition β)} :
  ∀ c d : support_condition β, c ≺[α] d →
  d ∈ constrains_closure α S → c ∈ constrains_closure α S :=
begin
  rintros ⟨c, A⟩ d hcd ⟨hd₁, e, he, hd₂⟩,
  split,
  { intros N hN,
    cases hN,
    obtain ⟨L, N, hN⟩ := N,
    obtain ⟨a | N', B⟩ := d,
    { rw constrains_atom at hcd,
      cases hcd,
      refl, },
    { rw constrains_iff at hcd,
      obtain _ | _ | _ | _ | _ := hcd,
      { simpa only [prod.mk.inj_iff, false_and, and_false, exists_false] using hcd, },
      { simp only [prod.mk.inj_iff, exists_eq_right_right'] at hcd,
        cases hcd.2.1,
        refl, },
      { simpa only [prod.mk.inj_iff, false_and, exists_false, and_false] using hcd, },
      { sorry },
      { sorry }, }, },
  { exact ⟨e, he, relation.refl_trans_gen.trans
    (relation.refl_trans_gen.tail relation.refl_trans_gen.refl hcd) hd₂⟩, },
end

lemma constrains_closure_litter_set_eq {S : set (support_condition β)} :
  ∀ N A, (⟨inr N, A⟩ : support_condition β) ∈ constrains_closure α S → litter_set N.fst = N.snd :=
λ N A h, h.1 N rfl

def support.strengthen (S : support β G x) : strong_support α β G x := {
  carrier := constrains_closure α S,
  small := constrains_closure_small α S.small,
  supports := constrains_closure_supports α S.supports,
  closed := constrains_closure_closed α,
  litter_set_eq := constrains_closure_litter_set_eq α,
}

end con_nf
