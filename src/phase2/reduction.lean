import phase2.flexible

/-!
# Reductions of supports
-/

universe u

open mul_action quiver set sum with_bot
open_locale cardinal

namespace con_nf
variables [params.{u}] (α : Λ) [position_data.{}] [phase_2_assumptions α]

variables {β : Λ} {G : Type*} {τ : Type*} [has_smul G (support_condition β)] [has_smul G τ]

variables {β G} {x : τ}

/-- A support condition is *reduced* if it is an atom or a litter. -/
@[mk_iff] inductive reduced {β : type_index} : support_condition β → Prop
| mk_atom (a : atom) (B : extended_index β) : reduced (inl a, B)
| mk_litter (L : litter) (B : extended_index β) : reduced (inr L.to_near_litter, B)

/-- The *reduction* of a set of support conditions is the downward closure of the set under
the constrains relation, but we only keep reduced conditions. -/
def reduction (S : set (support_condition β)) : set (support_condition β) :=
{c | ∃ d ∈ S, c ≤[α] d} ∩ set_of reduced

lemma reduction_singleton (c : support_condition β) :
  reduction α {c} = ({c} ∪ {d | d <[α] c}) ∩ set_of reduced :=
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
  exact small_constrains c,
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
  {c | ∃ d ∈ S, c ≤[α] d} = ⋃ n, nth_reduction α S n :=
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
  small {c | ∃ d ∈ S, c ≤[α] d} :=
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

lemma reduction_small'' {S : set (support_condition β)} (h : small S) :
  small {c | ∃ d ∈ S, c <[α] d} :=
begin
  refine lt_of_le_of_lt (cardinal.mk_le_mk_of_subset _) (reduction_small' α h),
  rintros c ⟨d, hd₁, hd₂⟩,
  exact ⟨d, hd₁, hd₂.to_refl⟩,
end

lemma reduction_small {S : set (support_condition β)} (h : small S) :
  small (reduction α S) :=
lt_of_le_of_lt (cardinal.mk_subtype_le_of_subset (λ c hc, hc.1)) (reduction_small' α h)

end con_nf
