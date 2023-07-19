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

/-- A support condition is *flex-reduced* if it is an atom or a flexible litter. -/
@[mk_iff] inductive flex_reduced {β : type_index} : support_condition β → Prop
| mk_atom (a : atom) (B : extended_index β) : flex_reduced (inl a, B)
| mk_litter (L : litter) (B : extended_index β) :
    flexible α L B → flex_reduced (inr L.to_near_litter, B)

/-- The *reduction* of a set of support conditions is the downward closure of the set under
the constrains relation, but we only keep reduced conditions. -/
def reduction (S : set (support_condition β)) : set (support_condition β) :=
{c | ∃ d ∈ S, c ≤[α] d} ∩ set_of reduced

/-- The *flex-reduction* of a set of support conditions is the downward closure of the set under
the constrains relation, but we only keep flex-reduced conditions. -/
def flex_reduction (S : set (support_condition β)) : set (support_condition β) :=
{c | ∃ d ∈ S, c ≤[α] d} ∩ set_of (flex_reduced α)

lemma mem_reduction_of_reduced (S : set (support_condition β))
  (c : support_condition β) (hc₁ : reduced c) (hc₂ : c ∈ S) : c ∈ reduction α S :=
⟨⟨c, hc₂, relation.refl_trans_gen.refl⟩, hc₁⟩

lemma mem_reduction_of_reduced_constrains (S : set (support_condition β))
  (c d : support_condition β) (hc : reduced c) (hcd : c ≺[α] d) (hd : d ∈ S) : c ∈ reduction α S :=
⟨⟨d, hd, relation.refl_trans_gen.single hcd⟩, hc⟩

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

lemma reduction_designated_support_supports [core_tangle_data β] (t : tangle β) :
  supports (allowable β) (reduction α (designated_support t : set (support_condition β))) t :=
begin
  intros π h₁,
  refine (designated_support t).supports π _,
  rintros ⟨a | N, B⟩ h₂,
  { exact h₁ (mem_reduction_of_reduced α _ _ (reduced.mk_atom a B) h₂), },
  { by_cases N.is_litter,
    { obtain ⟨L, rfl⟩ := h.exists_litter_eq,
      exact h₁ (mem_reduction_of_reduced α _ _ (reduced.mk_litter L B) h₂), },
    { have h := near_litter.not_is_litter h,
      have h₃ := congr_arg prod.fst (h₁ (mem_reduction_of_reduced_constrains α _ _ _
        (reduced.mk_litter N.fst B) (constrains.near_litter N h B) h₂)),
      have h₄ := λ a ha, congr_arg prod.fst (h₁ (mem_reduction_of_reduced_constrains α _ _ _
        (reduced.mk_atom a B) (constrains.symm_diff N a ha B) h₂)),
      refine prod.ext _ rfl,
      change inr _ = inr _ at h₃,
      change ∀ a ha, inl _ = inl _ at h₄,
      change inr _ = inr _,
      simp only at h₃ h₄ ⊢,
      apply_fun set_like.coe at h₃,
      refine set_like.coe_injective _,
      refine (near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul _ N).trans _,
      change _ • (_ : set atom) = _ at h₃,
      simp only [struct_perm.to_near_litter_perm_smul_set, h₃],
      refine eq.trans _ (symm_diff_symm_diff_cancel_left (litter_set N.fst) _),
      refine congr_arg _ _,
      ext a : 1,
      split,
      { rintro ⟨b, hb, rfl⟩,
        rw h₄ b hb,
        exact hb, },
      { intro ha,
        refine ⟨a, ha, _⟩,
        exact h₄ a ha, }, }, },
end

noncomputable! def reduced_support [core_tangle_data β] (t : tangle β) :
  support β (allowable β) t := {
  carrier := reduction α (designated_support t : set (support_condition β)),
  small := reduction_small α (designated_support t).small,
  supports := reduction_designated_support_supports α t,
}

lemma mem_reduced_support_iff [core_tangle_data β] (t : tangle β) (c : support_condition β) :
  c ∈ reduced_support α t ↔ c ∈ reduction α (designated_support t : set (support_condition β)) :=
iff.rfl

lemma mem_reduction_designated_support {β γ : Iic α} {δ ε : Iio α}
  (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
  (B : path (β : type_index) γ) (t : tangle δ)
  (c : support_condition δ)
  (h : c ∈ reduced_support α t) :
  (c.fst, (B.cons (coe_lt hδ)).comp c.snd) <[α]
  (inr (f_map (coe_ne_coe.mpr $ coe_ne' hδε) t).to_near_litter,
    (B.cons (coe_lt hε)).cons (bot_lt_coe _)) :=
begin
  obtain ⟨⟨d, hd, hcd⟩, hc⟩ := h,
  refine relation.trans_gen.tail' _ (constrains.f_map hδ hε hδε B t d hd),
  exact refl_trans_gen_constrains_comp hcd _,
end

end con_nf
