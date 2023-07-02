import phase2.atom_completion
import phase2.near_litter_completion

open function quiver set sum with_bot
open_locale classical pointwise

universe u

namespace con_nf

namespace struct_approx
variables [params.{u}] {α : Λ} [position_data.{}] [phase_2_assumptions α]
  {β : Iic α} [freedom_of_action_hypothesis β]

/-!
We now construct the completed action of a structural approximation using well-founded recursion
on support conditions. It remains to prove that this map yields an allowable permutation.
TODO: Rename `complete_atom_map`, `atom_completion` etc.
TODO: Swap argument order for things that take an atom/near-litter and an extended index.
-/

noncomputable def complete_atom_map (π : struct_approx β) (hπ : π.free) :
  atom → extended_index β → atom :=
hypothesis.fix_atom π.atom_completion (π.near_litter_completion hπ)

noncomputable def complete_near_litter_map (π : struct_approx β) (hπ : π.free) :
  near_litter → extended_index β → near_litter :=
hypothesis.fix_near_litter π.atom_completion (π.near_litter_completion hπ)

noncomputable def complete_litter_map (π : struct_approx β) (hπ : π.free)
  (L : litter) (A : extended_index β) : litter :=
(π.complete_near_litter_map hπ L.to_near_litter A).1

noncomputable def foa_hypothesis (π : struct_approx β) (hπ : π.free) {c : support_condition β} :
  hypothesis c :=
⟨λ b B hb, π.complete_atom_map hπ b B, λ N B hb, π.complete_near_litter_map hπ N B⟩

variables {π : struct_approx β} {hπ : π.free}

section map_spec
variables {a : atom} {L : litter} {N : near_litter} {A : extended_index β}

lemma complete_atom_map_eq :
  π.complete_atom_map hπ a A = π.atom_completion a A (π.foa_hypothesis hπ) :=
hypothesis.fix_atom_eq _ _ _ _

lemma complete_near_litter_map_eq :
  π.complete_near_litter_map hπ N A = π.near_litter_completion hπ N A (π.foa_hypothesis hπ) :=
hypothesis.fix_near_litter_eq _ _ _ _

lemma complete_litter_map_eq :
  π.complete_litter_map hπ L A = π.litter_completion hπ L A (π.foa_hypothesis hπ) :=
by rw [complete_litter_map, complete_near_litter_map_eq]; refl

lemma complete_near_litter_map_fst_eq :
  (π.complete_near_litter_map hπ L.to_near_litter A).1 = π.complete_litter_map hπ L A := rfl

@[simp] lemma foa_hypothesis_atom_image {c : support_condition β}
  (h : relation.trans_gen (constrains α β) (inl a, A) c) :
  (π.foa_hypothesis hπ : hypothesis c).atom_image a A h = π.complete_atom_map hπ a A := rfl

@[simp] lemma foa_hypothesis_near_litter_image {c : support_condition β}
  (h : relation.trans_gen (constrains α β) (inr N, A) c) :
  (π.foa_hypothesis hπ : hypothesis c).near_litter_image N A h =
    π.complete_near_litter_map hπ N A := rfl

end map_spec

lemma complete_atom_map_eq_of_mem_domain {a} {A} (h : a ∈ (π A).atom_perm.domain) :
  π.complete_atom_map hπ a A = π A • a :=
by rw [complete_atom_map_eq, atom_completion, dif_pos h]

lemma complete_atom_map_eq_of_not_mem_domain {a} {A} (h : a ∉ (π A).atom_perm.domain) :
  π.complete_atom_map hπ a A = ((π A).largest_sublitter a.1).order_iso
    ((π A).largest_sublitter (π.complete_litter_map hπ a.1 A))
    ⟨a, (π A).mem_largest_sublitter_of_not_mem_domain a h⟩ :=
by rw [complete_atom_map_eq, atom_completion, dif_neg h]; refl

/-!
Lemmas about the proof-relevant `inflexible_*` objects.
-/

lemma inflexible_of_inflexible_bot {β : Iic α} {L : litter} {A : extended_index β}
  (h : inflexible_bot L A) : inflexible α L A :=
begin
  have := inflexible.mk_bot h.hε h.B h.a,
  rw [← h.hL, ← h.hA] at this,
  exact this,
end

lemma inflexible_of_inflexible_coe {β : Iic α} {L : litter} {A : extended_index β}
  (h : inflexible_coe L A) : inflexible α L A :=
begin
  have := inflexible.mk_coe h.hδ h.hε h.hδε h.B h.t,
  rw [← h.hL, ← h.hA] at this,
  exact this,
end

lemma inflexible_bot_or_inflexible_coe_of_inflexible {β : Iic α} {L : litter} {A : extended_index β}
  (h : inflexible α L A) : nonempty (inflexible_bot L A) ∨ nonempty (inflexible_coe L A) :=
begin
  obtain ⟨hδ, hε, hδε, B, t⟩ | ⟨hε, B, a⟩ := h,
  { refine or.inr ⟨⟨_, _, _, _, _, _, _, _, rfl, rfl⟩⟩,
    assumption, },
  { exact or.inl ⟨⟨_, _, _, _, _, rfl, rfl⟩⟩, },
end

lemma flexible_iff_not_inflexible_bot_coe {β : Iic α} {L : litter} {A : extended_index β} :
  flexible α L A ↔ (inflexible_bot L A → false) ∧ (inflexible_coe L A → false) :=
begin
  split,
  { intro h,
    exact ⟨λ h', h (inflexible_of_inflexible_bot h'), λ h', h (inflexible_of_inflexible_coe h')⟩, },
  { intros h₁ h₂,
    cases inflexible_bot_or_inflexible_coe_of_inflexible h₂,
    exact h₁.1 h.some,
    exact h₁.2 h.some, },
end

@[simp] def near_litter_hypothesis_eq (N : near_litter) (A : extended_index β) :
  near_litter_hypothesis N A (π.foa_hypothesis hπ) = (π.foa_hypothesis hπ) := rfl

/-- A basic definition unfold. -/
lemma complete_litter_map_eq_of_inflexible_coe (hπ : π.free) {L : litter} {A : extended_index β}
  (h : inflexible_coe L A) (hH : hypothesis_injective_inflexible (π.foa_hypothesis hπ) h) :
  π.complete_litter_map hπ L A = f_map (with_bot.coe_ne_coe.mpr $ coe_ne' h.hδε)
    (hypothesised_allowable π hπ h (π.foa_hypothesis hπ) hH • h.t) :=
begin
  have : nonempty (inflexible_coe L A) := ⟨h⟩,
  rw [complete_litter_map_eq, litter_completion, dif_pos this],
  cases subsingleton.elim this.some h,
  rw dif_pos,
end

/-- A basic definition unfold. -/
lemma complete_litter_map_eq_of_inflexible_bot {L : litter} {A : extended_index β}
  (h : inflexible_bot L A) :
  π.complete_litter_map hπ L A =
  f_map (show (⊥ : type_index) ≠ (h.ε : Λ), from with_bot.bot_ne_coe)
    (π.complete_atom_map hπ h.a (h.B.cons (with_bot.bot_lt_coe _))) :=
begin
  have h₁ : ¬nonempty (inflexible_coe L A) := λ h', inflexible_bot_inflexible_coe h h'.some,
  have h₂ : nonempty (inflexible_bot L A) := ⟨h⟩,
  rw [complete_litter_map_eq, litter_completion, dif_neg h₁, dif_pos h₂],
  cases subsingleton.elim h₂.some h,
  refl,
end

/-- A basic definition unfold. -/
lemma complete_litter_map_eq_of_flexible {L : litter} {A : extended_index β}
  (h₁ : inflexible_bot L A → false) (h₂ : inflexible_coe L A → false) :
  π.complete_litter_map hπ L A = near_litter_approx.flexible_completion α (π A) A • L :=
by rw [complete_litter_map_eq, litter_completion,
  dif_neg (show ¬nonempty (inflexible_coe L A), from λ h, h₂ h.some),
  dif_neg (show ¬nonempty (inflexible_bot L A), from λ h, h₁ h.some)]

/-- A basic definition unfold. -/
lemma complete_litter_map_eq_of_flexible' {L : litter} {A : extended_index β}
  (h : flexible α L A) :
  π.complete_litter_map hπ L A = near_litter_approx.flexible_completion α (π A) A • L :=
complete_litter_map_eq_of_flexible
  (flexible_iff_not_inflexible_bot_coe.mp h).1
  (flexible_iff_not_inflexible_bot_coe.mp h).2

-- TODO: Move these notations earlier, and maybe consider different ones.
notation c ` <[`:50 α `] ` d:50 := relation.trans_gen (constrains α _) c d
notation c ` ≤[`:50 α `] ` d:50 := relation.refl_trans_gen (constrains α _) c d

def trans_constrained (c d : support_condition β) : set (support_condition β) :=
{e | e <[α] c} ∪ {e | e <[α] d}

def refl_trans_constrained (c d : support_condition β) : set (support_condition β) :=
{e | e ≤[α] c} ∪ {e | e ≤[α] d}

lemma mem_refl_trans_constrained_of_mem_trans_constrained {c d e : support_condition β}
  (he : e ∈ trans_constrained c d) : e ∈ refl_trans_constrained c d :=
begin
  cases he,
  exact or.inl he.to_refl,
  exact or.inr he.to_refl,
end

lemma trans_constrained_trans {c d e f : support_condition β}
  (he : e ∈ trans_constrained c d) (hf : f ≤[α] e) : f ∈ trans_constrained c d :=
begin
  cases he,
  exact or.inl (relation.trans_gen.trans_right hf he),
  exact or.inr (relation.trans_gen.trans_right hf he),
end

lemma refl_trans_constrained_trans {c d e f : support_condition β}
  (he : e ∈ refl_trans_constrained c d) (hf : f ≤[α] e) : f ∈ refl_trans_constrained c d :=
begin
  cases he,
  exact or.inl (hf.trans he),
  exact or.inr (hf.trans he),
end

lemma trans_constrained_of_refl_trans_constrained_of_trans_constrains
  {c d e f : support_condition β}
  (he : e ∈ refl_trans_constrained c d) (hf : f <[α] e) : f ∈ trans_constrained c d :=
begin
  cases he,
  exact or.inl (hf.trans_left he),
  exact or.inr (hf.trans_left he),
end

lemma trans_constrained_of_constrains {c d e f : support_condition β}
  (he : e ∈ trans_constrained c d) (hf : f ≺[α] e) : f ∈ trans_constrained c d :=
trans_constrained_trans he (relation.refl_trans_gen.single hf)

lemma refl_trans_constrained_of_constrains {c d e f : support_condition β}
  (he : e ∈ refl_trans_constrained c d) (hf : f ≺[α] e) : f ∈ refl_trans_constrained c d :=
refl_trans_constrained_trans he (relation.refl_trans_gen.single hf)

lemma trans_constrained_of_refl_trans_constrained_of_constrains {c d e f : support_condition β}
  (he : e ∈ refl_trans_constrained c d) (hf : f ≺[α] e) : f ∈ trans_constrained c d :=
trans_constrained_of_refl_trans_constrained_of_trans_constrains he (relation.trans_gen.single hf)

lemma fst_trans_constrained {c d : support_condition β}
  {a : atom} {A : extended_index β}
  (hac : (inl a, A) ∈ refl_trans_constrained c d) :
  (inr a.fst.to_near_litter, A) ∈ trans_constrained c d :=
trans_constrained_of_refl_trans_constrained_of_constrains hac (constrains.atom a A)

lemma fst_mem_trans_constrained' {c d : support_condition β} {A : extended_index β} {a : atom}
  (h : (inl a, A) ∈ trans_constrained c d) :
  (inr a.fst.to_near_litter, A) ∈ trans_constrained c d :=
trans_constrained_of_constrains h (constrains.atom a A)

lemma fst_mem_trans_constrained {c d : support_condition β} {A : extended_index β} {N : near_litter}
  (hN : (inr N, A) ∈ trans_constrained c d) :
  (inr N.fst.to_near_litter, A) ∈ trans_constrained c d :=
begin
  cases hN,
  exact or.inl (trans_gen_near_litter' hN),
  exact or.inr (trans_gen_near_litter' hN),
end

lemma fst_mem_trans_constrained_of_mem_symm_diff {c d : support_condition β}
  {A : extended_index β} {N : near_litter} {a : atom} (h : a ∈ litter_set N.1 ∆ N)
  (hN : (inr N, A) ∈ trans_constrained c d) :
  (inr a.fst.to_near_litter, A) ∈ trans_constrained c d :=
begin
  obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := h,
  { rw mem_litter_set at h₁,
    rw h₁,
    exact fst_mem_trans_constrained hN, },
  { cases hN,
    { refine fst_mem_trans_constrained' (or.inl _),
      exact relation.trans_gen.head (constrains.symm_diff N a (or.inr ⟨h₁, h₂⟩) A) hN, },
    { refine fst_mem_trans_constrained' (or.inr _),
      exact relation.trans_gen.head (constrains.symm_diff N a (or.inr ⟨h₁, h₂⟩) A) hN, }, },
end

lemma fst_mem_trans_constrained_of_mem {c d : support_condition β}
  {A : extended_index β} {N : near_litter} {a : atom} (h : a ∈ N)
  (hN : (inr N, A) ∈ trans_constrained c d) :
  (inr a.fst.to_near_litter, A) ∈ trans_constrained c d :=
begin
  by_cases ha : a.1 = N.1,
  { rw ha,
    exact fst_mem_trans_constrained hN, },
  { exact fst_mem_trans_constrained_of_mem_symm_diff (or.inr ⟨h, ha⟩) hN, },
end

/-- The inductive hypothesis used to prove that the induced action generated in the freedom of
action theorem is lawful. We perform induction over two support conditions at once so that we can
prove things like injectivity and surjectivity which consider two support conditions at once. -/
structure foa_props {π : struct_approx β} (hπ : π.free) (c d : support_condition β) : Prop :=
(atom_injective : ∀ a b (B : extended_index β),
  (inl a, B) ∈ trans_constrained c d →
  (inl b, B) ∈ trans_constrained c d →
  π.complete_atom_map hπ a B = π.complete_atom_map hπ b B → a = b)
(litter_injective : ∀ (L₁ L₂ : litter) (B : extended_index β),
  (inr L₁.to_near_litter, B) ∈ trans_constrained c d →
  (inr L₂.to_near_litter, B) ∈ trans_constrained c d →
  π.complete_litter_map hπ L₁ B = π.complete_litter_map hπ L₂ B → L₁ = L₂)
(map_flexible : ∀ (L : litter) {γ : Iic α} (A : path (β : type_index) γ) (B : extended_index γ)
  (hL : (inr L.to_near_litter, A.comp B) ∈ trans_constrained c d)
  (hflex : flexible α L B), flexible α (π.complete_litter_map hπ L (A.comp B)) B)

lemma eq_of_sublitter_bijection_apply_eq {π : near_litter_approx} {L₁ L₂ L₃ L₄ : litter} {a b} :
  ((π.largest_sublitter L₁).order_iso (π.largest_sublitter L₂) a : atom) =
  (π.largest_sublitter L₃).order_iso (π.largest_sublitter L₄) b →
  L₁ = L₃ → L₂ = L₄ → (a : atom) = b :=
begin
  rintros h₁ rfl rfl,
  simp only [subtype.coe_inj, embedding_like.apply_eq_iff_eq] at h₁,
  rw h₁,
end

/-- We show that injectivity of the atom map extends to atoms below the current support conditions
`c` and `d`, given that certain properties hold for support conditions before `c` and `d`. -/
lemma atom_injective_extends {c d : support_condition β} (H : foa_props hπ c d)
  {a b : atom} {A : extended_index β}
  (hac : (inl a, A) ∈ refl_trans_constrained c d)
  (hbc : (inl b, A) ∈ refl_trans_constrained c d)
  (h : π.complete_atom_map hπ a A = π.complete_atom_map hπ b A) :
  a = b :=
begin
  by_cases ha : a ∈ (π A).atom_perm.domain;
  by_cases hb : b ∈ (π A).atom_perm.domain,
  { rw [complete_atom_map_eq_of_mem_domain ha, complete_atom_map_eq_of_mem_domain hb] at h,
    exact (π A).atom_perm.inj_on ha hb h, },
  { rw [complete_atom_map_eq_of_mem_domain ha, complete_atom_map_eq_of_not_mem_domain hb] at h,
    cases (π A).not_mem_domain_of_mem_largest_sublitter ((subtype.coe_eq_iff.mp h.symm).some)
      ((π A).atom_perm.map_domain ha), },
  { rw [complete_atom_map_eq_of_not_mem_domain ha, complete_atom_map_eq_of_mem_domain hb] at h,
    cases (π A).not_mem_domain_of_mem_largest_sublitter ((subtype.coe_eq_iff.mp h).some)
      ((π A).atom_perm.map_domain hb), },
  { rw [complete_atom_map_eq_of_not_mem_domain ha, complete_atom_map_eq_of_not_mem_domain hb] at h,
    have h₁ := (subtype.coe_eq_iff.mp h).some.1,
    have h₂ := (((π A).largest_sublitter b.1).order_iso
      ((π A).largest_sublitter (π.complete_litter_map hπ b.1 A))
      ⟨b, (π A).mem_largest_sublitter_of_not_mem_domain b hb⟩).prop.1,
    have := H.litter_injective _ _ _
      (fst_trans_constrained hac) (fst_trans_constrained hbc) (h₁.symm.trans h₂),
    have := eq_of_sublitter_bijection_apply_eq h this (by rw this),
    rw [set_like.coe_mk, set_like.coe_mk] at this,
    exact this, },
end

lemma complete_atom_map_mem_complete_near_litter_map
  {c d : support_condition β} (H : foa_props hπ c d)
  {a : atom} {A : extended_index β} {N : near_litter} (h : a ∈ N)
  (hN : (inr N, A) ∈ trans_constrained c d) :
  π.complete_atom_map hπ a A ∈ π.complete_near_litter_map hπ N A :=
begin
  rw complete_near_litter_map_eq,
  by_cases ha : a ∈ (π A).atom_perm.domain,
  { rw complete_atom_map_eq_of_mem_domain ha,
    refine or.inl ⟨or.inr ⟨a, ⟨h, ha⟩, rfl⟩, _⟩,
    rintro ⟨_, ⟨b, rfl⟩, _, ⟨hb, rfl⟩, hab⟩,
    simp only [foa_hypothesis_atom_image, mem_singleton_iff] at hab,
    rw complete_atom_map_eq_of_not_mem_domain hb.2 at hab,
    have := sublitter.order_iso_apply_mem _,
    rw ← hab at this,
    exact this.2 ((π A).atom_perm.map_domain ha), },
  rw complete_atom_map_eq_of_not_mem_domain ha,
  by_cases ha' : a.fst = N.1,
  { refine or.inl ⟨or.inl _, _⟩,
    { rw set_like.mem_coe,
      convert sublitter.order_iso_apply_mem _ using 1,
      rw [ha', near_litter_hypothesis_eq, complete_litter_map_eq], },
    { rintro ⟨_, ⟨b, rfl⟩, _, ⟨hb, rfl⟩, hab⟩,
      simp only [foa_hypothesis_atom_image, mem_singleton_iff] at hab,
      rw complete_atom_map_eq_of_not_mem_domain hb.2 at hab,
      have := H.litter_injective _ _ _
        (fst_mem_trans_constrained hN) (fst_mem_trans_constrained_of_mem_symm_diff hb.1 hN) _,
      { rw ← ha' at this,
        rw [sublitter.order_iso_congr_left (congr_arg _ this) _,
          sublitter.order_iso_congr_right (congr_arg _ (congr_arg2 _ this rfl)) _,
          subtype.coe_inj, equiv_like.apply_eq_iff_eq] at hab,
        simp only [set_like.coe_mk] at hab,
        cases hab,
        exact hb.1.elim (λ h', h'.2 h) (λ h', h'.2 ha'), },
      have := order_iso_apply_eq hab,
      simp only [near_litter_approx.largest_sublitter_litter, ha'] at this,
      exact this, }, },
  { refine or.inr ⟨⟨_, ⟨a, rfl⟩, _, ⟨⟨or.inr ⟨h, ha'⟩, ha⟩, rfl⟩, _⟩, _⟩,
    { simp only [foa_hypothesis_atom_image, mem_singleton_iff],
      rw complete_atom_map_eq_of_not_mem_domain, },
    rintro (h' | ⟨b, ⟨hb₁, hb₂⟩, hb₃⟩),
    { simp only [near_litter_hypothesis_eq, near_litter_approx.coe_largest_sublitter,
        mem_diff, mem_litter_set, ← complete_litter_map_eq] at h',
      have := sublitter.order_iso_apply_fst_eq _,
      rw [h'.1, near_litter_approx.largest_sublitter_litter] at this,
      exact ha' (H.litter_injective _ _ _
        (fst_mem_trans_constrained hN) (fst_mem_trans_constrained_of_mem h hN) this).symm, },
    { have := sublitter.order_iso_apply_mem _,
      rw ← hb₃ at this,
      exact this.2 ((π A).atom_perm.map_domain hb₂), }, },
end

@[simp] lemma near_litter_completion_map_eq {L : litter} {A : extended_index β} :
  near_litter_completion_map π hπ L.to_near_litter A (π.foa_hypothesis hπ) =
  (litter_set (π.litter_completion hπ L.to_near_litter.fst A (π.foa_hypothesis hπ)) \
    (π A).atom_perm.domain) ∪
  π A • (litter_set L ∩ (π A).atom_perm.domain) :=
begin
  simp only [near_litter_completion_map, set.symm_diff_def, near_litter_hypothesis_eq,
    litter.coe_to_near_litter, litter.to_near_litter_fst, mem_union, mem_diff, mem_litter_set,
    diff_self, mem_empty_iff_false, false_and, Union_neg', not_false_iff, Union_empty, diff_empty,
    empty_diff, union_empty, near_litter_approx.coe_largest_sublitter],
end

lemma mem_of_complete_atom_map_mem_complete_near_litter_map
  {c d : support_condition β} (H : foa_props hπ c d)
  {a : atom} {A : extended_index β} {L : litter}
  (h : π.complete_atom_map hπ a A ∈ π.complete_near_litter_map hπ L.to_near_litter A)
  (ha : (inl a, A) ∈ trans_constrained c d)
  (hL : (inr L.to_near_litter, A) ∈ trans_constrained c d) :
  a.fst = L :=
begin
  simp only [complete_near_litter_map_eq, near_litter_completion,
    near_litter_completion_map_eq] at h,
  cases h,
  { rw [mem_diff, mem_litter_set, complete_atom_map_eq_of_not_mem_domain] at h,
    { refine H.litter_injective a.fst L A (fst_mem_trans_constrained' ha) hL _,
      generalize_proofs at h,
      rw litter.to_near_litter_fst at h,
      simp only [complete_litter_map_eq, ← struct_approx.order_iso_apply_mem h.1,
        near_litter_approx.largest_sublitter_litter], },
    { intro ha,
      rw complete_atom_map_eq_of_mem_domain ha at h,
      exact h.2 ((π A).atom_perm.map_domain ha), }, },
  { obtain ⟨b, ⟨hb₁, hb₂⟩, hb⟩ := h,
    by_cases ha' : a ∈ (π A).atom_perm.domain,
    { rw complete_atom_map_eq_of_mem_domain ha' at hb,
      cases (π A).atom_perm.inj_on hb₂ ha' hb,
      exact hb₁, },
    { rw complete_atom_map_eq_of_not_mem_domain ha' at hb,
      have := sublitter.order_iso_apply_mem _,
      rw ← hb at this,
      cases this.2 ((π A).atom_perm.map_domain hb₂), }, },
end

lemma eq_of_mem_near_litter_completion_map {c d : support_condition β} (H : foa_props hπ c d)
  {L₁ L₂ : litter} {A : extended_index β}
  (hL₁ : (inr L₁.to_near_litter, A) ∈ trans_constrained c d)
  (hL₂ : (inr L₂.to_near_litter, A) ∈ trans_constrained c d)
  (a : atom)
  (ha₁ : a ∈ near_litter_completion_map π hπ L₁.to_near_litter A (π.foa_hypothesis hπ))
  (ha₂ : a ∈ near_litter_completion_map π hπ L₂.to_near_litter A (π.foa_hypothesis hπ)) :
  L₁ = L₂ :=
begin
  rw near_litter_completion_map_eq at ha₁ ha₂,
  obtain (⟨ha₁, ha₁'⟩ | ha₁) := ha₁;
  obtain (⟨ha₂, ha₂'⟩ | ha₂) := ha₂,
  { rw mem_litter_set at ha₁ ha₂,
    rw ha₁ at ha₂,
    refine H.litter_injective L₁ L₂ A hL₁ hL₂ _,
    rw [complete_litter_map_eq, complete_litter_map_eq],
    exact ha₂, },
  { obtain ⟨b, hb, rfl⟩ := ha₂,
    cases ha₁' ((π A).atom_perm.map_domain hb.2), },
  { obtain ⟨b, hb, rfl⟩ := ha₁,
    cases ha₂' ((π A).atom_perm.map_domain hb.2), },
  { obtain ⟨b, hb, rfl⟩ := ha₁,
    obtain ⟨c, hc, hc'⟩ := ha₂,
    cases (π A).atom_perm.inj_on hc.2 hb.2 hc',
    exact eq_of_mem_litter_set_of_mem_litter_set hb.1 hc.1, },
end

lemma eq_of_litter_map_inter_nonempty {c d : support_condition β} (H : foa_props hπ c d)
  {L₁ L₂ : litter} {A : extended_index β}
  (hL₁ : (inr L₁.to_near_litter, A) ∈ trans_constrained c d)
  (hL₂ : (inr L₂.to_near_litter, A) ∈ trans_constrained c d)
  (h : ((π.complete_near_litter_map hπ L₁.to_near_litter A : set atom) ∩
    π.complete_near_litter_map hπ L₂.to_near_litter A).nonempty) : L₁ = L₂ :=
begin
  obtain ⟨a, ha₁, ha₂⟩ := h,
  refine eq_of_mem_near_litter_completion_map H hL₁ hL₂ a _ _,
  rwa complete_near_litter_map_eq at ha₁,
  rwa complete_near_litter_map_eq at ha₂,
end

lemma hypothesis_injective_inflexible_of_mem_refl_trans_constrained
  {c d : support_condition β} (H : foa_props hπ c d)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (h' : (inr L.to_near_litter, A) ∈ refl_trans_constrained c d) :
  hypothesis_injective_inflexible (π.foa_hypothesis hπ) h :=
begin
  constructor,
  { intros a b B ha hb hab,
    rw [inflexible_support, ← h.hL, ← h.hA] at ha hb,
    refine H.atom_injective a b ((h.B.cons $ coe_lt h.hδ).comp B) _ _ hab,
    exact trans_constrained_of_refl_trans_constrained_of_trans_constrains h' ha,
    exact trans_constrained_of_refl_trans_constrained_of_trans_constrains h' hb, },
  { intros L₁ L₂ B hL₁ hL₂ hL,
    rw [inflexible_support, ← h.hL, ← h.hA] at hL₁ hL₂,
    refine H.litter_injective L₁ L₂ ((h.B.cons $ coe_lt h.hδ).comp B) _ _ _,
    exact trans_constrained_of_refl_trans_constrained_of_trans_constrains h' hL₁,
    exact trans_constrained_of_refl_trans_constrained_of_trans_constrains h' hL₂,
    simp only [foa_hypothesis_near_litter_image] at hL,
    rw eq_of_litter_map_inter_nonempty H _ _ hL,
    exact trans_constrained_of_refl_trans_constrained_of_trans_constrains h' hL₁,
    exact trans_constrained_of_refl_trans_constrained_of_trans_constrains h' hL₂, },
  { intros a L' B ha hL',
    simp only [mem_litter_set, foa_hypothesis_atom_image, foa_hypothesis_near_litter_image],
    rw [inflexible_support, ← h.hL, ← h.hA] at ha hL',
    split,
    { intro haL,
      refine complete_atom_map_mem_complete_near_litter_map H haL _,
      exact trans_constrained_of_refl_trans_constrained_of_trans_constrains h' hL', },
    { intro haL,
      refine mem_of_complete_atom_map_mem_complete_near_litter_map H haL _ _,
      exact trans_constrained_of_refl_trans_constrained_of_trans_constrains h' ha,
      exact trans_constrained_of_refl_trans_constrained_of_trans_constrains h' hL', }, },
  { intros L' B hL₁ hL₂,
    rw [foa_hypothesis_near_litter_image, complete_near_litter_map_fst_eq],
    rw [inflexible_support, ← h.hL, ← h.hA] at hL₁,
    have := H.map_flexible,
    refine @this L' h.δ (h.B.cons $ coe_lt h.hδ) B _ hL₂,
    exact trans_constrained_of_refl_trans_constrained_of_trans_constrains h' hL₁, },
end

lemma ne_of_inflexible_bot_of_not_inflexible_bot {c d : support_condition β} (H : foa_props hπ c d)
  {L₁ L₂ : litter} {A : extended_index β}
  (hL₁ : inflexible_bot L₁ A) (hL₂ : inflexible_bot L₂ A → false)
  (hL₁' : (inr L₁.to_near_litter, A) ∈ refl_trans_constrained c d)
  (hL₂' : (inr L₂.to_near_litter, A) ∈ refl_trans_constrained c d) :
  π.complete_litter_map hπ L₁ A ≠ π.complete_litter_map hπ L₂ A :=
begin
  obtain ⟨γ₁, ε₁, hγε₁, B₁, a₁, hL₁, hA₁⟩ := hL₁,
  rw complete_litter_map_eq_of_inflexible_bot ⟨γ₁, ε₁, hγε₁, B₁, a₁, hL₁, hA₁⟩,
  by_cases h₂ : nonempty (inflexible_coe L₂ A),
  { cases h₂,
    rw complete_litter_map_eq_of_inflexible_coe hπ h₂,
    intro h,
    have := congr_arg litter.β h,
    simp only [f_map, bot_ne_coe] at this,
    exact this,
    exact hypothesis_injective_inflexible_of_mem_refl_trans_constrained H h₂ hL₂', },
  { have flex := flexible_iff_not_inflexible_bot_coe.mpr ⟨hL₂, λ h, h₂ ⟨h⟩⟩,
    rw complete_litter_map_eq_of_flexible hL₂ (λ h, h₂ ⟨h⟩),
    intro h,
    have : L₂ ∈ ((π A).flexible_completion α A).litter_perm.domain :=
      by rwa near_litter_approx.flexible_completion_litter_perm_domain_free _ _ _ (hπ A),
    have := ((π A).flexible_completion α A).litter_perm.map_domain this,
    rw [near_litter_approx.smul_litter_eq, ← h,
      near_litter_approx.flexible_completion_litter_perm_domain_free _ _ _ (hπ A)] at this,
    refine this _,
    have := inflexible.mk_bot hγε₁ B₁ _,
    rw ← hA₁ at this,
    exact this, },
end

lemma ne_of_inflexible_coe_of_not_inflexible {c d : support_condition β} (H : foa_props hπ c d)
  {L₁ L₂ : litter} {A : extended_index β}
  (hL₁ : inflexible_coe L₁ A)
  (hL₂ : inflexible_bot L₂ A → false) (hL₂' : inflexible_coe L₂ A → false)
  (hcL₁ : (inr L₁.to_near_litter, A) ∈ refl_trans_constrained c d) :
  π.complete_litter_map hπ L₁ A ≠ π.complete_litter_map hπ L₂ A :=
begin
  rw complete_litter_map_eq_of_inflexible_coe hπ hL₁,
  have flex := flexible_iff_not_inflexible_bot_coe.mpr ⟨hL₂, hL₂'⟩,
  rw complete_litter_map_eq_of_flexible hL₂ hL₂',
  intro h,
  have : L₂ ∈ ((π A).flexible_completion α A).litter_perm.domain :=
    by rwa near_litter_approx.flexible_completion_litter_perm_domain_free _ _ _ (hπ A),
  have := ((π A).flexible_completion α A).litter_perm.map_domain this,
  rw [near_litter_approx.smul_litter_eq, ← h,
    near_litter_approx.flexible_completion_litter_perm_domain_free _ _ _ (hπ A)] at this,
  refine this _,
  obtain ⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₁, hL₁, hA₁⟩ := hL₁,
  have := inflexible.mk_coe hδ₁ hε₁ hδε₁ B₁ _,
  rw ← hA₁ at this,
  exact this,
  refine hypothesis_injective_inflexible_of_mem_refl_trans_constrained H hL₁ hcL₁,
end

lemma trans_constrained_small (c d : support_condition β) : small (trans_constrained c d) :=
begin
  have := reduction_small' α (small.union (small_singleton c) (small_singleton d)),
  refine small.image_subset id injective_id this _,
  intros e he,
  simp only [id.def, image_id'] at he,
  cases he,
  exact ⟨c, or.inl rfl, he.to_refl⟩,
  exact ⟨d, or.inr rfl, he.to_refl⟩,
end

-- TODO: hypothesis_injective_inflexible_of_mem_refl_trans_constrained as a corollary to this.
noncomputable def trans_gen_struct_approx {c d : support_condition β} (H : foa_props hπ c d)
  {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ) (A : quiver.path (β : type_index) γ) :
  weak_struct_approx δ :=
λ B, {
  atom_map := λ a, {
    dom := (inl a, (A.cons (coe_lt hδ)).comp B) ∈ trans_constrained c d,
    get := λ ha, π.complete_atom_map hπ a ((A.cons (coe_lt hδ)).comp B)
  },
  litter_map := λ L, {
    dom := (inr L.to_near_litter, (A.cons (coe_lt hδ)).comp B) ∈ trans_constrained c d,
    get := λ hL, π.complete_near_litter_map hπ L.to_near_litter ((A.cons (coe_lt hδ)).comp B)
  },
  atom_map_dom_small := begin
    refine small.image_subset (λ a, (inl a, (A.cons (coe_lt hδ)).comp B)) _
      (trans_constrained_small c d) _,
    { intros a b h,
      simp only [prod.mk.inj_iff, eq_self_iff_true, and_true] at h,
      exact h, },
    { rintros _ ⟨a, ha, rfl⟩,
      simp only [pfun.dom_mk, mem_set_of_eq] at ha,
      exact ha, },
  end,
  litter_map_dom_small := begin
    refine small.image_subset (λ L, (inr L.to_near_litter, (A.cons (coe_lt hδ)).comp B)) _
      (trans_constrained_small c d) _,
    { intros L₁ L₂ h,
      simp only [prod.mk.inj_iff, eq_self_iff_true, and_true,
        litter.to_near_litter_injective.eq_iff] at h,
      exact h, },
    { rintros _ ⟨L, hL, rfl⟩,
      exact hL, },
  end,
  atom_map_injective := λ a b, H.atom_injective a b _,
  litter_map_injective := λ L₁ L₂ hL₁ hL₂ h, begin
    refine H.litter_injective L₁ L₂ _ hL₁ hL₂ _,
    rw eq_of_litter_map_inter_nonempty H hL₁ hL₂ h,
  end,
  atom_mem := λ a ha L hL, begin
    simp only [mem_litter_set, foa_hypothesis_atom_image, foa_hypothesis_near_litter_image],
    split,
    exact λ haL, complete_atom_map_mem_complete_near_litter_map H haL hL,
    exact λ haL, mem_of_complete_atom_map_mem_complete_near_litter_map H haL ha hL,
  end,
}

@[simp] lemma trans_gen_struct_approx_atom_map {c d : support_condition β} (H : foa_props hπ c d)
  {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ) (A : quiver.path (β : type_index) γ)
  (B : extended_index δ) (a : atom) :
  (trans_gen_struct_approx H hδ A B).atom_map a = {
    dom := (inl a, (A.cons (coe_lt hδ)).comp B) ∈ trans_constrained c d,
    get := λ ha, π.complete_atom_map hπ a ((A.cons (coe_lt hδ)).comp B)
  } := rfl

@[simp] lemma trans_gen_struct_approx_litter_map {c d : support_condition β} (H : foa_props hπ c d)
  {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ) (A : quiver.path (β : type_index) γ)
  (B : extended_index δ) (L : litter) :
  (trans_gen_struct_approx H hδ A B).litter_map L = {
    dom := (inr L.to_near_litter, (A.cons (coe_lt hδ)).comp B) ∈ trans_constrained c d,
    get := λ hL, π.complete_near_litter_map hπ L.to_near_litter ((A.cons (coe_lt hδ)).comp B)
  } := rfl

lemma trans_gen_struct_approx_coherent_aux₁ {c d : support_condition β} (H : foa_props hπ c d)
  {γ : Iic α} {δ ε : Iio α} (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
  (A : quiver.path (β : type_index) γ) (t : tangle δ)
  (ht : (inr (f_map (coe_ne_coe.mpr (coe_ne' hδε)) t).to_near_litter,
    (A.cons (coe_lt hε)).cons (bot_lt_coe _)) ∈ refl_trans_constrained c d)
  {ρ : allowable δ}
  {γ' : Iic α} {δ' ε' : Iio α} (hδ' : (δ' : Λ) < γ') (hε' : (ε' : Λ) < γ') (hδε' : δ' ≠ ε')
  (B : path (δ : type_index) γ') (t' : tangle δ')
  (hL : (((trans_gen_struct_approx H hδ A).refine
      ((B.cons $ coe_lt hε').cons (bot_lt_coe _))).litter_map
    (f_map (coe_ne_coe.mpr (coe_ne' hδε')) t')).dom)
  (e : support_condition δ) (he : e ∈ (designated_support t).carrier)
  (ih₁ : (inr (f_map (coe_ne_coe.mpr (coe_ne' hδε')) t').to_near_litter,
    (B.cons $ coe_lt hε').cons (bot_lt_coe _)) ≤[α] e)
  (C : extended_index ↑δ') (a : atom)
  (haC : (inl a, ((A.cons $ coe_lt hδ).comp (B.cons $ coe_lt hδ')).comp C) <[α]
    (inr (f_map (coe_ne_coe.mpr (coe_ne' hδε')) t').to_near_litter,
      (((A.cons $ coe_lt hδ).comp B).cons $ coe_lt hε').cons (bot_lt_coe _)))
  (ih₂ : struct_perm.derivative ((B.cons $ coe_lt hδ').comp C) (allowable.to_struct_perm ρ) • a =
    (trans_gen_struct_approx H hδ A ((B.cons $ coe_lt hδ').comp C)).refine.atom_map_or_else a) :
  struct_perm.derivative C
    (allowable.to_struct_perm
      (π.hypothesised_allowable hπ
        ⟨γ', δ', ε', hδ', hε', hδε', (A.cons $ coe_lt hδ).comp B, t', rfl, rfl⟩
        (π.foa_hypothesis hπ)
        (hypothesis_injective_inflexible_of_mem_refl_trans_constrained H _
          (mem_refl_trans_constrained_of_mem_trans_constrained hL)))) • a =
  struct_perm.derivative C
    (allowable.to_struct_perm
        (allowable_derivative (γ' : Iic_index α) δ' (coe_lt_coe.mpr hδ')
          ((allowable.derivative
            (show path ((δ : Iic_index α) : type_index) (γ' : Iic_index α), from B)) ρ))) • a :=
begin
  have he' : (e.fst, (A.cons $ coe_lt hδ).comp e.snd) ∈ trans_constrained c d,
  { refine trans_constrained_of_refl_trans_constrained_of_constrains ht _,
    exact constrains.f_map hδ hε hδε _ _ _ he, },
  have ha : ((trans_gen_struct_approx H hδ A ((B.cons $ coe_lt hδ').comp C)).atom_map a).dom,
  { simp only [trans_gen_struct_approx_atom_map],
    rw ← path.comp_assoc,
    refine trans_constrained_trans _ haC.to_refl,
    have := refl_trans_gen_constrains_comp ih₁ (A.cons $ coe_lt hδ),
    simp only [path.comp_cons] at this,
    exact trans_constrained_trans he' this, },
  rw weak_near_litter_approx.atom_map_or_else_of_dom at ih₂,
  swap,
  { exact or.inl (or.inl ha), },
  rw [← struct_perm.derivative_derivative, struct_perm.derivative_cons] at ih₂,
  rw allowable.derivative_to_struct_perm
    (show path ((δ : Iic_index α) : type_index) (γ' : Iic_index α), from B) at ih₂,
  rw allowable.derivative_to_struct_perm
    (show path ((γ' : Iic_index α) : type_index) (δ' : Iic_index α), from _) at ih₂,
  refine eq.trans _ ih₂.symm,
  rw weak_near_litter_approx.refine_atom_map_get ha,
  refine (weak_struct_approx.smul_atom_eq _
    (hypothesised_allowable_exactly_approximates π hπ
    ⟨γ', δ', ε', hδ', hε', hδε', _, t', rfl, rfl⟩ (π.foa_hypothesis hπ)
    (hypothesis_injective_inflexible_of_mem_refl_trans_constrained H _
      (mem_refl_trans_constrained_of_mem_trans_constrained hL))) (or.inl (or.inl haC))).trans _,
  refine (weak_near_litter_approx.refine_atom_map_get _).trans _,
  simp only [hypothesised_weak_struct_approx_atom_map, foa_hypothesis_atom_image,
    trans_gen_struct_approx_atom_map, path.comp_cons, ← path.comp_assoc],
end

lemma trans_gen_struct_approx_coherent_aux₂ {c d : support_condition β} (H : foa_props hπ c d)
  {γ : Iic α} {δ ε : Iio α} (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
  (A : quiver.path (β : type_index) γ) (t : tangle δ)
  (ht : (inr (f_map (coe_ne_coe.mpr (coe_ne' hδε)) t).to_near_litter,
    (A.cons (coe_lt hε)).cons (bot_lt_coe _)) ∈ refl_trans_constrained c d)
  {ρ : allowable δ}
  {γ' : Iic α} {δ' ε' : Iio α} (hδ' : (δ' : Λ) < γ') (hε' : (ε' : Λ) < γ') (hδε' : δ' ≠ ε')
  (B : path (δ : type_index) γ') (t' : tangle δ')
  (hL : (((trans_gen_struct_approx H hδ A).refine
      ((B.cons $ coe_lt hε').cons (bot_lt_coe _))).litter_map
    (f_map (coe_ne_coe.mpr (coe_ne' hδε')) t')).dom)
  (e : support_condition δ) (he : e ∈ (designated_support t).carrier)
  (ih₁ : (inr (f_map (coe_ne_coe.mpr (coe_ne' hδε')) t').to_near_litter,
    (B.cons $ coe_lt hε').cons (bot_lt_coe _)) ≤[α] e)
  (C : extended_index ↑δ') (N : near_litter)
  (haC : (inr N, ((A.cons $ coe_lt hδ).comp (B.cons $ coe_lt hδ')).comp C) <[α]
    (inr (f_map (coe_ne_coe.mpr (coe_ne' hδε')) t').to_near_litter,
      (((A.cons $ coe_lt hδ).comp B).cons $ coe_lt hε').cons (bot_lt_coe _)))
  (ih₂ : struct_perm.derivative ((B.cons $ coe_lt hδ').comp C) (allowable.to_struct_perm ρ) • N =
    (trans_gen_struct_approx H hδ A
      ((B.cons $ coe_lt hδ').comp C)).refine.near_litter_map_or_else N) :
  struct_perm.derivative C
    (allowable.to_struct_perm
      (π.hypothesised_allowable hπ
        ⟨γ', δ', ε', hδ', hε', hδε', (A.cons $ coe_lt hδ).comp B, t', rfl, rfl⟩
        (π.foa_hypothesis hπ)
        (hypothesis_injective_inflexible_of_mem_refl_trans_constrained H _
          (mem_refl_trans_constrained_of_mem_trans_constrained hL)))) • N =
  struct_perm.derivative C
    (allowable.to_struct_perm
        (allowable_derivative (γ' : Iic_index α) δ' (coe_lt_coe.mpr hδ')
          ((allowable.derivative
            (show path ((δ : Iic_index α) : type_index) (γ' : Iic_index α), from B)) ρ))) • N :=
begin
  have he' : (e.fst, (A.cons $ coe_lt hδ).comp e.snd) ∈ trans_constrained c d,
  { refine trans_constrained_of_refl_trans_constrained_of_constrains ht _,
    exact constrains.f_map hδ hε hδε _ _ _ he, },
  have hN : ((trans_gen_struct_approx H hδ A ((B.cons $ coe_lt hδ').comp C)).litter_map N.fst).dom,
  { simp only [trans_gen_struct_approx_litter_map],
    rw ← path.comp_assoc,
    refine trans_constrained_trans _ (trans_gen_near_litter' haC).to_refl,
    have := refl_trans_gen_constrains_comp ih₁ (A.cons $ coe_lt hδ),
    simp only [path.comp_cons] at this,
    exact trans_constrained_trans he' this, },
  have ha : ∀ a (ha : a ∈ litter_set N.fst ∆ N),
    ((trans_gen_struct_approx H hδ A ((B.cons $ coe_lt hδ').comp C)).atom_map a).dom,
  { intros a ha,
    simp only [trans_gen_struct_approx_atom_map],
    rw ← path.comp_assoc,
    refine trans_constrained_trans _ (haC.head $ constrains.symm_diff N a ha _).to_refl,
    have := refl_trans_gen_constrains_comp ih₁ (A.cons $ coe_lt hδ),
    simp only [path.comp_cons] at this,
    exact trans_constrained_trans he' this, },
  rw weak_near_litter_approx.near_litter_map_or_else_of_dom at ih₂,
  swap,
  { exact hN, },
  swap,
  { exact λ a ha', or.inl (or.inl (ha a ha')), },
  rw [← struct_perm.derivative_derivative, struct_perm.derivative_cons] at ih₂,
  rw allowable.derivative_to_struct_perm
    (show path ((δ : Iic_index α) : type_index) (γ' : Iic_index α), from B) at ih₂,
  rw allowable.derivative_to_struct_perm
    (show path ((γ' : Iic_index α) : type_index) (δ' : Iic_index α), from _) at ih₂,
  refine eq.trans _ ih₂.symm,
  rw ← set_like.coe_set_eq,
  refine (near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul _ _).trans _,
  -- have := hypothesised_allowable_exactly_approximates π hπ
  --   ⟨γ', δ', ε', hδ', hε', hδε', _, t', rfl, rfl⟩ (π.foa_hypothesis hπ)
  --   (hypothesis_injective_inflexible_of_mem_refl_trans_constrained H _
  --     (mem_refl_trans_constrained_of_mem_trans_constrained hL)),
  -- have lhs := (this C).map_near_litter N.fst.to_near_litter _
  --   (λ a h, h.elim (λ h, (h.2 h.1).elim) (λ h, (h.2 h.1).elim)),
  -- rw ← set_like.coe_set_eq at lhs,
  -- rw struct_perm.to_near_litter_perm_smul,
  -- rw ← (show _ = struct_perm.derivative C _ • (N.fst.to_near_litter : set atom), from lhs),
  -- clear lhs,
  refine congr_arg2 _ _ _,
  { have := weak_struct_approx.smul_to_near_litter_eq_of_precise,
    all_goals { sorry }, },
  { sorry, },
end

lemma trans_gen_struct_approx_coherent {c d : support_condition β} (H : foa_props hπ c d)
  {γ : Iic α} {δ ε : Iio α} (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
  (A : quiver.path (β : type_index) γ) (t : tangle δ)
  (ht : (inr (f_map (coe_ne_coe.mpr (coe_ne' hδε)) t).to_near_litter,
    (A.cons (coe_lt hε)).cons (bot_lt_coe _)) ∈ refl_trans_constrained c d) :
  (trans_gen_struct_approx H hδ A).refine.coherent t :=
begin
  split,
  { rintros ρ hρ γ' δ' ε' hδ' hε' hδε' B t' hL ⟨e, he, ih₁⟩ ih₂,
    simp only [path.comp_cons, complete_near_litter_map_eq, near_litter_completion_fst_eq,
      near_litter_hypothesis_eq, weak_struct_approx.refine_apply,
      weak_struct_approx.refine_litter_map, trans_gen_struct_approx_litter_map],
    have := π.litter_completion_of_inflexible_coe hπ (f_map _ t') _ (π.foa_hypothesis hπ)
      ⟨γ', δ', ε', hδ', hε', hδε', _, t', rfl, rfl⟩ _,
    refine (this.trans _).symm,
    { refine hypothesis_injective_inflexible_of_mem_refl_trans_constrained H _ _,
      exact mem_refl_trans_constrained_of_mem_trans_constrained hL, },
    refine congr_arg2 _ rfl _,
    rw [← inv_smul_eq_iff, smul_smul],
    refine (designated_support t').supports _ _,
    intros f hf,
    rw [mul_smul, inv_smul_eq_iff],
    refine prod.ext _ rfl,
    specialize ih₂ f hf,
    obtain ⟨a | N, C⟩ := f,
    { have ih₂ : (inl _, _) = (inl _, _) := ih₂,
      change inl _ = inl _,
      simp only [prod.mk.inj_iff, weak_struct_approx.refine_apply,
        eq_self_iff_true, and_true] at ih₂ ⊢,
      refine trans_gen_struct_approx_coherent_aux₁
        H hδ hε hδε A t ht hδ' hε' hδε' B t' hL e he ih₁ C a _ ih₂,
      exact relation.trans_gen.single (constrains.f_map hδ' hε' hδε' _ _ _ hf), },
    { have ih₂ : (inr _, _) = (inr _, _) := ih₂,
      change inr _ = inr _,
      simp only [prod.mk.inj_iff, weak_struct_approx.refine_apply,
        eq_self_iff_true, and_true] at ih₂ ⊢,
      refine trans_gen_struct_approx_coherent_aux₂
        H hδ hε hδε A t ht hδ' hε' hδε' B t' hL e he ih₁ C N _ ih₂,
      exact relation.trans_gen.single (constrains.f_map hδ' hε' hδε' _ _ _ hf), }, },
  { rintros ρ hρ γ' ε' hε' B a hL ih,
    sorry, },
end

lemma trans_gen_struct_approx_free {c d : support_condition β} (H : foa_props hπ c d)
  {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ)
  (A : quiver.path (β : type_index) γ) :
(show struct_approx (δ : Iic α), from (trans_gen_struct_approx H hδ A).refine.complete).free := sorry

lemma eq_of_hypothesised_allowable_smul_eq {c d : support_condition β} (H : foa_props hπ c d)
  {L₁ L₂ : litter} {A : extended_index β}
  (hcL₁ : (inr L₁.to_near_litter, A) ∈ refl_trans_constrained c d)
  (hcL₂ : (inr L₂.to_near_litter, A) ∈ refl_trans_constrained c d)
  (h : π.complete_litter_map hπ L₁ A = π.complete_litter_map hπ L₂ A)
  {γ : Iic α} {δ ε : Iio α}
  (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
  {B : path (β : type_index) γ} (hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _))
  {t₁ : tangle δ} (hL₁ : L₁ = f_map _ t₁)
  {t₂ : tangle δ} (hL₂ : L₂ = f_map _ t₂)
  (h : (π.hypothesised_allowable hπ
      ⟨γ, δ, ε, hδ, hε, hδε, B, t₁, hL₁, hA⟩
      (π.foa_hypothesis hπ)
      (hypothesis_injective_inflexible_of_mem_refl_trans_constrained H _ hcL₁) • t₁) =
    (π.hypothesised_allowable hπ
      ⟨γ, δ, ε, hδ, hε, hδε, B, t₂, hL₂, hA⟩
      (π.foa_hypothesis hπ)
      (hypothesis_injective_inflexible_of_mem_refl_trans_constrained H _ hcL₂) • t₂)) :
  t₁ = t₂ :=
begin
  have h₁ := weak_struct_approx.smul_eq_smul_tangle
    (hypothesised_weak_struct_approx (π.foa_hypothesis hπ)
      ⟨γ, δ, ε, hδ, hε, hδε, B, t₁, hL₁, hA⟩ _).refine
    (trans_gen_struct_approx H hδ B).refine
    (weak_struct_approx.refine_precise _) (weak_struct_approx.refine_precise _)
    t₁ _ _ (trans_gen_struct_approx_coherent H hδ hε hδε B t₁ _)
    (π.hypothesised_allowable_exactly_approximates hπ
      ⟨γ, δ, ε, hδ, hε, hδε, B, t₁, hL₁, hA⟩ (π.foa_hypothesis hπ) _)
    (π.allowable_of_weak_struct_approx_exactly_approximates hπ hδ B _ _),
  all_goals { sorry, },
end

lemma litter_injective_extends_coe_coe {c d : support_condition ↑β} (H : foa_props hπ c d)
  {L₁ L₂ : litter} {A : extended_index β}
  (hcL₁ : (inr L₁.to_near_litter, A) ∈ refl_trans_constrained c d)
  (hcL₂ : (inr L₂.to_near_litter, A) ∈ refl_trans_constrained c d)
  (h : π.complete_litter_map hπ L₁ A = π.complete_litter_map hπ L₂ A)
  (h₁ : inflexible_coe L₁ A) (h₂ : inflexible_coe L₂ A) :
  L₁ = L₂ :=
begin
  obtain ⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₁, hL₁, hA₁⟩ := h₁,
  obtain ⟨γ₂, δ₂, ε₂, hδ₂, hε₂, hδε₂, B₂, t₂, hL₂, hA₂⟩ := h₂,
  rw hA₁ at hA₂,
  cases subtype.coe_injective (coe_injective (path.obj_eq_of_cons_eq_cons hA₂)),
  cases subtype.coe_injective (coe_injective (path.obj_eq_of_cons_eq_cons
    (path.heq_of_cons_eq_cons hA₂).eq)),
  cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons hA₂).eq).eq,
  have := (complete_litter_map_eq_of_inflexible_coe hπ
      ⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₁, hL₁, hA₁⟩
      (hypothesis_injective_inflexible_of_mem_refl_trans_constrained H _ hcL₁)).symm.trans
    (h.trans (complete_litter_map_eq_of_inflexible_coe hπ
      ⟨γ₁, δ₂, ε₁, hδ₂, hε₁, hδε₂, B₁, t₂, hL₂, hA₁⟩
      (hypothesis_injective_inflexible_of_mem_refl_trans_constrained H _ hcL₂))),
  have := congr_arg litter.β this,
  cases subtype.coe_injective (coe_injective this),
  rw [hL₁, hL₂],
  refine congr_arg _ _,
  exact eq_of_hypothesised_allowable_smul_eq H hcL₁ hcL₂ h hδ₁ hε₁ hδε₁ hA₁ hL₁ hL₂
    (f_map_injective _ ‹_›),
end

lemma litter_injective_extends {c d : support_condition β} (H : foa_props hπ c d)
  {L₁ L₂ : litter} {A : extended_index β}
  (hcL₁ : (inr L₁.to_near_litter, A) ∈ refl_trans_constrained c d)
  (hcL₂ : (inr L₂.to_near_litter, A) ∈ refl_trans_constrained c d)
  (h : π.complete_litter_map hπ L₁ A = π.complete_litter_map hπ L₂ A) :
  L₁ = L₂ :=
begin
  by_cases h₁ : nonempty (inflexible_bot L₁ A);
  by_cases h₂ : nonempty (inflexible_bot L₂ A),
  { obtain ⟨⟨γ₁, ε₁, hγε₁, B₁, a₁, hL₁, hA₁⟩⟩ := h₁,
    obtain ⟨⟨γ₂, ε₂, hγε₂, B₂, a₂, hL₂, hA₂⟩⟩ := h₂,
    rw hA₁ at hA₂,
    cases subtype.coe_injective (coe_injective (path.obj_eq_of_cons_eq_cons hA₂)),
    cases subtype.coe_injective (coe_injective (path.obj_eq_of_cons_eq_cons
      (path.heq_of_cons_eq_cons hA₂).eq)),
    cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons hA₂).eq).eq,
    rw [complete_litter_map_eq_of_inflexible_bot ⟨γ₁, ε₁, hγε₁, B₁, a₁, hL₁, hA₁⟩,
      complete_litter_map_eq_of_inflexible_bot ⟨γ₁, ε₁, hγε₁, B₁, a₂, hL₂, hA₁⟩] at h,
    cases H.atom_injective _ _ _ _ _ (f_map_injective bot_ne_coe h),
    rw [hL₁, hL₂],
    { have := constrains.f_map_bot hγε₁ B₁ a₁,
      rw [← hL₁, ← hA₁] at this,
      exact trans_constrained_of_refl_trans_constrained_of_trans_constrains hcL₁
        (relation.trans_gen.single this), },
    { have := constrains.f_map_bot hγε₁ B₁ a₂,
      rw [← hL₂, ← hA₁] at this,
      exact trans_constrained_of_refl_trans_constrained_of_trans_constrains hcL₂
        (relation.trans_gen.single this), }, },
  { cases ne_of_inflexible_bot_of_not_inflexible_bot H h₁.some (λ h, h₂ ⟨h⟩) hcL₁ hcL₂ h, },
  { cases ne_of_inflexible_bot_of_not_inflexible_bot H h₂.some (λ h, h₁ ⟨h⟩) hcL₂ hcL₁ h.symm, },
  by_cases h₁' : nonempty (inflexible_coe L₁ A);
  by_cases h₂' : nonempty (inflexible_coe L₂ A),
  { exact litter_injective_extends_coe_coe H hcL₁ hcL₂ h h₁'.some h₂'.some, },
  { cases ne_of_inflexible_coe_of_not_inflexible H h₁'.some
      (λ h, h₂ ⟨h⟩) (λ h, h₂' ⟨h⟩) hcL₁ h, },
  { cases ne_of_inflexible_coe_of_not_inflexible H h₂'.some
      (λ h, h₁ ⟨h⟩) (λ h, h₁' ⟨h⟩) hcL₂ h.symm, },
  { rw [complete_litter_map_eq_of_flexible, complete_litter_map_eq_of_flexible,
      near_litter_approx.smul_eq_smul_litter] at h,
    exact h,
    rw [near_litter_approx.flexible_completion_litter_perm_domain_free _ _ _ (hπ A),
      mem_set_of, flexible_iff_not_inflexible_bot_coe],
    exact ⟨λ h, h₁ ⟨h⟩, λ h, h₁' ⟨h⟩⟩,
    rw [near_litter_approx.flexible_completion_litter_perm_domain_free _ _ _ (hπ A),
      mem_set_of, flexible_iff_not_inflexible_bot_coe],
    exact ⟨λ h, h₂ ⟨h⟩, λ h, h₂' ⟨h⟩⟩,
    exact λ h, h₂ ⟨h⟩,
    exact λ h, h₂' ⟨h⟩,
    exact λ h, h₁ ⟨h⟩,
    exact λ h, h₁' ⟨h⟩, },
end

-- lemma hypothesis_injective_inflexible_comp {L : litter} {A : extended_index β}
--   (γ : Iic α) (δ ε : Iio α)
--   (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
--   (C : path (δ : type_index) γ) (t : tangle δ) :
--   hypothesis_injective_inflexible (π.foa_hypothesis hπ)
--     ⟨γ, δ, ε, hδ, hε, hδε, (C.cons (coe_lt hδ)).comp C, t, rfl, rfl⟩ :=
-- begin
-- end

-- (map_flexible : ∀ (L : litter) B (hL₁ : (inr L.to_near_litter, B) ∈ inflexible_support h)
--   (hL₂ : flexible α L B),
--   flexible α (H.near_litter_image L.to_near_litter ((h.B.cons (coe_lt h.hδ)).comp B)
--     (by rwa [inflexible_support, ← h.hL, ← h.hA] at hL₁)).1 B)

/-

/-- The inductive hypothesis used to prove that the induced action generated in the freedom of
action theorem is lawful. This is to be proven by well-founded recursion on `c`. -/
structure foa_props (π : struct_approx β) (hπ : π.free) (c : support_condition β) : Prop :=
(atom_injective : ∀ a b (B : extended_index β),
  (relation.trans_gen (constrains α β)) ⟨inl a, B⟩ c →
  (relation.trans_gen (constrains α β)) ⟨inl b, B⟩ c →
  π.complete_atom_map hπ a B = π.complete_atom_map hπ b B → a = b)
(litter_injective : ∀ (L₁ L₂ : litter) (B : extended_index β),
  (relation.trans_gen (constrains α β)) ⟨inr L₁.to_near_litter, B⟩ c →
  (relation.trans_gen (constrains α β)) ⟨inr L₂.to_near_litter, B⟩ c →
  π.complete_litter_map hπ L₁ B = π.complete_litter_map hπ L₂ B → L₁ = L₂)

lemma eq_of_sublitter_bijection_apply_eq {π : near_litter_approx} {L₁ L₂ L₃ L₄ : litter} {a b} :
  ((π.largest_sublitter L₁).order_iso (π.largest_sublitter L₂) a : atom) =
  (π.largest_sublitter L₃).order_iso (π.largest_sublitter L₄) b →
  L₁ = L₃ → L₂ = L₄ → (a : atom) = b :=
begin
  rintros h₁ rfl rfl,
  simp only [subtype.coe_inj, embedding_like.apply_eq_iff_eq] at h₁,
  rw h₁,
end

/-- We show that injectivity of the atom map extends to atoms below the current support condition
`c`, given that certain properties hold for support conditions before `c`. -/
lemma atom_injective_extends {c : support_condition β} (H : π.foa_props hπ c)
  {a b : atom} {A : extended_index β}
  (hac : (relation.refl_trans_gen (constrains α β)) ⟨inl a, A⟩ c)
  (hbc : (relation.refl_trans_gen (constrains α β)) ⟨inl b, A⟩ c)
  (h : π.complete_atom_map hπ a A = π.complete_atom_map hπ b A) :
  a = b :=
begin
  by_cases ha : a ∈ (π A).atom_perm.domain;
  by_cases hb : b ∈ (π A).atom_perm.domain,
  { rw [complete_atom_map_eq_of_mem_domain ha, complete_atom_map_eq_of_mem_domain hb] at h,
    exact (π A).atom_perm.inj_on ha hb h, },
  { rw [complete_atom_map_eq_of_mem_domain ha, complete_atom_map_eq_of_not_mem_domain hb] at h,
    cases (π A).not_mem_domain_of_mem_largest_sublitter ((subtype.coe_eq_iff.mp h.symm).some)
      ((π A).atom_perm.map_domain ha), },
  { rw [complete_atom_map_eq_of_not_mem_domain ha, complete_atom_map_eq_of_mem_domain hb] at h,
    cases (π A).not_mem_domain_of_mem_largest_sublitter ((subtype.coe_eq_iff.mp h).some)
      ((π A).atom_perm.map_domain hb), },
  { rw [complete_atom_map_eq_of_not_mem_domain ha, complete_atom_map_eq_of_not_mem_domain hb] at h,
    have h₁ := (subtype.coe_eq_iff.mp h).some.1,
    have h₂ := (((π A).largest_sublitter b.1).order_iso
      ((π A).largest_sublitter (π.complete_litter_map hπ b.1 A))
      ⟨b, (π A).mem_largest_sublitter_of_not_mem_domain b hb⟩).prop.1,
    have := H.litter_injective _ _ _
      (relation.trans_gen.head' (constrains.atom a A) hac)
      (relation.trans_gen.head' (constrains.atom b A) hbc)
      (h₁.symm.trans h₂),
    have := eq_of_sublitter_bijection_apply_eq h this (by rw this),
    rw [set_like.coe_mk, set_like.coe_mk] at this,
    exact this, },
end

lemma eq_of_litter_map_inter_nonempty {c : support_condition β} (H : π.foa_props hπ c)
  {L₁ L₂ : litter} {A : extended_index β}
  (hL₁ : relation.trans_gen (constrains α β) (inr L₁.to_near_litter, A) c)
  (hL₂ : relation.trans_gen (constrains α β) (inr L₂.to_near_litter, A) c)
  (h : (((π.foa_hypothesis hπ).near_litter_image L₁.to_near_litter A hL₁ : set atom) ∩
    (π.foa_hypothesis hπ).near_litter_image L₂.to_near_litter A hL₂).nonempty) : ljnkafsdjhlksfd := sorry

lemma hypothesis_injective_inflexible_hypothesis {c : support_condition β} (H : π.foa_props hπ c)
  {L : litter} {A : extended_index β} (hL : inflexible_coe L A)
  (hL' : relation.trans_gen (constrains α β) (inr L.to_near_litter, A) c) :
  hypothesis_injective_inflexible (π.foa_hypothesis hπ) hL :=
begin
  constructor,
  { intros a b B ha hb h,
    refine H.atom_injective a b _ _ _ h,
    { rw [inflexible_support, ← hL.hL, ← hL.hA] at ha,
      exact relation.trans_gen.trans ha hL', },
    { rw [inflexible_support, ← hL.hL, ← hL.hA] at hb,
      exact relation.trans_gen.trans hb hL', }, },
  { intros L₁ L₂ B hL₁ hL₂ h,
    refine H.litter_injective L₁ L₂ _ _ _ _,
    {  }, },
end

/-- The complete litter map sends flexible litters to flexible litters, even when the flexibility
condition is tested along a lower path. -/
lemma map_flexible {L : litter} {γ : Iio α} (B : path (β : type_index) γ) (C : extended_index γ)
  (hL : flexible α L C) : flexible α (π.complete_litter_map hπ L (B.comp C)) C :=
begin
  by_cases flexible α L (B.comp C),
  { rw complete_litter_map_eq_of_flexible' h,
    have hdom := near_litter_approx.flexible_completion_litter_perm_domain_free
      α (π (B.comp C)) (B.comp C) (hπ _),
    have := local_perm.map_domain _,
    rw hdom at this,
    exact flexible_of_comp_flexible (this h), },
  contrapose hL,
  rw not_flexible_iff at h hL ⊢,
  obtain (⟨⟨h⟩⟩ | ⟨⟨h⟩⟩) := inflexible_bot_or_inflexible_coe_of_inflexible h,
  { rw complete_litter_map_eq_of_inflexible_bot h at hL,
    rw inflexible_iff at hL ⊢,
    obtain (⟨γ, δ, ε, hδ, hε, hδε, A, t, hL, rfl⟩ | ⟨γ₁, ε₁, hε₁, A₁, a₁, hL₁, hA₁⟩) := hL,
    { have := f_map_β _ _,
      rw hL at this,
      rw f_map_β at this,
      cases this, },
    obtain ⟨γ₂, ε₂, hε₂, A₂, a₂, hL₂, hA₂⟩ := h,
    { have := f_map_γ _ _,
      rw hL₁ at this,
      rw [f_map_γ, subtype.coe_injective.eq_iff] at this,
      subst this,
      have := f_map_injective _ hL₁,
      subst this,
      exact or.inr ⟨γ₁, ε₂, hε₁, A₁, a₂, hL₂, hA₁⟩, }, },
  { rw complete_litter_map_eq_of_inflexible_coe hπ h at hL,
    rw inflexible_iff at hL ⊢,
    obtain (⟨γ, δ, ε, hδ, hε, hδε, A, t, hL, rfl⟩ | ⟨γ₁, ε₁, hε₁, A₁, a₁, hL₁, hA₁⟩) := hL,
    { have := f_map_β _ _,
      rw hL at this,
      rw f_map_β at this,
      cases this, },
    obtain ⟨γ₂, ε₂, hε₂, A₂, a₂, hL₂, hA₂⟩ := h,
    { have := f_map_γ _ _,
      rw hL₁ at this,
      rw [f_map_γ, subtype.coe_injective.eq_iff] at this,
      subst this,
      have := f_map_injective _ hL₁,
      subst this,
      exact or.inr ⟨γ₁, ε₂, hε₁, A₁, a₂, hL₂, hA₁⟩, }, },
end

-- TODO: This lemma is stated badly.
/-- Inflexible supports created from inflexible litters in other inflexible supports are nested. -/
lemma hypothesis_injective_inflexible_comp {L : litter} {A : extended_index β}
  (h : inflexible_coe L A)
  (hH : hypothesis_injective_inflexible (π.foa_hypothesis hπ) h)
  (γ : Iic α) (δ ε : Iio α)
  (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
  (C : path (h.δ : type_index) γ) (t : tangle δ)
  (hL : (inr (f_map (subtype.coe_injective.ne (Iio.coe_injective.ne hδε)) t).to_near_litter,
    (C.cons $ coe_lt hε).cons (bot_lt_coe _)) ∈ inflexible_support h):
  hypothesis_injective_inflexible (π.foa_hypothesis hπ) ⟨γ, δ, ε, hδ, hε, hδε,
    (h.B.cons (coe_lt h.hδ)).comp C, t, rfl, rfl⟩ :=
begin
  rw inflexible_support at hL,
  constructor,
  { intros a b B ha hb hab,
    refine hH.atom_map_injective a b ((C.cons $ coe_lt hδ).comp B) _ _ _,
    { -- TODO: Factor out this block.
      simp only [inflexible_support, preimage_set_of_eq],
      refine relation.trans_gen.trans _ hL,
      rw [← path.comp_assoc, path.comp_cons],
      exact ha, },
    { simp only [inflexible_support, preimage_set_of_eq],
      refine relation.trans_gen.trans _ hL,
      rw [← path.comp_assoc, path.comp_cons],
      exact hb, },
    { simp only [foa_hypothesis_atom_image],
      rw [← path.comp_assoc, path.comp_cons],
      exact hab, }, },
  { intros L₁ L₂ B hL₁ hL₂ h,
    refine hH.litter_map_injective L₁ L₂ ((C.cons $ coe_lt hδ).comp B) _ _ _,
    { simp only [inflexible_support, preimage_set_of_eq],
      refine relation.trans_gen.trans _ hL,
      rw [← path.comp_assoc, path.comp_cons],
      exact hL₁, },
    { simp only [inflexible_support, preimage_set_of_eq],
      refine relation.trans_gen.trans _ hL,
      rw [← path.comp_assoc, path.comp_cons],
      exact hL₂, },
    { simp only [foa_hypothesis_near_litter_image] at h ⊢,
      rw [← path.comp_assoc, path.comp_cons],
      exact h, }, },
  { intros a L' B ha hL',
    rw hH.atom_mem a L' ((C.cons $ coe_lt hδ).comp B),
    { simp only [foa_hypothesis_atom_image, foa_hypothesis_near_litter_image],
      rw [← path.comp_assoc, path.comp_cons], },
    { simp only [inflexible_support, preimage_set_of_eq],
      refine relation.trans_gen.trans _ hL,
      rw [← path.comp_assoc, path.comp_cons],
      exact ha, },
    { simp only [inflexible_support, preimage_set_of_eq],
      refine relation.trans_gen.trans _ hL,
      rw [← path.comp_assoc, path.comp_cons],
      exact hL', }, },
  { have := hH.map_flexible,
    -- asdlkfjasdl;kfj
    intros L' B hL₁ hL₂,
    exact map_flexible _ B hL₂, },
end

lemma hypothesised_weak_struct_approx_coherent {L : litter} {A : extended_index β}
  (h : inflexible_coe L A) (hH : hypothesis_injective_inflexible (π.foa_hypothesis hπ) h) :
  (hypothesised_weak_struct_approx (π.foa_hypothesis hπ) h hH).refine.coherent :=
begin
  -- rw litter_perm_below,
  constructor,
  /- { intros L' B hL' hflex,
    simp only [hypothesised_weak_struct_approx_litter_map, foa_hypothesis_near_litter_image,
      complete_near_litter_map_eq, near_litter_completion, near_litter_hypothesis_eq,
      weak_struct_approx.refine_apply, weak_struct_approx.refine_litter_map],
    simp only [near_litter_approx.flexible_completion_litter_perm_domain'] at hflex,
    rw litter_completion_of_flexible,
    refl,
    cases hflex,
    { exact hπ _ _ hflex, },
    sorry { exact hflex, }, }, -/
  sorry { intros ρ hρ γ δ ε hδ hε hδε C t hL ih,
    simp only [hypothesised_weak_struct_approx_litter_map, path.comp_cons,
      foa_hypothesis_near_litter_image, complete_near_litter_map_eq,
      near_litter_completion_fst_eq, near_litter_hypothesis_eq],
    have := litter_completion_of_inflexible_coe _ _ _ _ _ ⟨γ, δ, ε, hδ, hε, hδε, _, t, rfl, rfl⟩ _,
    refine (this.trans _).symm,
    { exact hypothesis_injective_inflexible_comp h hH hρ γ δ ε hδ hε hδε C t hL ih, },
    refine congr_arg2 _ rfl _,
    rw [← inv_smul_eq_iff, smul_smul],
    refine (designated_support t).supports _ _,
    intros c hc,
    rw [mul_smul, inv_smul_eq_iff],
    have := ih c hc,
    simp only at this ⊢,
    sorry, },
  sorry { intros ρ hρ γ ε hε C a hL ih,
    simp only [hypothesised_weak_struct_approx_litter_map, path.comp_cons,
      foa_hypothesis_near_litter_image, complete_near_litter_map_eq],
    rw [ih, weak_near_litter_approx.atom_map_or_else_of_dom, near_litter_completion_fst_eq],
    have := litter_completion_of_inflexible_bot _ _ _ _ _ ⟨γ,  ε, hε, _, a, rfl, rfl⟩,
    refine (this.trans _).symm,
    { refine relation.trans_gen.trans _ hL,
      exact relation.trans_gen.single (constrains.f_map_bot _ _ _), },
    { refl, }, },
end

def trans_gen_support (c : support_condition β) {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ)
  (A : quiver.path (β : type_index) γ) : set (support_condition δ) :=
(λ c, (c.1, (A.cons (coe_lt hδ)).comp c.2)) ⁻¹' {d | relation.trans_gen (constrains α β) d c}

lemma trans_gen_support_small (c : support_condition β) {γ : Iic α} {δ : Iio α}
  (hδ : (δ : Λ) < γ) (A : quiver.path (β : type_index) γ) :
  small (trans_gen_support c hδ A) :=
begin
  have := reduction_small' α (small_singleton c),
  simp only [mem_singleton_iff, exists_prop, exists_eq_left] at this,
  refine small.preimage _ (small.mono _ this),
  { intros c d h,
    simp only [prod.mk.inj_iff, path.comp_inj_right] at h,
    exact prod.ext h.1 h.2, },
  { intros d hd,
    exact hd.to_refl, },
end

noncomputable def trans_gen_struct_approx {c : support_condition β} (H : π.foa_props hπ c)
  {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ)
  (A : quiver.path (β : type_index) γ) : weak_struct_approx δ :=
λ B, {
  atom_map := λ a, {
    dom := relation.trans_gen (constrains α β)
      (inl a, (A.cons (coe_lt hδ)).comp B) c,
    get := λ ha, π.complete_atom_map hπ a ((A.cons (coe_lt hδ)).comp B)
  },
  litter_map := λ L, {
    dom := relation.trans_gen (constrains α β)
      (inr L.to_near_litter, (A.cons (coe_lt hδ)).comp B) c,
    get := λ hL, π.complete_near_litter_map hπ L.to_near_litter ((A.cons (coe_lt hδ)).comp B)
  },
  atom_map_dom_small := begin
    refine small.image_subset (λ a, (inl a, B)) _ (trans_gen_support_small c hδ A) _,
    { intros a b h,
      simp only [prod.mk.inj_iff, eq_self_iff_true, and_true] at h,
      exact h, },
    { rintros _ ⟨a, ha, rfl⟩,
      exact ha, },
  end,
  litter_map_dom_small := begin
    refine small.image_subset (λ L, (inr L.to_near_litter, B)) _ (trans_gen_support_small c hδ A) _,
    { intros L₁ L₂ h,
      simp only [prod.mk.inj_iff, eq_self_iff_true, and_true,
        litter.to_near_litter_injective.eq_iff] at h,
      exact h, },
    { rintros _ ⟨L, hL, rfl⟩,
      exact hL, },
  end,
  atom_map_injective := λ a b, H.atom_injective a b _,
  litter_map_injective := λ L₁ L₂ hL₁ hL₂ h, H.litter_injective L₁ L₂ _ hL₁ hL₂ sorry,
  atom_mem := λ a ha L hL, sorry,
}

lemma trans_gen_struct_approx_coherent {c : support_condition β} (H : π.foa_props hπ c)
  {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ)
  (A : quiver.path (β : type_index) γ) :
  (trans_gen_struct_approx H hδ A).refine.coherent :=
sorry

lemma trans_gen_struct_approx_free {c : support_condition β} (H : π.foa_props hπ c)
  {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ)
  (A : quiver.path (β : type_index) γ) :
(show struct_approx (δ : Iic α), from (trans_gen_struct_approx H hδ A).refine.complete).free := sorry

/-
noncomputable def support_map_union {π : struct_approx β} (hπ) {γ : Iic α} {δ ε : Iio α}
  {B : path (β : type_index) γ} {t₁ t₂ : tangle δ} {L₁ L₂ A} (hδ hε hδε hL₁ hL₂ hA) :
  support_map δ := {
  carrier := inflexible_support (⟨γ, δ, ε, hδ, hε, hδε, B, t₁, hL₁, hA⟩ : inflexible_coe L₁ A) ∪
    inflexible_support (⟨γ, δ, ε, hδ, hε, hδε, B, t₂, hL₂, hA⟩ : inflexible_coe L₂ A),
  small := small.union (inflexible_support_small _) (inflexible_support_small _),
  atom_image := λ a C h, π.complete_atom_map hπ a ((B.cons $ coe_lt hδ).comp C),
  near_litter_image := λ N C h, π.complete_near_litter_map hπ N
    ((B.cons $ coe_lt hδ).comp C),
}

lemma le_support_map_union {π : struct_approx β} (hπ : π.free) {γ : Iic α} {δ ε : Iio α}
  {B : path (β : type_index) γ} {t₁ t₂ : tangle δ} {L₁ L₂ A} (hδ) (hε : (ε : Λ) < γ) (hδε)
  (hL₁ : L₁ = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t₁)
  (hL₂ : L₂ = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t₂)
  (hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _)) :
  inflexible_support_map (π.foa_hypothesis hπ)
    (⟨γ, δ, ε, hδ, hε, hδε, B, t₁, hL₁, hA⟩ : inflexible_coe L₁ A) ≤
    support_map_union hπ hδ hε hδε hL₁ hL₂ hA :=
⟨subset_union_left _ _, λ a B ha, rfl, λ N B hN, rfl⟩

lemma support_map_union_symm {π : struct_approx β} (hπ : π.free) {γ : Iic α} {δ ε : Iio α}
  {B : path (β : type_index) γ} {t₁ t₂ : tangle δ} {L₁ L₂ A} (hδ) (hε : (ε : Λ) < γ) (hδε)
  (hL₁ : L₁ = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t₁)
  (hL₂ : L₂ = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t₂)
  (hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _)) :
  support_map_union hπ hδ hε hδε hL₁ hL₂ hA = support_map_union hπ hδ hε hδε hL₂ hL₁ hA :=
begin
  rw [support_map_union, support_map_union],
  simp only,
  refine ⟨_, _, _⟩,
  { rw union_comm, },
  { ext, refl, intros a b h, cases h,
    ext, refl, intros A A' h, cases h,
    ext, rw union_comm, intros b b' h, refl, },
  { ext, refl, intros a b h, cases h,
    ext, refl, intros A A' h, cases h,
    ext, rw union_comm, intros b b' h, refl, },
end

lemma support_map_union_free {π : struct_approx β} (hπ : π.free) {γ : Iic α} {δ ε : Iio α}
  {B : path (β : type_index) γ} {t₁ t₂ : tangle δ} {L₁ L₂ A} (hδ) (hε : (ε : Λ) < γ) (hδε)
  (hL₁ : L₁ = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t₁)
  (hL₂ : L₂ = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t₂)
  (hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _)) :
  (show struct_approx (δ : Iic α), from supported_action (support_map_union hπ hδ hε hδε hL₁ hL₂ hA)
    (λ (C : extended_index δ), π ((B.cons $ coe_lt hδ).comp C))).free :=
λ C L, or.rec (flexible_of_comp_flexible ∘ hπ _ L) and.left

-- TODO: Rename the following few lemmas.

lemma atom_image_inj_on {π : struct_approx β} (hπ : π.free)
  {c : support_condition β} (H : π.foa_props hπ c) {γ : Iic α} {δ ε : Iio α}
  {B : path (β : type_index) γ} {t : tangle δ} {L A} (hδ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
  (hL : L = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t)
  (hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _))
  (hcL : (relation.refl_trans_gen (constrains α β)) ⟨inr L.to_near_litter, A⟩ c) (C a b ha hb)
  (hab : (inflexible_support_map (π.foa_hypothesis hπ)
    ⟨γ, δ, ε, hδ, hε, hδε, B, t, hL, hA⟩).atom_image a C ha =
  (inflexible_support_map (π.foa_hypothesis hπ)
    ⟨γ, δ, ε, hδ, hε, hδε, B, t, hL, hA⟩).atom_image b C hb) :
  a = b :=
begin
  unfold inflexible_support_map at hab,
  simp only [foa_hypothesis_atom_image] at hab,
  refine H.atom_injective _ _ _ _ _ hab,
  { exact relation.trans_gen.trans_left ha (by rw [hL, hA] at hcL; exact hcL), },
  { exact relation.trans_gen.trans_left hb (by rw [hL, hA] at hcL; exact hcL), },
end

lemma near_litter_image_inj_on {π : struct_approx β} (hπ : π.free)
  {c : support_condition β} (H : π.foa_props hπ c)
  (A : extended_index β) (L₁ L₂ : litter)
  (hcL₁ : (relation.trans_gen (constrains α β)) ⟨inr L₁.to_near_litter, A⟩ c)
  (hcL₂ : (relation.trans_gen (constrains α β)) ⟨inr L₂.to_near_litter, A⟩ c)
  (hL : ((π.complete_near_litter_map hπ L₁.to_near_litter A : set atom) ∩
    π.complete_near_litter_map hπ L₂.to_near_litter A).nonempty) :
  L₁ = L₂ :=
begin
  obtain ⟨a, ha₁, ha₂⟩ := hL,
  simp only [complete_near_litter_map_eq] at ha₁ ha₂,
  obtain ⟨ha₁ | ha₁, ha₃⟩ := ha₁;
  obtain ⟨ha₂ | ha₂, ha₄⟩ := ha₂,
  { have := eq_of_mem_litter_set_of_mem_litter_set
      (sublitter.subset _ ha₁) (sublitter.subset _ ha₂),
    simp only [near_litter_hypothesis_eq, near_litter_approx.largest_sublitter_litter] at this,
    refine H.litter_injective L₁ L₂ A hcL₁ hcL₂ _,
    rw [complete_litter_map_eq, complete_litter_map_eq],
    exact this, },
  { obtain ⟨b, hb, rfl⟩ := ha₂,
    have : b ∈ (π A).atom_perm.domain,
    -- TODO: Factor out this block.
    { contrapose! hb,
      intro h,
      simp only [litter.coe_to_near_litter, litter.to_near_litter_fst,
        near_litter_approx.coe_largest_sublitter, sdiff_sdiff_right_self, inf_eq_inter,
        mem_inter_iff, mem_litter_set] at h,
      exact hb h.2, },
    have := (π A).atom_perm.map_domain this,
    cases near_litter_approx.not_mem_domain_of_mem_largest_sublitter _ ha₁ this, },
  { obtain ⟨b, hb, rfl⟩ := ha₁,
    have : b ∈ (π A).atom_perm.domain,
    { contrapose! hb,
      intro h,
      simp only [litter.coe_to_near_litter, litter.to_near_litter_fst,
        near_litter_approx.coe_largest_sublitter, sdiff_sdiff_right_self, inf_eq_inter,
        mem_inter_iff, mem_litter_set] at h,
      exact hb h.2, },
    have := (π A).atom_perm.map_domain this,
    cases near_litter_approx.not_mem_domain_of_mem_largest_sublitter _ ha₂ this, },
  { obtain ⟨b, hb₁, hb₂⟩ := ha₁,
    obtain ⟨c, hc₁, hc₂⟩ := ha₂,
    have hb : b ∈ (π A).atom_perm.domain,
    { contrapose! hb₁,
      intro h,
      simp only [litter.coe_to_near_litter, litter.to_near_litter_fst,
        near_litter_approx.coe_largest_sublitter, sdiff_sdiff_right_self, inf_eq_inter,
        mem_inter_iff, mem_litter_set] at h,
      exact hb₁ h.2, },
    have hc : c ∈ (π A).atom_perm.domain,
    { contrapose! hc₁,
      intro h,
      simp only [litter.coe_to_near_litter, litter.to_near_litter_fst,
        near_litter_approx.coe_largest_sublitter, sdiff_sdiff_right_self, inf_eq_inter,
        mem_inter_iff, mem_litter_set] at h,
      exact hc₁ h.2, },
    rw ← hc₂ at hb₂,
    cases (π A).atom_perm.inj_on hb hc hb₂,
    simp only [litter.coe_to_near_litter, litter.to_near_litter_fst, mem_diff,
      mem_litter_set] at hb₁ hc₁,
    exact hb₁.1.symm.trans hc₁.1, },
end

lemma inflexible_support_map_injective {π : struct_approx β} (hπ : π.free)
  {c : support_condition β} (H : π.foa_props hπ c) {γ : Iic α} {δ ε : Iio α}
  {B : path (β : type_index) γ} {t : tangle δ} {L A} (hδ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
  (hL : L = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t)
  (hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _))
  (hcL : (relation.refl_trans_gen (constrains α β)) ⟨inr L.to_near_litter, A⟩ c) (C) :
  (inflexible_support_map (π.foa_hypothesis hπ) ⟨γ, δ, ε, hδ, hε, hδε, B, t, hL, hA⟩).injective C :=
begin
  split,
  { exact atom_image_inj_on hπ H hδ hε hδε hL hA hcL C, },
  intros L₁ L₂ hL₁ hL₂ hL₁₂,
  refine near_litter_image_inj_on hπ H _ L₁ L₂
    (relation.trans_gen.trans_left hL₁ _) (relation.trans_gen.trans_left hL₂ _) hL₁₂;
  rwa [← hL, ← hA],
end

lemma support_map_union_injective {π : struct_approx β} (hπ : π.free)
  {c : support_condition β} (H : π.foa_props hπ c) {γ : Iic α} {δ ε : Iio α}
  {B : path (β : type_index) γ} {t₁ t₂ : tangle δ} {L₁ L₂ A} (hδ) (hε : (ε : Λ) < γ) (hδε)
  (hL₁ : L₁ = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t₁)
  (hL₂ : L₂ = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t₂)
  (hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _))
  (hcL₁ : relation.refl_trans_gen (constrains α β) (inr L₁.to_near_litter, A) c)
  (hcL₂ : relation.refl_trans_gen (constrains α β) (inr L₂.to_near_litter, A) c) :
  ∀ C, (support_map_union hπ hδ hε hδε hL₁ hL₂ hA).injective C :=
begin
  intro C,
  refine ⟨_, _⟩,
  { rintro a b (ha | ha) (hb | hb) h;
    refine H.atom_injective _ _ _
      (relation.trans_gen.trans_left ha _) (relation.trans_gen.trans_left hb _) h;
    simpa only [← hL₁, ← hL₂, ← hA], },
  { rintro L₃ L₄ (hL₃ | hL₃) (hL₄ | hL₄) h;
    refine near_litter_image_inj_on hπ H _ L₃ L₄
      (relation.trans_gen.trans_left hL₃ _) (relation.trans_gen.trans_left hL₄ _) h;
    simpa only [← hL₁, ← hL₂, ← hA], },
end

lemma supported_action_atom_map_eq {π : struct_approx β} (hπ : π.free)
  {c : support_condition β} (H : π.foa_props hπ c) {γ : Iic α} {δ ε : Iio α}
  {B : path (β : type_index) γ} {t : tangle δ} {L A} (hδ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
  (hL : L = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t)
  (hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _))
  (hcL : (relation.refl_trans_gen (constrains α β)) ⟨inr L.to_near_litter, A⟩ c) (C) :
  supported_action_atom_map
    (inflexible_support_map (π.foa_hypothesis hπ) ⟨γ, δ, ε, hδ, hε, hδε, B, t, hL, hA⟩)
    C =
  local_perm.complete
    (supported_action_atom_map_core
      (inflexible_support_map (π.foa_hypothesis hπ) ⟨γ, δ, ε, hδ, hε, hδε, B, t, hL, hA⟩) C)
    (supported_action_atom_map_core_domain _ C)
    (litter_set $ sandbox_litter _ C)
    (mk_supported_action_atom_map_domain _ C)
    (le_of_le_of_eq κ_regular.aleph_0_le (mk_litter_set _).symm)
    (supported_action_atom_map_domain_disjoint _ C)
    (supported_action_inj_on _ C (inflexible_support_map_injective hπ H hδ hε hδε hL hA hcL C)) :=
by rw [supported_action_atom_map, dif_pos];
  exact ⟨atom_image_inj_on hπ H hδ hε hδε hL hA hcL C,
    near_litter_image_inj_on hπ H hδ hε hδε hL hA hcL C⟩

lemma support_map_union_supported {π : struct_approx β} (hπ : π.free)
  {c : support_condition β} (H : π.foa_props hπ c) {L₁ L₂ A} (γ : Iic α) (δ ε : Iio α)
  (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε) (B : path (β : type_index) γ)
  (t₁ : tangle δ) (hL₁ : L₁ = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t₁)
  (hcL₁ : relation.refl_trans_gen (constrains α β) (inr L₁.to_near_litter, A) c)
  (hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _))
  (t₂ : tangle δ) (hL₂ : L₂ = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t₂)
  (hcL₂ : relation.refl_trans_gen (constrains α β) (inr L₂.to_near_litter, A) c) :
  support_map_supported π hπ ⟨γ, δ, ε, hδ, hε, hδε, B, t₁, hL₁, hA⟩
    (π.foa_hypothesis hπ) _ (support_map_union_free hπ hδ hε hδε hL₁ hL₂ hA) :=
begin
  intros L C d hd₁ hd₂ h,
  dsimp only at *,
  have hbanned : banned_litter
    (inflexible_support_map (π.foa_hypothesis hπ) ⟨γ, δ, ε, hδ, hε, hδε, B, t₁, hL₁, hA⟩) C L,
  { refine banned_litter.support_litter _ _,
    exact relation.trans_gen.tail' (refl_trans_gen_constrains_comp hd₂ _)
      (constrains.f_map hδ hε hδε _ _ _ hd₁), },
  have hbanned' : banned_litter (support_map_union hπ hδ hε hδε hL₁ hL₂ hA) C L,
  { exact support_map.banned_litter_of_le hbanned (le_support_map_union _ _ _ _ _ _ _), },
  sorry,
end
-/

lemma ne_of_inflexible_bot_of_not_inflexible_bot {c : support_condition β} (H : π.foa_props hπ c)
  {L₁ L₂ : litter} {A : extended_index β}
  (hL₁ : inflexible_bot L₁ A) (hL₂ : inflexible_bot L₂ A → false) :
  π.complete_litter_map hπ L₁ A ≠ π.complete_litter_map hπ L₂ A :=
begin
  obtain ⟨γ₁, ε₁, hγε₁, B₁, a₁, hL₁, hA₁⟩ := hL₁,
  rw complete_litter_map_eq_of_inflexible_bot ⟨γ₁, ε₁, hγε₁, B₁, a₁, hL₁, hA₁⟩,
  by_cases h₂ : nonempty (inflexible_coe L₂ A),
  { obtain ⟨⟨γ₂, δ₂, ε₂, hδ₂, hε₂, hδε₂, B₂, t₂, hL₂, hB₂⟩⟩ := h₂,
    rw complete_litter_map_eq_of_inflexible_coe hπ ⟨γ₂, δ₂, ε₂, hδ₂, hε₂, hδε₂, B₂, t₂, hL₂, hB₂⟩,
    intro h,
    have := congr_arg litter.β h,
    simp only [f_map, bot_ne_coe] at this,
    exact this,
    sorry, },
  { have flex := flexible_iff_not_inflexible_bot_coe.mpr ⟨hL₂, λ h, h₂ ⟨h⟩⟩,
    rw complete_litter_map_eq_of_flexible hL₂ (λ h, h₂ ⟨h⟩),
    intro h,
    have : L₂ ∈ ((π A).flexible_completion α A).litter_perm.domain :=
      by rwa near_litter_approx.flexible_completion_litter_perm_domain_free _ _ _ (hπ A),
    have := ((π A).flexible_completion α A).litter_perm.map_domain this,
    rw [near_litter_approx.smul_litter_eq, ← h,
      near_litter_approx.flexible_completion_litter_perm_domain_free _ _ _ (hπ A)] at this,
    refine this _,
    have := inflexible.mk_bot hγε₁ B₁ _,
    rw ← hA₁ at this,
    exact this, },
end

lemma ne_of_inflexible_coe_of_not_inflexible {c : support_condition β} (H : π.foa_props hπ c)
  {L₁ L₂ : litter} {A : extended_index β}
  (hL₁ : inflexible_coe L₁ A)
  (hL₂ : inflexible_bot L₂ A → false) (hL₂' : inflexible_coe L₂ A → false) :
  π.complete_litter_map hπ L₁ A ≠ π.complete_litter_map hπ L₂ A :=
begin
  rw complete_litter_map_eq_of_inflexible_coe hπ hL₁,
  have flex := flexible_iff_not_inflexible_bot_coe.mpr ⟨hL₂, hL₂'⟩,
  rw complete_litter_map_eq_of_flexible hL₂ hL₂',
  intro h,
  have : L₂ ∈ ((π A).flexible_completion α A).litter_perm.domain :=
    by rwa near_litter_approx.flexible_completion_litter_perm_domain_free _ _ _ (hπ A),
  have := ((π A).flexible_completion α A).litter_perm.map_domain this,
  rw [near_litter_approx.smul_litter_eq, ← h,
    near_litter_approx.flexible_completion_litter_perm_domain_free _ _ _ (hπ A)] at this,
  refine this _,
  obtain ⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₁, hL₁, hA₁⟩ := hL₁,
  have := inflexible.mk_coe hδ₁ hε₁ hδε₁ B₁ _,
  rw ← hA₁ at this,
  exact this,
  sorry,
end

lemma litter_injective_extends {c : support_condition β} (H : π.foa_props hπ c)
  {L₁ L₂ : litter} {A : extended_index β}
  (hcL₁ : (relation.refl_trans_gen (constrains α β)) ⟨inr L₁.to_near_litter, A⟩ c)
  (hcL₂ : (relation.refl_trans_gen (constrains α β)) ⟨inr L₂.to_near_litter, A⟩ c)
  (h : π.complete_litter_map hπ L₁ A = π.complete_litter_map hπ L₂ A) :
  L₁ = L₂ :=
begin
  by_cases h₁ : nonempty (inflexible_bot L₁ A);
  by_cases h₂ : nonempty (inflexible_bot L₂ A),
  { obtain ⟨⟨γ₁, ε₁, hγε₁, B₁, a₁, hL₁, hA₁⟩⟩ := h₁,
    obtain ⟨⟨γ₂, ε₂, hγε₂, B₂, a₂, hL₂, hA₂⟩⟩ := h₂,
    rw hA₁ at hA₂,
    cases subtype.coe_injective (coe_injective (path.obj_eq_of_cons_eq_cons hA₂)),
    cases subtype.coe_injective (coe_injective (path.obj_eq_of_cons_eq_cons
      (path.heq_of_cons_eq_cons hA₂).eq)),
    cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons hA₂).eq).eq,
    rw [complete_litter_map_eq_of_inflexible_bot ⟨γ₁, ε₁, hγε₁, B₁, a₁, hL₁, hA₁⟩,
      complete_litter_map_eq_of_inflexible_bot ⟨γ₁, ε₁, hγε₁, B₁, a₂, hL₂, hA₁⟩] at h,
    cases H.atom_injective _ _ _ _ _ (f_map_injective bot_ne_coe h),
    rw [hL₁, hL₂],
    { have := constrains.f_map_bot hγε₁ B₁ a₁,
      rw [← hL₁, ← hA₁] at this,
      exact relation.trans_gen.trans_left (relation.trans_gen.single this) hcL₁, },
    { have := constrains.f_map_bot hγε₁ B₁ a₂,
      rw [← hL₂, ← hA₁] at this,
      exact relation.trans_gen.trans_left (relation.trans_gen.single this) hcL₂, }, },
  { cases ne_of_inflexible_bot_of_not_inflexible_bot H h₁.some (λ h, h₂ ⟨h⟩) h, },
  { cases ne_of_inflexible_bot_of_not_inflexible_bot H h₂.some (λ h, h₁ ⟨h⟩) h.symm, },
  by_cases h₁' : nonempty (inflexible_coe L₁ A);
  by_cases h₂' : nonempty (inflexible_coe L₂ A),
  { obtain ⟨⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₁, hL₁, hA₁⟩⟩ := h₁',
    obtain ⟨⟨γ₂, δ₂, ε₂, hδ₂, hε₂, hδε₂, B₂, t₂, hL₂, hA₂⟩⟩ := h₂',
    rw hA₁ at hA₂,
    cases subtype.coe_injective (coe_injective (path.obj_eq_of_cons_eq_cons hA₂)),
    cases subtype.coe_injective (coe_injective (path.obj_eq_of_cons_eq_cons
      (path.heq_of_cons_eq_cons hA₂).eq)),
    cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons hA₂).eq).eq,
    have h := (complete_litter_map_eq_of_inflexible_coe hπ
        ⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₁, hL₁, hA₁⟩ _).symm.trans
      (h.trans (complete_litter_map_eq_of_inflexible_coe hπ
        ⟨γ₁, δ₂, ε₁, hδ₂, hε₁, hδε₂, B₁, t₂, hL₂, hA₁⟩ _)),
    have := congr_arg litter.β h,
    cases subtype.coe_injective (coe_injective this),
    rw [hL₁, hL₂],
    refine congr_arg _ _,
    have h₁ := weak_struct_approx.smul_eq_smul_tangle
      (hypothesised_weak_struct_approx (π.foa_hypothesis hπ)
        ⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₁, hL₁, hA₁⟩ _).refine
      (trans_gen_struct_approx H hδ₁ B₁).refine
      (weak_struct_approx.refine_precise _) (weak_struct_approx.refine_precise _)
      (hypothesised_weak_struct_approx_coherent _ _)
      (trans_gen_struct_approx_coherent H hδ₁ B₁)
      _
      (hypothesised_allowable_exactly_approximates _ _ _ _ _)
      (allowable_of_weak_struct_approx_exactly_approximates _ _ _ _ _ _)
      t₁ _,
    have h₂ := weak_struct_approx.smul_eq_smul_tangle
      (hypothesised_weak_struct_approx (π.foa_hypothesis hπ)
        ⟨γ₁, δ₁, ε₁, hδ₁, hε₂, hδε₁, B₁, t₂, hL₂, hA₁⟩ _).refine
      (trans_gen_struct_approx H hδ₁ B₁).refine
      (weak_struct_approx.refine_precise _) (weak_struct_approx.refine_precise _)
      (hypothesised_weak_struct_approx_coherent _ _)
      (trans_gen_struct_approx_coherent H hδ₁ B₁)
      _
      (hypothesised_allowable_exactly_approximates _ _ _ _ _)
      (allowable_of_weak_struct_approx_exactly_approximates _ _ _ _ _ _)
      t₂ _,
    have := (h₁.symm.trans (f_map_injective (coe_ne_coe.mpr $ coe_ne' hδε₁) h)).trans h₂,
    rw smul_left_cancel_iff at this,
    exact this,
    exact hπ,
    exact trans_gen_struct_approx_free H hδ₁ B₁,
    all_goals { sorry, },
    /- sorry,
    sorry,
    { intros B L hL,
      rw [litter_perm_below, near_litter_approx.flexible_completion_litter_perm_domain'],
      exact or.inr hL, },
    sorry,
    { intros B L hL,
      rw [litter_perm_below, near_litter_approx.flexible_completion_litter_perm_domain'],
      exact or.inr hL, },
    sorry, -/
     },
  { cases ne_of_inflexible_coe_of_not_inflexible H h₁'.some (λ h, h₂ ⟨h⟩) (λ h, h₂' ⟨h⟩) h, },
  { cases ne_of_inflexible_coe_of_not_inflexible H h₂'.some (λ h, h₁ ⟨h⟩) (λ h, h₁' ⟨h⟩) h.symm, },
  { rw [complete_litter_map_eq_of_flexible, complete_litter_map_eq_of_flexible,
      near_litter_approx.smul_eq_smul_litter] at h,
    exact h,
    rw [near_litter_approx.flexible_completion_litter_perm_domain_free _ _ _ (hπ A),
      mem_set_of, flexible_iff_not_inflexible_bot_coe],
    exact ⟨λ h, h₁ ⟨h⟩, λ h, h₁' ⟨h⟩⟩,
    rw [near_litter_approx.flexible_completion_litter_perm_domain_free _ _ _ (hπ A),
      mem_set_of, flexible_iff_not_inflexible_bot_coe],
    exact ⟨λ h, h₂ ⟨h⟩, λ h, h₂' ⟨h⟩⟩,
    exact λ h, h₂ ⟨h⟩,
    exact λ h, h₂' ⟨h⟩,
    exact λ h, h₁ ⟨h⟩,
    exact λ h, h₁' ⟨h⟩, },
end

-/
end struct_approx

end con_nf
