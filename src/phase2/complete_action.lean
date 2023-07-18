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

noncomputable def complete_atom_map (π : struct_approx β) :
  atom → extended_index β → atom :=
hypothesis.fix_atom π.atom_completion π.near_litter_completion

noncomputable def complete_near_litter_map (π : struct_approx β) :
  near_litter → extended_index β → near_litter :=
hypothesis.fix_near_litter π.atom_completion π.near_litter_completion

noncomputable def complete_litter_map (π : struct_approx β)
  (L : litter) (A : extended_index β) : litter :=
(π.complete_near_litter_map L.to_near_litter A).1

noncomputable def foa_hypothesis (π : struct_approx β) {c : support_condition β} :
  hypothesis c :=
⟨λ b B hb, π.complete_atom_map b B, λ N B hb, π.complete_near_litter_map N B⟩

variables {π : struct_approx β}

section map_spec
variables {a : atom} {L : litter} {N : near_litter} {A : extended_index β}

lemma complete_atom_map_eq :
  π.complete_atom_map a A = π.atom_completion a A π.foa_hypothesis :=
hypothesis.fix_atom_eq _ _ _ _

lemma complete_near_litter_map_eq :
  π.complete_near_litter_map N A = π.near_litter_completion N A π.foa_hypothesis :=
hypothesis.fix_near_litter_eq _ _ _ _

lemma complete_litter_map_eq :
  π.complete_litter_map L A = π.litter_completion L A π.foa_hypothesis :=
by rw [complete_litter_map, complete_near_litter_map_eq]; refl

lemma complete_near_litter_map_fst_eq :
  (π.complete_near_litter_map L.to_near_litter A).1 = π.complete_litter_map L A := rfl

@[simp] lemma foa_hypothesis_atom_image {c : support_condition β}
  (h : (inl a, A) <[α] c) :
  (π.foa_hypothesis : hypothesis c).atom_image a A h = π.complete_atom_map a A := rfl

@[simp] lemma foa_hypothesis_near_litter_image {c : support_condition β}
  (h : (inr N, A) <[α] c) :
  (π.foa_hypothesis : hypothesis c).near_litter_image N A h = π.complete_near_litter_map N A := rfl

end map_spec

lemma complete_atom_map_eq_of_mem_domain {a} {A} (h : a ∈ (π A).atom_perm.domain) :
  π.complete_atom_map a A = π A • a :=
by rw [complete_atom_map_eq, atom_completion, dif_pos h]

lemma complete_atom_map_eq_of_not_mem_domain {a} {A} (h : a ∉ (π A).atom_perm.domain) :
  π.complete_atom_map a A = ((π A).largest_sublitter a.1).order_iso
    ((π A).largest_sublitter (π.complete_litter_map a.1 A))
    ⟨a, (π A).mem_largest_sublitter_of_not_mem_domain a h⟩ :=
by rw [complete_atom_map_eq, atom_completion, dif_neg h]; refl

@[simp] def near_litter_hypothesis_eq (N : near_litter) (A : extended_index β) :
  near_litter_hypothesis N A π.foa_hypothesis = π.foa_hypothesis := rfl

/-- A basic definition unfold. -/
lemma complete_litter_map_eq_of_inflexible_coe {L : litter} {A : extended_index β}
  (h : inflexible_coe L A) (h₁ h₂) :
  π.complete_litter_map L A =
  f_map (with_bot.coe_ne_coe.mpr $ coe_ne' h.hδε)
    ((ih_action (π.foa_hypothesis : hypothesis ⟨inr L.to_near_litter, A⟩)).hypothesised_allowable
      h h₁ h₂ • h.t) :=
by rw [complete_litter_map_eq, litter_completion_of_inflexible_coe]

/-- A basic definition unfold. -/
lemma complete_litter_map_eq_of_inflexible_bot {L : litter} {A : extended_index β}
  (h : inflexible_bot L A) :
  π.complete_litter_map L A =
  f_map (show (⊥ : type_index) ≠ (h.ε : Λ), from with_bot.bot_ne_coe)
    (π.complete_atom_map h.a (h.B.cons (with_bot.bot_lt_coe _))) :=
by rw [complete_litter_map_eq, litter_completion_of_inflexible_bot]; refl

/-- A basic definition unfold. -/
lemma complete_litter_map_eq_of_flexible {L : litter} {A : extended_index β}
  (h : flexible α L A) :
  π.complete_litter_map L A = near_litter_approx.flexible_completion α (π A) A • L :=
by rw [complete_litter_map_eq, litter_completion_of_flexible _ _ _ _ h]

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
structure foa_props (π : struct_approx β) (c d : support_condition β) : Prop :=
(atom_injective : ∀ a b (B : extended_index β),
  (inl a, B) ∈ trans_constrained c d →
  (inl b, B) ∈ trans_constrained c d →
  π.complete_atom_map a B = π.complete_atom_map b B → a = b)
(litter_injective : ∀ (L₁ L₂ : litter) (B : extended_index β),
  (inr L₁.to_near_litter, B) ∈ trans_constrained c d →
  (inr L₂.to_near_litter, B) ∈ trans_constrained c d →
  π.complete_litter_map L₁ B = π.complete_litter_map L₂ B → L₁ = L₂)
(map_flexible : ∀ (L : litter) {γ : Iic α} (A : path (β : type_index) γ) (B : extended_index γ)
  (hL : (inr L.to_near_litter, A.comp B) ∈ trans_constrained c d)
  (hflex : flexible α L B), flexible α (π.complete_litter_map L (A.comp B)) B)

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
lemma atom_injective_extends {c d : support_condition β} (H : foa_props π c d)
  {a b : atom} {A : extended_index β}
  (hac : (inl a, A) ∈ refl_trans_constrained c d)
  (hbc : (inl b, A) ∈ refl_trans_constrained c d)
  (h : π.complete_atom_map a A = π.complete_atom_map b A) :
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
      ((π A).largest_sublitter (π.complete_litter_map b.1 A))
      ⟨b, (π A).mem_largest_sublitter_of_not_mem_domain b hb⟩).prop.1,
    have := H.litter_injective _ _ _
      (fst_trans_constrained hac) (fst_trans_constrained hbc) (h₁.symm.trans h₂),
    have := eq_of_sublitter_bijection_apply_eq h this (by rw this),
    rw [set_like.coe_mk, set_like.coe_mk] at this,
    exact this, },
end

lemma complete_atom_map_mem_complete_near_litter_map
  {c d : support_condition β} (H : foa_props π c d)
  {a : atom} {A : extended_index β} {N : near_litter} (h : a ∈ N)
  (hN : (inr N, A) ∈ trans_constrained c d) :
  π.complete_atom_map a A ∈ π.complete_near_litter_map N A :=
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
  near_litter_completion_map π L.to_near_litter A π.foa_hypothesis =
  (litter_set (π.litter_completion L.to_near_litter.fst A π.foa_hypothesis) \
    (π A).atom_perm.domain) ∪
  π A • (litter_set L ∩ (π A).atom_perm.domain) :=
by simp only [near_litter_completion_map, set.symm_diff_def, near_litter_hypothesis_eq,
  litter.coe_to_near_litter, litter.to_near_litter_fst, mem_union, mem_diff, mem_litter_set,
  diff_self, mem_empty_iff_false, false_and, Union_neg', not_false_iff, Union_empty, diff_empty,
  empty_diff, union_empty, near_litter_approx.coe_largest_sublitter]

lemma mem_of_complete_atom_map_mem_complete_near_litter_map
  {c d : support_condition β} (H : foa_props π c d)
  {a : atom} {A : extended_index β} {L : litter}
  (h : π.complete_atom_map a A ∈ π.complete_near_litter_map L.to_near_litter A)
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

lemma eq_of_mem_near_litter_completion_map {c d : support_condition β} (H : foa_props π c d)
  {L₁ L₂ : litter} {A : extended_index β}
  (hL₁ : (inr L₁.to_near_litter, A) ∈ trans_constrained c d)
  (hL₂ : (inr L₂.to_near_litter, A) ∈ trans_constrained c d)
  (a : atom)
  (ha₁ : a ∈ near_litter_completion_map π L₁.to_near_litter A π.foa_hypothesis)
  (ha₂ : a ∈ near_litter_completion_map π L₂.to_near_litter A π.foa_hypothesis) :
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

lemma eq_of_litter_map_inter_nonempty {c d : support_condition β} (H : foa_props π c d)
  {L₁ L₂ : litter} {A : extended_index β}
  (hL₁ : (inr L₁.to_near_litter, A) ∈ trans_constrained c d)
  (hL₂ : (inr L₂.to_near_litter, A) ∈ trans_constrained c d)
  (h : ((π.complete_near_litter_map L₁.to_near_litter A : set atom) ∩
    π.complete_near_litter_map L₂.to_near_litter A).nonempty) : L₁ = L₂ :=
begin
  obtain ⟨a, ha₁, ha₂⟩ := h,
  refine eq_of_mem_near_litter_completion_map H hL₁ hL₂ a _ _,
  rwa complete_near_litter_map_eq at ha₁,
  rwa complete_near_litter_map_eq at ha₂,
end

/-- An object like `ih_action` that can take two support conditions. -/
noncomputable def ihs_action (π : struct_approx β) (c d : support_condition β) : struct_action β :=
λ B, {
  atom_map := λ a, ⟨(inl a, B) ∈ trans_constrained c d,
    λ h, π.complete_atom_map a B⟩,
  litter_map := λ L, ⟨(inr L.to_near_litter, B) ∈ trans_constrained c d,
    λ h, π.complete_near_litter_map L.to_near_litter B⟩,
  atom_map_dom_small := small.union
    (ih_action π.foa_hypothesis B).atom_map_dom_small
    (ih_action π.foa_hypothesis B).atom_map_dom_small,
  litter_map_dom_small := small.union
    (ih_action π.foa_hypothesis B).litter_map_dom_small
    (ih_action π.foa_hypothesis B).litter_map_dom_small,
}

lemma ih_action_supports {L : litter} {A : extended_index β} (h : inflexible_coe L A) :
  ((ih_action (π.foa_hypothesis : hypothesis ⟨inr L.to_near_litter, A⟩)).comp
    (h.B.cons (coe_lt h.hδ))).supports h.t := {
  atom_mem := begin
    intros a B ha,
    simp only [struct_action.comp_atom_map, ih_action_atom_map],
    have := mem_reduction_designated_support α h.hδ h.hε h.hδε h.B h.t _ ha,
    rw [← h.hL, ← h.hA] at this,
    exact this,
  end,
  litter_mem := begin
    intros L B hL,
    simp only [struct_action.comp_litter_map, ih_action_litter_map],
    have := mem_reduction_designated_support α h.hδ h.hε h.hδε h.B h.t _ hL,
    rw [← h.hL, ← h.hA] at this,
    exact this,
  end,
}

lemma trans_gen_constrains_of_mem_designated_support
  {L : litter} {A : extended_index β} {h : inflexible_coe L A}
  {γ : Iic α} {δ ε : Iio α} {hδ : (δ : Λ) < γ} {hε : (ε : Λ) < γ} (hδε : δ ≠ ε)
  {C : path (h.δ : type_index) γ} {t : tangle δ} {d : support_condition h.δ}
  (hd₂ : (inr (f_map (subtype.coe_injective.ne (Iio.coe_injective.ne hδε)) t).to_near_litter,
    (C.cons (coe_lt hε)).cons (bot_lt_coe _)) ≤[α] d)
  (hd : (d.fst, (h.B.cons (coe_lt h.hδ)).comp d.snd) ≺[α] (inr L.to_near_litter, A))
  {B : extended_index δ} {a : atom}
  (hc : (inl a, B) ∈ (designated_support t).carrier) :
  (inl a, (h.B.cons (coe_lt h.hδ)).comp ((C.cons (coe_lt hδ)).comp B)) <[α]
    (inr L.to_near_litter, A) :=
begin
  refine relation.trans_gen.tail' _ hd,
  refine @refl_trans_gen_constrains_comp _ _ _ _ _ _ (inl a, _) d
    _ (h.B.cons $ coe_lt h.hδ),
  refine relation.refl_trans_gen.trans _ hd₂,
  exact relation.refl_trans_gen.single (constrains.f_map hδ hε hδε C t _ hc),
end

lemma ih_action_coherent_coe
  {L : litter} {A : extended_index β}
  (h : inflexible_coe L A)
  (h₁ : ((ih_action π.foa_hypothesis).comp (h.B.cons _)).lawful)
  (h₂ : ((ih_action (π.foa_hypothesis : hypothesis ⟨inr L.to_near_litter, A⟩)).comp
    (h.B.cons $ coe_lt h.hδ)).map_flexible) :
  (((ih_action (π.foa_hypothesis : hypothesis ⟨inr L.to_near_litter, A⟩)).comp
    (h.B.cons (coe_lt h.hδ))).refine h₁).coherent_coe struct_action.refine_lawful h.t :=
begin
  rintros ρ hρ γ δ ε hδ hε hδε C t hL ⟨d, hd₁, hd₂⟩ ht,
  simp only [struct_action.refine_apply, struct_action.refine_litter_map,
    struct_action.comp_litter_map, path.comp_cons, ih_action_litter_map,
    foa_hypothesis_near_litter_image, complete_near_litter_map_fst_eq],
  let inflex : inflexible_coe (f_map _ t) ((((h.B.cons (coe_lt h.hδ)).comp C).cons _).cons _) :=
    ⟨γ, δ, ε, hδ, hε, hδε, _, t, rfl, rfl⟩,
  refine eq.trans _ (complete_litter_map_eq_of_inflexible_coe inflex _ _).symm,
  { sorry, },
  { sorry, },
  { refine congr_arg _ _,
    rw [← inv_smul_eq_iff, smul_smul],
    refine (designated_support t).supports _ _,
    intros c hc,
    rw [mul_smul, inv_smul_eq_iff],
    refine prod.ext _ rfl,
    refine eq.trans _ ((congr_arg prod.fst (ht c hc)).trans _),
    { rw ← allowable.derivative_cons_apply,
      change _ • _ = _ • _,
      rw [← allowable.derivative_to_struct_perm, struct_perm.derivative_derivative],
      refl, },
    have hd := constrains.f_map h.hδ h.hε h.hδε _ h.t d hd₁,
      rw [← h.hL, ← h.hA] at hd,
    obtain ⟨a | N, B⟩ := c,
    { rw struct_action.support_condition_map_or_else,
      have ha : (((ih_action π.foa_hypothesis).comp (h.B.cons $ coe_lt h.hδ)
        ((C.cons $ coe_lt hδ).comp B)).atom_map a).dom,
      { simp only [struct_action.comp_atom_map, ih_action_atom_map],
        exact trans_gen_constrains_of_mem_designated_support hδε hd₂ hd hc, },
      rw near_litter_action.atom_map_or_else_of_dom,
      swap, exact or.inl (or.inl ha),
      change inl _ = inl _,
      simp only [struct_action.refine_apply],
      simp_rw struct_action.refine_atom_map ha,
      have := ((ih_action π.foa_hypothesis).hypothesised_allowable_exactly_approximates
        inflex _ _ _).map_atom a (or.inl (or.inl (or.inl (or.inl _)))),
      rw struct_perm.of_bot_smul at this,
      rw [← this, struct_action.rc_smul_atom_eq],
      simp only [struct_action.comp_atom_map, ih_action_atom_map, foa_hypothesis_atom_image],
      rw [← path.comp_assoc, path.comp_cons],
      simp only [struct_action.comp_atom_map, ih_action_atom_map],
      all_goals { exact relation.trans_gen.single (constrains.f_map hδ hε hδε _ _ _ hc), }, },
    { rw struct_action.support_condition_map_or_else,
      rw near_litter_action.near_litter_map_or_else_of_dom,
      swap,
      { simp only [struct_action.refine_apply, struct_action.refine_litter_map,
          struct_action.comp_litter_map, ih_action_litter_map],
        refine relation.trans_gen.tail' _ hd,
        refine @refl_trans_gen_constrains_comp _ _ _ _ _ _ (inr N.fst.to_near_litter, _) d
          _ (h.B.cons $ coe_lt h.hδ),
        refine relation.refl_trans_gen.trans _ hd₂,
        refine refl_trans_gen_near_litter _,
        exact relation.refl_trans_gen.single (constrains.f_map hδ hε hδε C t _ hc), },
      swap,
      { intros a ha,
        refine or.inl (or.inl _),
        simp only [struct_action.comp_atom_map, ih_action_atom_map],
        refine relation.trans_gen.tail' _ hd,
        refine @refl_trans_gen_constrains_comp _ _ _ _ _ _ (inl a, _) d
          _ (h.B.cons $ coe_lt h.hδ),
        refine relation.refl_trans_gen.trans _ hd₂,
        refine relation.refl_trans_gen.head (constrains.symm_diff N a ha _) _,
        exact relation.refl_trans_gen.single (constrains.f_map hδ hε hδε C t _ hc), },
      change inr _ = inr _,
      simp only [struct_action.refine_apply, struct_action.refine_litter_map,
        struct_action.comp_litter_map, ih_action_litter_map, foa_hypothesis_near_litter_image],
      rw ← (@set_like.coe_injective near_litter atom _).eq_iff,
      simp only [near_litter.coe_mk, subtype.coe_mk],
      refine eq.trans _ (near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul _ _).symm,
      refine congr_arg2 _ _ _,
      { have hex := ((ih_action π.foa_hypothesis).hypothesised_allowable_exactly_approximates
          inflex _ _ _),
        have := near_litter_action.smul_to_near_litter_eq_of_precise_at _ hex _ _ _,
        apply_fun set_like.coe at this,
        refine eq.trans _ this.symm,
        { sorry },
        { simp only [struct_action.refine_apply, struct_action.refine_litter_map,
            struct_action.comp_litter_map, ih_action_litter_map, foa_hypothesis_near_litter_image],
          rw [← path.comp_assoc, path.comp_cons],
          refl, },
        { exact struct_action.refine_precise _ _, },
        { simp only [struct_perm.of_bot_smul, struct_action.refine_apply,
            struct_action.refine_litter_map, struct_action.comp_litter_map,
            ih_action_litter_map, foa_hypothesis_near_litter_image],
          sorry, }, },
      { sorry, }, }, },
end

lemma ih_action_coherent_bot
  {L : litter} {A : extended_index β}
  (h : inflexible_coe L A) (h₁ : ((ih_action π.foa_hypothesis).comp (h.B.cons _)).lawful)
  (h₂ : ((ih_action (π.foa_hypothesis : hypothesis ⟨inr L.to_near_litter, A⟩)).comp
    (h.B.cons $ coe_lt h.hδ)).map_flexible) :
  (((ih_action (π.foa_hypothesis : hypothesis ⟨inr L.to_near_litter, A⟩)).comp
    (h.B.cons (coe_lt h.hδ))).refine h₁).coherent_bot struct_action.refine_lawful := sorry

lemma ih_action_coherent
  {L : litter} {A : extended_index β}
  (h : inflexible_coe L A) (h₁ : ((ih_action π.foa_hypothesis).comp (h.B.cons _)).lawful)
  (h₂ : ((ih_action (π.foa_hypothesis : hypothesis ⟨inr L.to_near_litter, A⟩)).comp
    (h.B.cons $ coe_lt h.hδ)).map_flexible) :
  (((ih_action (π.foa_hypothesis : hypothesis ⟨inr L.to_near_litter, A⟩)).comp
    (h.B.cons (coe_lt h.hδ))).refine h₁).coherent struct_action.refine_lawful h.t := {
  coe := ih_action_coherent_coe h h₁ h₂,
  bot := ih_action_coherent_bot h h₁ h₂,
}

lemma ih_action_smul_eq_ihs_action_smul
  {L : litter} {A : extended_index β} {c : support_condition β}
  (h : inflexible_coe L A) (h₁ h₂ h₃ h₄) :
  (ih_action (π.foa_hypothesis : hypothesis ⟨inr L.to_near_litter, A⟩)).hypothesised_allowable
    h h₁ h₂ • h.t =
  (ihs_action π (inr L.to_near_litter, A) c).hypothesised_allowable
    h h₃ h₄ • h.t :=
begin
  refine struct_action.smul_eq_smul_tangle _ _ _ _
    struct_action.refine_precise
    struct_action.refine_precise
    _ _ _ _
    (struct_action.allowable_exactly_approximates _ _ _ _)
    (struct_action.allowable_exactly_approximates _ _ _ _),
  { constructor,
    { intros a B ha,
      simp only [struct_action.refine_apply],
      refine (struct_action.refine_atom_map_get _).trans
        ((struct_action.refine_atom_map_get _).trans _).symm,
      sorry,
      sorry,
      sorry,
      refl, },
    { intros a B ha,
      simp only [struct_action.refine_apply, struct_action.refine_litter_map],
      refl, },
    { exact struct_action.refine_supports _ _ (ih_action_supports h), }, },
  { exact ih_action_coherent h h₁ h₂, },
  { sorry, },
end

/-

lemma hypothesis_injective_inflexible_of_mem_refl_trans_constrained
  {c d : support_condition β} (H : foa_props π c d)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (h' : (inr L.to_near_litter, A) ∈ refl_trans_constrained c d) :
  hypothesis_injective_inflexible π.foa_hypothesis h :=
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

lemma ne_of_inflexible_bot_of_not_inflexible_bot {c d : support_condition β} (H : foa_props π c d)
  {L₁ L₂ : litter} {A : extended_index β}
  (hL₁ : inflexible_bot L₁ A) (hL₂ : is_empty (inflexible_bot L₂ A))
  (hL₁' : (inr L₁.to_near_litter, A) ∈ refl_trans_constrained c d)
  (hL₂' : (inr L₂.to_near_litter, A) ∈ refl_trans_constrained c d) :
  π.complete_litter_map L₁ A ≠ π.complete_litter_map L₂ A :=
begin
  obtain ⟨γ₁, ε₁, hγε₁, B₁, a₁, hL₁, hA₁⟩ := hL₁,
  rw complete_litter_map_eq_of_inflexible_bot ⟨γ₁, ε₁, hγε₁, B₁, a₁, hL₁, hA₁⟩,
  by_cases h₂ : nonempty (inflexible_coe L₂ A),
  { cases h₂,
    rw complete_litter_map_eq_of_inflexible_coe h₂,
    intro h,
    have := congr_arg litter.β h,
    simp only [f_map, bot_ne_coe] at this,
    exact this,
    exact hypothesis_injective_inflexible_of_mem_refl_trans_constrained H h₂ hL₂', },
  { have flex := flexible_iff_not_inflexible_bot_coe.mpr ⟨hL₂, ⟨λ h, h₂ ⟨h⟩⟩⟩,
    rw complete_litter_map_eq_of_flexible hL₂ ⟨λ h, h₂ ⟨h⟩⟩,
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

lemma ne_of_inflexible_coe_of_not_inflexible {c d : support_condition β} (H : foa_props π c d)
  {L₁ L₂ : litter} {A : extended_index β}
  (hL₁ : inflexible_coe L₁ A)
  (hL₂ : flexible α L₂ A)
  (hcL₁ : (inr L₁.to_near_litter, A) ∈ refl_trans_constrained c d) :
  π.complete_litter_map L₁ A ≠ π.complete_litter_map L₂ A :=
begin
  rw complete_litter_map_eq_of_inflexible_coe hL₁,
  rw complete_litter_map_eq_of_flexible hL₂,
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
noncomputable def trans_gen_struct_approx {c d : support_condition β} (H : foa_props π c d)
  {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ) (A : quiver.path (β : type_index) γ) :
  near_litter_action δ :=
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

@[simp] lemma trans_gen_struct_approx_atom_map {c d : support_condition β} (H : foa_props π c d)
  {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ) (A : quiver.path (β : type_index) γ)
  (B : extended_index δ) (a : atom) :
  (trans_gen_struct_approx H hδ A B).atom_map a = {
    dom := (inl a, (A.cons (coe_lt hδ)).comp B) ∈ trans_constrained c d,
    get := λ ha, π.complete_atom_map hπ a ((A.cons (coe_lt hδ)).comp B)
  } := rfl

@[simp] lemma trans_gen_struct_approx_litter_map {c d : support_condition β} (H : foa_props π c d)
  {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ) (A : quiver.path (β : type_index) γ)
  (B : extended_index δ) (L : litter) :
  (trans_gen_struct_approx H hδ A B).litter_map L = {
    dom := (inr L.to_near_litter, (A.cons (coe_lt hδ)).comp B) ∈ trans_constrained c d,
    get := λ hL, π.complete_near_litter_map hπ L.to_near_litter ((A.cons (coe_lt hδ)).comp B)
  } := rfl

lemma complete_litter_map_flexible {L : litter} {A : extended_index β} (h : flexible α L A) :
  flexible α (π.complete_litter_map hπ L A) A :=
begin
  rw complete_litter_map_eq_of_flexible' h,
  exact near_litter_approx.flexible_completion_smul_flexible _ _ _ (hπ A) _ h,
end

noncomputable lemma complete_litter_map_inflexible_bot {L : litter} {A : extended_index β}
  (h : inflexible_bot L A) : inflexible_bot (π.complete_litter_map hπ L A) A :=
begin
  rw complete_litter_map_eq_of_inflexible_bot h,
  obtain ⟨γ, ε, hγε, B, a, rfl, rfl⟩ := h,
  exact ⟨_, _, _, _, _, rfl, rfl⟩,
end

noncomputable lemma complete_litter_map_inflexible_coe {c d : support_condition β}
  (H : foa_props π c d) {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (hL : (inr L.to_near_litter, A) ∈ refl_trans_constrained c d) :
  inflexible_coe (π.complete_litter_map hπ L A) A :=
begin
  rw complete_litter_map_eq_of_inflexible_coe hπ h,
  obtain ⟨γ, δ, ε, hδ, hε, hδε, B, a, rfl, rfl⟩ := h,
  exact ⟨_, _, _, hδ, hε, hδε, _, _, rfl, rfl⟩,
  exact hypothesis_injective_inflexible_of_mem_refl_trans_constrained H h hL,
end

lemma complete_litter_map_flexible' {c d : support_condition β}
  (H : foa_props π c d) {L : litter} {A : extended_index β}
  (hL : (inr L.to_near_litter, A) ∈ refl_trans_constrained c d)
  (h : flexible α (π.complete_litter_map hπ L A) A) : flexible α L A :=
begin
  obtain (h' | h' | h') := flexible_cases' L A,
  { exact h', },
  { have := complete_litter_map_inflexible_bot h'.some,
    rw flexible_iff_not_inflexible_bot_coe at h,
    cases h.1.false this, },
  { have := complete_litter_map_inflexible_coe H h'.some hL,
    rw flexible_iff_not_inflexible_bot_coe at h,
    cases h.2.false this, },
end

lemma complete_litter_map_flexible_iff {c d : support_condition β}
  (H : foa_props π c d) {L : litter} {A : extended_index β}
  (hL : (inr L.to_near_litter, A) ∈ refl_trans_constrained c d) :
  flexible α (π.complete_litter_map hπ L A) A ↔ flexible α L A :=
⟨complete_litter_map_flexible' H hL, complete_litter_map_flexible⟩

noncomputable lemma complete_litter_map_inflexible_bot' {c d : support_condition β}
  (H : foa_props π c d) {L : litter} {A : extended_index β}
  (hL : (inr L.to_near_litter, A) ∈ refl_trans_constrained c d)
  (h : inflexible_bot (π.complete_litter_map hπ L A) A) : inflexible_bot L A :=
begin
  refine nonempty.some _,
  obtain (h' | h' | h') := flexible_cases' L A,
  { have := complete_litter_map_flexible h',
    rw flexible_iff_not_inflexible_bot_coe at this,
    cases this.1.false h, },
  { exact h', },
  { have := complete_litter_map_inflexible_coe H h'.some hL,
    cases inflexible_bot_inflexible_coe h this, },
end

lemma complete_litter_map_inflexible_bot_iff {c d : support_condition β}
  (H : foa_props π c d) {L : litter} {A : extended_index β}
  (hL : (inr L.to_near_litter, A) ∈ refl_trans_constrained c d) :
  nonempty (inflexible_bot (π.complete_litter_map hπ L A) A) ↔ nonempty (inflexible_bot L A) :=
⟨λ ⟨h⟩, ⟨complete_litter_map_inflexible_bot' H hL h⟩, λ ⟨h⟩, ⟨complete_litter_map_inflexible_bot h⟩⟩

noncomputable lemma complete_litter_map_inflexible_coe' {c d : support_condition β}
  (H : foa_props π c d) {L : litter} {A : extended_index β}
  (hL : (inr L.to_near_litter, A) ∈ refl_trans_constrained c d)
  (h : inflexible_coe (π.complete_litter_map hπ L A) A) : inflexible_coe L A :=
begin
  refine nonempty.some _,
  obtain (h' | h' | h') := flexible_cases' L A,
  { have := complete_litter_map_flexible h',
    rw flexible_iff_not_inflexible_bot_coe at this,
    cases this.2.false h, },
  { have := complete_litter_map_inflexible_bot h'.some,
    cases inflexible_bot_inflexible_coe this h, },
  { exact h', },
end

lemma complete_litter_map_inflexible_coe_iff {c d : support_condition β}
  (H : foa_props π c d) {L : litter} {A : extended_index β}
  (hL : (inr L.to_near_litter, A) ∈ refl_trans_constrained c d) :
  nonempty (inflexible_coe (π.complete_litter_map hπ L A) A) ↔ nonempty (inflexible_coe L A) :=
⟨λ ⟨h⟩, ⟨complete_litter_map_inflexible_coe' H hL h⟩,
  λ ⟨h⟩, ⟨complete_litter_map_inflexible_coe H h hL⟩⟩

lemma eq_of_hypothesised_allowable_smul_eq {c d : support_condition β} (H : foa_props π c d)
  {γ : Iic α} {δ ε : Iio α}
  {t₁ t₂ : tangle δ}
  {B : path (β : type_index) γ}
  (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
  (h₁ : (inr (f_map _ t₁).to_near_litter, (B.cons (coe_lt hε)).cons (bot_lt_coe _)) ∈
    refl_trans_constrained c d)
  (h₂ : (inr (f_map _ t₂).to_near_litter, (B.cons (coe_lt hε)).cons (bot_lt_coe _)) ∈
    refl_trans_constrained c d)
  (h : (π.hypothesised_allowable hπ
      ⟨γ, δ, ε, hδ, hε, hδε, B, t₁, rfl, rfl⟩
      (π.foa_hypothesis hπ)
      (hypothesis_injective_inflexible_of_mem_refl_trans_constrained H _ h₁) • t₁) =
    (π.hypothesised_allowable hπ
      ⟨γ, δ, ε, hδ, hε, hδε, B, t₂, rfl, rfl⟩
      (π.foa_hypothesis hπ)
      (hypothesis_injective_inflexible_of_mem_refl_trans_constrained H _ h₂) • t₂)) :
  t₁ = t₂ :=
sorry

lemma litter_injective_extends {c d : support_condition β} (H : foa_props π c d)
  {L₁ L₂ : litter} {A : extended_index β}
  (h₁ : (inr L₁.to_near_litter, A) ∈ refl_trans_constrained c d)
  (h₂ : (inr L₂.to_near_litter, A) ∈ refl_trans_constrained c d)
  (h : π.complete_litter_map hπ L₁ A = π.complete_litter_map hπ L₂ A) :
  L₁ = L₂ :=
begin
  obtain (h₁' | h₁' | h₁') := flexible_cases' L₁ A,
  { have h₂' : flexible α L₂ A,
    { have := complete_litter_map_flexible h₁',
      rw h at this,
      exact complete_litter_map_flexible' H h₂ this, },
    rw [complete_litter_map_eq_of_flexible' h₁',
      complete_litter_map_eq_of_flexible' h₂'] at h,
    refine local_perm.inj_on _ _ _ h,
    all_goals {
      rw near_litter_approx.flexible_completion_litter_perm_domain_free _ _ _ (hπ A),
      assumption, }, },
  { obtain ⟨h₁'⟩ := h₁',
    have h₂' : inflexible_bot L₂ A,
    { have := complete_litter_map_inflexible_bot h₁',
      rw h at this,
      exact complete_litter_map_inflexible_bot' H h₂ this, },
    rw [complete_litter_map_eq_of_inflexible_bot h₁',
      complete_litter_map_eq_of_inflexible_bot h₂'] at h,
    obtain ⟨γ₁, ε₁, hγε₁, B₁, a₁, rfl, rfl⟩ := h₁',
    obtain ⟨γ₂, ε₂, hγε₂, B₂, a₂, rfl, hB⟩ := h₂',
    cases subtype.coe_injective (coe_injective (path.obj_eq_of_cons_eq_cons hB)),
    cases subtype.coe_injective (coe_injective (path.obj_eq_of_cons_eq_cons
      (path.heq_of_cons_eq_cons hB).eq)),
    cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons hB).eq).eq,
    refine congr_arg _ (H.atom_injective _ _ _ _ _ (f_map_injective bot_ne_coe h)),
    { have := constrains.f_map_bot hγε₁ B₁ a₁,
      exact trans_constrained_of_refl_trans_constrained_of_trans_constrains h₁
        (relation.trans_gen.single this), },
    { have := constrains.f_map_bot hγε₁ B₁ a₂,
      exact trans_constrained_of_refl_trans_constrained_of_trans_constrains h₂
        (relation.trans_gen.single this), }, },
  { obtain ⟨h₁'⟩ := h₁',
    have h₂' : inflexible_coe L₂ A,
    { have := complete_litter_map_inflexible_coe H h₁' h₁,
      rw h at this,
      exact complete_litter_map_inflexible_coe' H h₂ this, },
    rw [complete_litter_map_eq_of_inflexible_coe hπ h₁'
      (hypothesis_injective_inflexible_of_mem_refl_trans_constrained H h₁' h₁),
      complete_litter_map_eq_of_inflexible_coe hπ h₂'
      (hypothesis_injective_inflexible_of_mem_refl_trans_constrained H h₂' h₂)] at h,
    obtain ⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₁, rfl, rfl⟩ := h₁',
    obtain ⟨γ₂, δ₂, ε₂, hδ₂, hε₂, hδε₂, B₂, t₂, rfl, hB⟩ := h₂',
    cases subtype.coe_injective (coe_injective (path.obj_eq_of_cons_eq_cons hB)),
    cases subtype.coe_injective (coe_injective (path.obj_eq_of_cons_eq_cons
      (path.heq_of_cons_eq_cons hB).eq)),
    cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons hB).eq).eq,
    have := congr_arg litter.β h,
    cases subtype.coe_injective (coe_injective this),
    refine congr_arg _ _,
    exact eq_of_hypothesised_allowable_smul_eq H hδ₁ hε₁ hδε₁ h₁ h₂ (f_map_injective _ h), },
end

-/

end struct_approx

end con_nf
