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

lemma trans_constrained_symm (c d : support_condition β) :
  trans_constrained c d = trans_constrained d c := union_comm _ _

lemma refl_trans_constrained_symm (c d : support_condition β) :
  refl_trans_constrained c d = refl_trans_constrained d c := union_comm _ _

@[simp] lemma trans_constrained_self (c : support_condition β) :
  trans_constrained c c = {e | e <[α] c} := union_self _

@[simp] lemma refl_trans_constrained_self (c : support_condition β) :
  refl_trans_constrained c c = {e | e ≤[α] c} := union_self _

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

-- TODO: Convert uses of `foa_props` into uses of
-- `struct_action.lawful` and `struct_action.map_flexible`.
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

@[simp] lemma ihs_action_atom_map {π : struct_approx β} {c d : support_condition β}
  {B : extended_index β} {a : atom} :
  (ihs_action π c d B).atom_map a =
  ⟨(inl a, B) ∈ trans_constrained c d,
    λ h, complete_atom_map π a B⟩ := rfl

@[simp] lemma ihs_action_litter_map {π : struct_approx β} {c d : support_condition β}
  {B : extended_index β} {L : litter} :
  (ihs_action π c d B).litter_map L =
  ⟨(inr L.to_near_litter, B) ∈ trans_constrained c d,
    λ h, π.complete_near_litter_map L.to_near_litter B⟩ := rfl

lemma ihs_action_symm (π : struct_approx β) (c d : support_condition β) :
  ihs_action π c d = ihs_action π d c :=
begin
  ext,
  rw [ihs_action_atom_map, ihs_action_atom_map, trans_constrained_symm],
  rw [ihs_action_litter_map, ihs_action_litter_map, trans_constrained_symm],
end

@[simp] lemma ihs_action_self (π : struct_approx β) (c : support_condition β) :
  ihs_action π c c = ih_action (π.foa_hypothesis : hypothesis c) :=
begin
  ext,
  { rw [ihs_action_atom_map, ih_action_atom_map, trans_constrained_self],
    refl, },
  { rw [ihs_action_litter_map, ih_action_litter_map, trans_constrained_self],
    refl, },
end

lemma ih_action_le_ihs_action (π : struct_approx β) (c d : support_condition β) :
  ih_action (π.foa_hypothesis : hypothesis c) ≤ ihs_action π c d :=
λ B, ⟨⟨λ a, or.inl, λ a h, rfl⟩, ⟨λ L, or.inl, λ L h, rfl⟩⟩

lemma ih_action_le {π : struct_approx β} {c d : support_condition β} (h : c ≤[α] d) :
  ih_action (π.foa_hypothesis : hypothesis c) ≤ ih_action (π.foa_hypothesis : hypothesis d) :=
begin
  refine λ B, ⟨⟨_, λ a h, rfl⟩, ⟨_, λ L h, rfl⟩⟩,
  { intros a ha,
    exact relation.trans_gen.trans_left ha h, },
  { intros a ha,
    exact relation.trans_gen.trans_left ha h, },
end

lemma ih_action_supports {L : litter} {A : extended_index β} (h : inflexible_coe L A) :
  ((ih_action (π.foa_hypothesis : hypothesis ⟨inr L.to_near_litter, A⟩)).comp
    (h.B.cons (coe_lt h.hδ))).supports h.t := {
  atom_mem := begin
    intros a B ha,
    simp only [struct_action.comp_apply, ih_action_atom_map],
    have := mem_reduction_designated_support α h.hδ h.hε h.hδε h.B h.t _ ha,
    rw [← h.hL, ← h.hA] at this,
    exact this,
  end,
  litter_mem := begin
    intros L B hL,
    simp only [struct_action.comp_apply, ih_action_litter_map],
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

-- TODO: move to struct_perm
@[simp] lemma _root_.con_nf.struct_perm.derivative_fst {α β : type_index} (π : struct_perm α)
  (A : path α β) (N : near_litter) :
  (struct_perm.derivative A π • N).fst = struct_perm.derivative A π • N.fst := rfl

lemma to_struct_perm_bot : (allowable.to_struct_perm : allowable ⊥ → struct_perm ⊥) =
  struct_perm.to_bot_iso.to_monoid_hom := rfl

/-- I think it's quite a big deal that this isn't a defeq.
We should probably refactor structural permutations to be like structural approximations,
a function from extended indices to near-litter permutations. -/
@[simp] lemma to_struct_perm_to_near_litter_perm (π : allowable ⊥) :
  π.to_struct_perm.to_near_litter_perm = π :=
begin
  ext a : 2,
  rw [to_struct_perm_bot, struct_perm.coe_to_near_litter_perm],
  simp only [mul_equiv.coe_to_monoid_hom, struct_perm.coe_to_bot_iso, struct_perm.of_bot_to_bot],
end

-- TODO: move earlier and use
lemma complete_near_litter_map_eq' (N : near_litter) (A : extended_index β) :
  (π.complete_near_litter_map N A : set atom) =
  (π.complete_near_litter_map N.fst.to_near_litter A) ∆
    ((λ a, π.complete_atom_map a A) '' litter_set N.fst ∆ ↑N) :=
begin
  simp only [complete_near_litter_map_eq, near_litter_completion, near_litter_completion_map,
    near_litter_hypothesis_eq, near_litter_approx.coe_largest_sublitter, mem_diff,
    foa_hypothesis_atom_image, near_litter.coe_mk, subtype.coe_mk, litter.coe_to_near_litter,
    litter.to_near_litter_fst, symm_diff_self, bot_eq_empty, mem_empty_iff_false, false_and,
    Union_neg', not_false_iff, Union_empty, symm_diff_empty],
  ext a : 1,
  split,
  { rintro (⟨ha₁ | ⟨a, ha₁, rfl⟩, ha₂⟩ | ⟨⟨_, ⟨b, rfl⟩, _, ⟨⟨hb₁, hb₂⟩, rfl⟩, ha⟩, ha₂⟩),
    { refine or.inl ⟨or.inl ha₁, _⟩,
      simp only [mem_image, not_exists, not_and],
      intros b hb,
      by_cases b ∈ (π A).atom_perm.domain,
      { rw complete_atom_map_eq_of_mem_domain h,
        rintro rfl,
        exact ha₁.2 ((π A).atom_perm.map_domain h), },
      { simp only [mem_Union, mem_singleton_iff, not_exists, and_imp] at ha₂,
        exact ne.symm (ha₂ b hb h), }, },
    { by_cases a ∈ litter_set N.fst,
      { refine or.inl ⟨or.inr ⟨a, ⟨h, ha₁.2⟩, rfl⟩, _⟩,
        simp only [mem_image, not_exists, not_and],
        intros b hb,
        by_cases hb' : b ∈ (π A).atom_perm.domain,
        { rw complete_atom_map_eq_of_mem_domain hb',
          intro hab,
          cases (π A).atom_perm.inj_on hb' ha₁.2 hab,
          cases hb,
          exact hb.2 ha₁.1,
          exact hb.2 h, },
        { simp only [mem_Union, mem_singleton_iff, not_exists, and_imp] at ha₂,
          exact ne.symm (ha₂ b hb hb'), }, },
      { refine or.inr ⟨⟨a, or.inr ⟨ha₁.1, h⟩, _⟩, _⟩,
        { simp only [complete_atom_map_eq_of_mem_domain ha₁.2], },
        rintro (ha | ⟨b, hb₁, hb₂⟩),
        { exact ha.2 ((π A).atom_perm.map_domain ha₁.2), },
        { cases (π A).atom_perm.inj_on hb₁.2 ha₁.2 hb₂,
          exact h hb₁.1, }, }, },
    { simp only [mem_singleton_iff] at ha,
      subst ha,
      refine or.inr ⟨⟨b, hb₁, rfl⟩, _⟩,
      contrapose! ha₂,
      cases ha₂,
      { exact or.inl ha₂, },
      obtain ⟨a, ha₁, ha₂⟩ := ha₂,
      by_cases a ∈ N,
      { rw ← ha₂,
        exact or.inr ⟨a, ⟨h, ha₁.2⟩, rfl⟩, },
      rw complete_atom_map_eq_of_not_mem_domain hb₂,
      simp only [mem_union, mem_diff, mem_litter_set, sublitter.order_iso_apply_fst_eq,
        near_litter_approx.largest_sublitter_litter],
      refine or.inl ⟨_, _⟩,
      { suffices : b ∈ litter_set N.fst,
        { rw mem_litter_set at this,
          rw [this, complete_litter_map_eq], },
        cases hb₁,
        { exact hb₁.1, },
        exfalso,
        rw complete_atom_map_eq_of_not_mem_domain hb₂ at ha₂,
        have : π A • a ∈ _ := (π A).atom_perm.map_domain ha₁.2,
        rw ha₂ at this,
        exact near_litter_approx.not_mem_domain_of_mem_largest_sublitter _
          (sublitter.order_iso_apply_mem _) this, },
      { exact near_litter_approx.not_mem_domain_of_mem_largest_sublitter _
          (sublitter.order_iso_apply_mem _), }, }, },
  { rintro (⟨ha₁ | ⟨a, ha₁, rfl⟩, ha₂⟩ | ⟨⟨a, ha₁, rfl⟩, ha₂⟩),
    { refine or.inl ⟨or.inl ha₁, _⟩,
      simp only [mem_Union, mem_singleton_iff, not_exists, and_imp],
      rintros b hb₁ hb₂ rfl,
      exact ha₂ ⟨b, hb₁, rfl⟩, },
    { refine or.inl ⟨_, _⟩,
      { by_cases a ∈ N,
        { exact or.inr ⟨a, ⟨h, ha₁.2⟩, rfl⟩, },
        { simp only [mem_image, not_exists, not_and] at ha₂,
          have := ha₂ a (or.inl ⟨ha₁.1, h⟩),
          rw complete_atom_map_eq_of_mem_domain ha₁.2 at this,
          cases this rfl, }, },
      { contrapose! ha₂,
        obtain ⟨_, ⟨b, rfl⟩, _, ⟨hb, rfl⟩, ha₂⟩ := ha₂,
        simp only [mem_singleton_iff] at ha₂,
        rw ha₂,
        exact ⟨b, hb.1, rfl⟩, }, },
    { rw [mem_union, not_or_distrib] at ha₂,
      by_cases ha : a ∈ litter_set N.fst,
      { have : a ∉ (π A).atom_perm.domain,
        { intro h,
          refine ha₂.2 ⟨a, ⟨ha, h⟩, _⟩,
          simp only [complete_atom_map_eq_of_mem_domain h], },
        refine or.inr ⟨_, _⟩,
        { exact ⟨_, ⟨a, rfl⟩, _, ⟨⟨ha₁, this⟩, rfl⟩, rfl⟩, },
        { rintro (h | ⟨b, hb₁, hb₂⟩),
          { exact ha₂.1 h, },
          simp only [complete_atom_map_eq_of_not_mem_domain this] at hb₂,
          have : π A • b ∈ _ := (π A).atom_perm.map_domain hb₁.2,
          rw hb₂ at this,
          exact near_litter_approx.not_mem_domain_of_mem_largest_sublitter _
            (sublitter.order_iso_apply_mem _) this, }, },
      { by_cases a ∈ (π A).atom_perm.domain,
        { refine or.inl ⟨_, _⟩,
          { simp only [complete_atom_map_eq_of_mem_domain h],
            refine or.inr ⟨a, ⟨_, h⟩, rfl⟩,
            cases ha₁,
            cases ha ha₁.1,
            exact ha₁.1, },
          { simp only [mem_Union, mem_singleton_iff, not_exists, and_imp],
            intros b hb₁ hb₂ hab,
            rw [complete_atom_map_eq_of_mem_domain h,
              complete_atom_map_eq_of_not_mem_domain hb₂] at hab,
            have : π A • a ∈ _ := (π A).atom_perm.map_domain h,
            rw hab at this,
            exact near_litter_approx.not_mem_domain_of_mem_largest_sublitter _
              (sublitter.order_iso_apply_mem _) this, }, },
        { refine or.inr ⟨_, _⟩,
          { exact ⟨_, ⟨a, rfl⟩, _, ⟨⟨ha₁, h⟩, rfl⟩, rfl⟩, },
          rintro (h' | ⟨b, hb₁, hb₂⟩),
          { exact ha₂.1 h', },
          simp only [complete_atom_map_eq_of_not_mem_domain h] at hb₂,
          have : π A • b ∈ _ := (π A).atom_perm.map_domain hb₁.2,
          rw hb₂ at this,
          exact near_litter_approx.not_mem_domain_of_mem_largest_sublitter _
            (sublitter.order_iso_apply_mem _) this, }, }, }, },
end

lemma _root_.quiver.path.exists_eq_cons {V : Type*} [quiver V] {a b : V}
  (p : path a b) (h : a ≠ b) : ∃ (c : V) (q : path a c) (h : c ⟶ b), p = q.cons h :=
begin
  cases p with c _ q h,
  cases h rfl,
  exact ⟨c, q, h, rfl⟩,
end

lemma coherent {γ : Iio α} (A : path (β : type_index) γ)
  (N : near_litter) (B : extended_index γ)
  (c d : support_condition β) (hc : (inr N, A.comp B) <[α] c)
  (hπ : ((ihs_action π c d).comp A).lawful)
  (ρ : allowable γ)
  (h : (((ihs_action π c d).comp A).rc hπ).exactly_approximates ρ.to_struct_perm) :
  complete_near_litter_map π N (A.comp B) = struct_perm.derivative B ρ.to_struct_perm • N :=
begin
  revert A B N c d hc hπ ρ,
  refine well_founded.induction (inv_image.wf subtype.val Λwf.wf) γ _,
  clear γ,
  intros γ ih A B N c d hc hπ ρ h,
  have hdom : ((((ihs_action π c d).comp A B).refine (hπ B)).litter_map N.fst).dom :=
    or.inl (trans_gen_near_litter' hc),
  suffices : complete_litter_map π N.fst (A.comp B) =
    struct_perm.derivative B ρ.to_struct_perm • N.fst,
  { refine set_like.coe_injective _,
    refine eq.trans _ (near_litter_action.smul_near_litter_eq_of_precise_at
      _ (h B) hdom (near_litter_action.refine_precise _) this.symm).symm,
    rw complete_near_litter_map_eq' N (A.comp B),
    simp only [struct_action.refine_apply, struct_action.refine_litter_map,
      foa_hypothesis_near_litter_image, struct_perm.of_bot_smul],
    simp only [struct_action.comp_apply, ihs_action_litter_map, symm_diff_right_inj],
    ext a : 1,
    split,
    { rintro ⟨a, ha, rfl⟩,
      refine ⟨a, ha, _⟩,
      refine ((h B).map_atom a _).symm.trans _,
      { refine (or.inl (or.inl (or.inl (or.inl (or.inl _))))),
        exact relation.trans_gen.head (constrains.symm_diff N a ha _) hc, },
      { rw struct_action.rc_smul_atom_eq,
        refl,
        exact or.inl (relation.trans_gen.head (constrains.symm_diff N a ha _) hc), }, },
    { rintro ⟨a, ha, rfl⟩,
      refine ⟨a, ha, _⟩,
      refine eq.trans _ ((h B).map_atom a _),
      { rw struct_action.rc_smul_atom_eq,
        refl,
        exact or.inl (relation.trans_gen.head (constrains.symm_diff N a ha _) hc), },
      { refine (or.inl (or.inl (or.inl (or.inl (or.inl _))))),
        exact relation.trans_gen.head (constrains.symm_diff N a ha _) hc, }, }, },
  have hc' := trans_gen_near_litter' hc,
  generalize hNL : N.fst = L,
  rw hNL at hdom hc',
  obtain (hL | ⟨⟨hL⟩⟩ | ⟨⟨hL⟩⟩) := flexible_cases' (γ : Iic α) L B,
  { refine eq.trans _ ((h B).map_litter L _),
    { rw struct_action.rc_smul_litter_eq,
      rw near_litter_action.flexible_litter_perm_apply_eq,
      swap, exact hdom,
      swap, exact hL,
      exact (near_litter_action.rough_litter_map_or_else_of_dom _ hdom).symm, },
    { refine or.inl (or.inl _),
      refine ⟨hdom, hL⟩, }, },
  { rw complete_litter_map_eq_of_inflexible_bot (hL.comp A),
    obtain ⟨δ, ε, hε, C, a, rfl, rfl⟩ := hL,
    rw struct_perm.derivative_cons,
    refine eq.trans _ (struct_perm.derivative_bot_smul _ _).symm,
    rw struct_perm.derivative_cons,
    rw allowable.derivative_to_struct_perm (show path (γ : type_index) (δ : Iic_index α), from C),
    refine eq.trans _ (to_struct_perm_smul_f_map (δ : Iic_index α) ⊥ ε (bot_lt_coe _) _ _
      (allowable.derivative (show path (γ : type_index) (δ : Iic_index α), from _) ρ) a).symm,
    { intro h, cases h, },
    refine congr_arg _ _,
    rw ← allowable.derivative_cons_apply,
    refine eq.trans _ (((h $ C.cons (bot_lt_coe _)).map_atom a
      (or.inl (or.inl (or.inl (or.inl (or.inl (relation.trans_gen.head
        (constrains.f_map_bot hε _ _) hc'))))))).trans _),
    { rw struct_action.rc_smul_atom_eq,
      refl,
      exact or.inl (relation.trans_gen.head (constrains.f_map_bot hε _ _) hc'), },
    { have := allowable.to_struct_perm_smul
        (allowable.derivative (show path (γ : type_index) (⊥ : Iic_index α),
          from C.cons (bot_lt_coe _)) ρ) a,
      rw ← allowable.derivative_to_struct_perm at this,
      refine this.trans _,
      congr,
      ext π a : 4,
      change π.to_struct_perm.to_near_litter_perm.atom_perm a = π.atom_perm a,
      rw to_struct_perm_to_near_litter_perm, }, },
  { rw complete_litter_map_eq_of_inflexible_coe (hL.comp A),
    swap,
    { rw [inflexible_coe.comp_B, ← path.comp_cons, ← struct_action.comp_comp],
      refine struct_action.lawful.comp _ _,
      refine (hπ.le (struct_action.le_comp (ih_action_le_ihs_action π c d) _)).le _,
      exact struct_action.le_comp (ih_action_le hc'.to_refl) _, },
    swap, sorry,
    obtain ⟨δ, ε, ζ, hε, hζ, hεζ, C, t, rfl, rfl⟩ := hL,
    rw struct_perm.derivative_cons,
    refine eq.trans _ (struct_perm.derivative_bot_smul _ _).symm,
    rw struct_perm.derivative_cons,
    rw allowable.derivative_to_struct_perm (show path (γ : type_index) (δ : Iic_index α), from C),
    refine eq.trans _ (to_struct_perm_smul_f_map (δ : Iic_index α) ε ζ (coe_lt hε) _ _
      (allowable.derivative (show path (γ : type_index) (δ : Iic_index α), from C) ρ) t).symm,
    { intro h,
      refine hεζ (subtype.ext _),
      have := congr_arg subtype.val h,
      exact coe_injective this, },
    refine congr_arg _ _,
    rw [← allowable.derivative_cons_apply, ← inv_smul_eq_iff, smul_smul],
    refine (designated_support t).supports _ _,
    intros c hct,
    rw [mul_smul, inv_smul_eq_iff],
    obtain ⟨a | M, D⟩ := c,
    { refine prod.ext _ rfl,
      change inl _ = inl _,
      simp only,
      rw [← allowable.derivative_to_struct_perm, struct_perm.derivative_derivative],
      refine eq.trans _ ((h _).map_atom a _),
      refine (((ih_action _ ).hypothesised_allowable_exactly_approximates
        ⟨δ, ε, ζ, hε, hζ, hεζ, A.comp C, t, rfl, rfl⟩ _ _ D).map_atom a _).symm.trans _,
      { refine or.inl (or.inl (or.inl (or.inl _))),
        exact relation.trans_gen.single (constrains.f_map _ _ _ _ _ _ hct), },
      { rw [struct_action.rc_smul_atom_eq, struct_action.rc_smul_atom_eq],
        { simp only [struct_action.comp_apply, ih_action_atom_map, foa_hypothesis_atom_image,
            ihs_action_atom_map],
          simp_rw ← path.comp_cons,
          rw path.comp_assoc, },
        { refine or.inl (relation.trans_gen.head _ hc'),
          exact constrains_comp (constrains.f_map _ _ _ _ _ _ hct) A, },
        { simp only [struct_action.comp_apply, ih_action_atom_map],
          simp_rw ← path.comp_cons,
          rw path.comp_assoc,
          exact relation.trans_gen.single
            (constrains_comp (constrains.f_map _ _ _ _ _ _ hct) A), }, },
      { refine or.inl (or.inl (or.inl (or.inl (or.inl _)))),
        refine relation.trans_gen.head _ hc',
        exact constrains_comp (constrains.f_map _ _ _ _ _ _ hct) A, }, },
    { refine prod.ext _ rfl,
      change inr _ = inr _,
      simp only,
      specialize ih ε (lt_of_lt_of_le hε (coe_le_coe.mp (le_of_path C)))
        ((A.comp C).cons $ coe_lt hε) D M,
      have := ih c d _ _ (allowable.derivative _ ρ) _,
      rw ih _ _ _ _ (((ih_action π.foa_hypothesis).hypothesised_allowable
        ⟨δ, ε, ζ, hε, hζ, hεζ, A.comp C, t, rfl, rfl⟩ _ _)) at this,
      exact this,
      { have := struct_action.hypothesised_allowable_exactly_approximates
          (ih_action _) ⟨δ, ε, ζ, hε, hζ, hεζ, A.comp C, t, rfl, rfl⟩ _ _,
        refine struct_approx.exactly_approximates_of_eq this _,
        swap 4,
        simp_rw ← ihs_action_self, },
      { rw [path.comp_cons, path.comp_cons],
        exact relation.trans_gen.single (constrains.f_map _ _ _ _ _ _ hct), },
      { refine relation.trans_gen.head _ (trans_gen_near_litter' hc),
        rw hNL,
        rw [path.comp_cons, path.comp_cons],
        exact constrains.f_map _ hζ _ _ t _ hct, },
      { rw [← path.comp_cons, ← struct_action.comp_comp],
        exact hπ.comp _, },
      { rw ← allowable.derivative_to_struct_perm,
        intro E,
        rw struct_perm.derivative_derivative,
        sorry,
        -- refine near_litter_approx.exactly_approximates_of_eq (h ((C.cons _).comp E)) _,
        -- simp_rw [← path.comp_cons, ← struct_action.rc_comp, struct_action.comp_comp],
         }, }, },
end

def in_out (π : near_litter_perm) (a : atom) (L : litter) : Prop :=
xor ((π • a).1 = π • L) (a.1 = L)

lemma in_out_def {π : near_litter_perm} {a : atom} {L : litter} :
  in_out π a L ↔ xor ((π • a).1 = π • L) (a.1 = L) := iff.rfl

structure _root_.con_nf.near_litter_perm.biexact (π π' : near_litter_perm)
  (atoms : set atom) (litters : set litter) : Prop :=
(smul_eq_smul_atom : ∀ a ∈ atoms, π • a = π' • a)
(smul_eq_smul_litter : ∀ L ∈ litters, π • L = π' • L)
(left_exact : ∀ L ∈ litters, ∀ a, in_out π a L → π • a = π' • a)
(right_exact : ∀ L ∈ litters, ∀ a, in_out π' a L → π • a = π' • a)

@[simp] lemma _root_.xor_elim_left {a b : Prop} (h : a) : xor a b ↔ ¬b :=
by unfold xor; tauto

@[simp] lemma _root_.xor_elim_right {a b : Prop} (h : b) : xor a b ↔ ¬a :=
by unfold xor; tauto

@[simp] lemma _root_.xor_elim_not_left {a b : Prop} (h : ¬a) : xor a b ↔ b :=
by unfold xor; tauto

@[simp] lemma _root_.xor_elim_not_right {a b : Prop} (h : ¬b) : xor a b ↔ a :=
by unfold xor; tauto

lemma _root_.con_nf.near_litter_perm.biexact.atoms
  {π π' : near_litter_perm} (s : set atom) (hs : ∀ a ∈ s, π • a = π' • a) :
  near_litter_perm.biexact π π' s ∅ :=
⟨hs, λ L, false.elim, λ L, false.elim, λ L, false.elim⟩

lemma _root_.con_nf.near_litter_perm.biexact.litter
  {π π' : near_litter_perm} (L : litter)
  (hL : π • L = π' • L)
  (hL₁ : ∀ a, in_out π a L → π • a = π' • a)
  (hL₂ : ∀ a, in_out π' a L → π • a = π' • a) :
  near_litter_perm.biexact π π' ∅ {L} :=
⟨
  λ a ha, ha.elim,
  λ L' hL', by cases hL'; exact hL,
  λ L' hL', by cases hL'; exact hL₁,
  λ L' hL', by cases hL'; exact hL₂,
⟩

lemma _root_.con_nf.near_litter_perm.biexact.symm
  {π π' : near_litter_perm} {atoms : set atom} {litters : set litter}
  (h : near_litter_perm.biexact π π' atoms litters) :
  near_litter_perm.biexact π' π atoms litters :=
⟨
  λ a ha, (h.smul_eq_smul_atom a ha).symm,
  λ L hL, (h.smul_eq_smul_litter L hL).symm,
  λ L hL a ha, (h.right_exact L hL a ha).symm,
  λ L hL a ha, (h.left_exact L hL a ha).symm,
⟩

lemma _root_.con_nf.near_litter_perm.biexact.union
  {π π' : near_litter_perm} {s₁ s₂ : set atom} {t₁ t₂ : set litter}
  (h₁ : near_litter_perm.biexact π π' s₁ t₁)
  (h₂ : near_litter_perm.biexact π π' s₂ t₂) :
  near_litter_perm.biexact π π' (s₁ ∪ s₂) (t₁ ∪ t₂) :=
⟨
  λ a ha, ha.elim (h₁.smul_eq_smul_atom a) (h₂.smul_eq_smul_atom a),
  λ L hL, hL.elim (h₁.smul_eq_smul_litter L) (h₂.smul_eq_smul_litter L),
  λ L hL, hL.elim (h₁.left_exact L) (h₂.left_exact L),
  λ L hL, hL.elim (h₁.right_exact L) (h₂.right_exact L),
⟩

lemma _root_.con_nf.near_litter_perm.biexact.smul_litter_subset
  {π π' : near_litter_perm} {atoms : set atom} {litters : set litter}
  (h : near_litter_perm.biexact π π' atoms litters)
  (L : litter) (hL : L ∈ litters) :
  (π • L.to_near_litter : set atom) ⊆ π' • L.to_near_litter :=
begin
  rintros _ ⟨a, ha, rfl⟩,
  simp only [litter.coe_to_near_litter, mem_litter_set] at ha,
  by_cases h' : (π • a).1 = π • L,
  by_cases h'' : (π'⁻¹ • π • a).1 = L,
  { refine ⟨_, h'', _⟩,
    rw smul_inv_smul, },
  { have := h.right_exact L hL _ (or.inl ⟨_, h''⟩),
    { rw [smul_inv_smul, smul_left_cancel_iff, inv_smul_eq_iff] at this,
      rw this,
      exact ⟨a, ha, rfl⟩, },
    { rw [smul_inv_smul, h', h.smul_eq_smul_litter L hL], }, },
  { rw h.left_exact L hL a (or.inr ⟨ha, h'⟩),
    simp only [litter.coe_to_near_litter, smul_mem_smul_set_iff, mem_litter_set],
    exact ha, },
end

lemma _root_.con_nf.near_litter_perm.biexact.smul_litter
  {π π' : near_litter_perm} {atoms : set atom} {litters : set litter}
  (h : near_litter_perm.biexact π π' atoms litters)
  (L : litter) (hL : L ∈ litters) :
  π • L.to_near_litter = π' • L.to_near_litter :=
begin
  refine set_like.coe_injective _,
  refine subset_antisymm _ _,
  exact h.smul_litter_subset L hL,
  exact h.symm.smul_litter_subset L hL,
end

lemma _root_.con_nf.near_litter_perm.biexact.smul_near_litter
  {π π' : near_litter_perm} {atoms : set atom} {litters : set litter}
  (h : near_litter_perm.biexact π π' atoms litters)
  (N : near_litter) (hN : N.1 ∈ litters) (hN' : litter_set N.1 ∆ N ⊆ atoms) :
  π • N = π' • N :=
begin
  refine set_like.coe_injective _,
  change _ • _ = _ • _,
  conv_lhs { rw near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul, },
  conv_rhs { rw near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul, },
  refine congr_arg2 _
    (congr_arg set_like.coe (h.smul_litter N.1 hN)) _,
  ext a : 1,
  split,
  { rintro ⟨b, hb, rfl⟩,
    rw h.smul_eq_smul_atom b (hN' hb),
    exact ⟨b, hb, rfl⟩, },
  { rintro ⟨b, hb, rfl⟩,
    rw ← h.smul_eq_smul_atom b (hN' hb),
    exact ⟨b, hb, rfl⟩, },
end

-- `in_out` is just another way to quantify exceptions, focusing on a slightly different litter.
-- Basically `in_out` looks only at images not preimages.
example (π : near_litter_perm) (a : atom) (L : litter) :
  in_out π a L → π.is_exception a ∨ π.is_exception (π • a) :=
begin
  rintro (ha | ⟨rfl, ha⟩),
  { refine or.inl (or.inl _),
    rw [mem_litter_set, ha.1, smul_left_cancel_iff],
    exact ne.symm ha.2, },
  { refine or.inr (or.inr _),
    intro h,
    rw [mem_litter_set, eq_inv_smul_iff] at h,
    rw [← h, inv_smul_smul] at ha,
    exact ha rfl, },
end

structure biexact {β : Iio α} (π π' : struct_perm β) (c : support_condition β) : Prop :=
(smul_eq_smul_atom : ∀ A : extended_index β, ∀ a : atom,
  (inl a, A) ≤[α] c →
  struct_perm.derivative A π • a = struct_perm.derivative A π' • a)
(smul_eq_smul_litter : ∀ A : extended_index β, ∀ L : litter,
  (inr L.to_near_litter, A) ≤[α] c → flexible α L A →
  struct_perm.derivative A π • L = struct_perm.derivative A π' • L)
(left_exact : ∀ A : extended_index β, ∀ L : litter, ∀ a : atom,
  (inr L.to_near_litter, A) ≤[α] c → in_out (struct_perm.of_bot $ struct_perm.derivative A π) a L →
  struct_perm.derivative A π • a = struct_perm.derivative A π' • a)
(right_exact : ∀ A : extended_index β, ∀ L : litter, ∀ a : atom,
  (inr L.to_near_litter, A) ≤[α] c → in_out (struct_perm.of_bot $ struct_perm.derivative A π') a L →
  struct_perm.derivative A π • a = struct_perm.derivative A π' • a)

lemma biexact.atoms {β : Iio α} {π π' : struct_perm β} {c : support_condition β}
  (h : biexact π π' c) (A : extended_index β) :
  near_litter_perm.biexact
    (struct_perm.of_bot $ struct_perm.derivative A π)
    (struct_perm.of_bot $ struct_perm.derivative A π')
    {a | (inl a, A) ≤[α] c}
    ∅ :=
near_litter_perm.biexact.atoms _ (h.smul_eq_smul_atom A)

lemma biexact.constrains {β : Iio α} {π π' : struct_perm β} {c d : support_condition β}
  (h : biexact π π' c) (h' : d ≤[α] c) : biexact π π' d :=
⟨
  λ A a ha, h.smul_eq_smul_atom A a (ha.trans h'),
  λ A L hL, h.smul_eq_smul_litter A L (hL.trans h'),
  λ A L a hL, h.left_exact A L a (hL.trans h'),
  λ A L a hL, h.right_exact A L a (hL.trans h'),
⟩

lemma biexact.smul_eq_smul {β : Iio α} {π π' : allowable β} {c : support_condition β}
  (h : biexact π.to_struct_perm π'.to_struct_perm c) : π • c = π' • c :=
begin
  revert h,
  refine well_founded.induction (constrains_wf α β) c _,
  clear c,
  intros c ih h,
  obtain ⟨a | N, A⟩ := c;
  refine prod.ext _ rfl,
  { change inl _ = inl _,
    simp only,
    exact h.smul_eq_smul_atom A a relation.refl_trans_gen.refl, },
  change inr _ = inr _,
  simp only,
  by_cases hL : N.is_litter,
  swap,
  { have := ih _ (constrains.near_litter N (near_litter.not_is_litter hL) A)
      (h.constrains (refl_trans_gen_near_litter relation.refl_trans_gen.refl)),
    change (inr _, _) = (inr _, _) at this,
    simp only [prod.mk.inj_iff, eq_self_iff_true, and_true] at this,
    refine set_like.coe_injective _,
    refine (near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul _ _).trans _,
    refine eq.trans _ (near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul _ _).symm,
    refine congr_arg2 _ (congr_arg set_like.coe this) _,
    ext a : 1,
    split,
    { rintro ⟨b, hb, rfl⟩,
      have : (inl _, _) = (inl _, _) := ih _ (constrains.symm_diff N b hb A)
        (h.constrains (relation.refl_trans_gen.single $ constrains.symm_diff N b hb A)),
      simp only [prod.mk.inj_iff, eq_self_iff_true, and_true] at this,
      exact ⟨b, hb, this.symm⟩, },
    { rintro ⟨b, hb, rfl⟩,
      have : (inl _, _) = (inl _, _) := ih _ (constrains.symm_diff N b hb A)
        (h.constrains (relation.refl_trans_gen.single $ constrains.symm_diff N b hb A)),
      simp only [prod.mk.inj_iff, eq_self_iff_true, and_true] at this,
      exact ⟨b, hb, this⟩, }, },
  obtain ⟨L, rfl⟩ := hL.exists_litter_eq,
  suffices : struct_perm.derivative A π.to_struct_perm • L =
    struct_perm.derivative A π'.to_struct_perm • L,
  { have := near_litter_perm.biexact.litter L this _ _,
    { refine (this.union (h.atoms A)).smul_near_litter L.to_near_litter (or.inl rfl) _,
      intros a ha,
      rw [litter.to_near_litter_fst, litter.coe_to_near_litter, symm_diff_self] at ha,
      cases ha, },
    { intros a ha,
      exact h.left_exact A L a relation.refl_trans_gen.refl ha, },
    { intros a ha,
      exact h.right_exact A L a relation.refl_trans_gen.refl ha, }, },
  obtain (hL | hL) := flexible_cases α L A,
  swap,
  { exact h.smul_eq_smul_litter A L relation.refl_trans_gen.refl hL, },
  induction hL with γ δ ε hδ hε hδε B t γ ε hε B a,
  { rw [struct_perm.derivative_cons, struct_perm.derivative_bot_smul, struct_perm.derivative_cons],
    rw allowable.derivative_to_struct_perm (show path (β : type_index) (γ : Iic_index α), from _),
    refine (to_struct_perm_smul_f_map
      (γ : Iic_index α) δ ε (coe_lt hδ) (coe_lt hε) (Iio.coe_injective.ne hδε) _ _).trans _,
    rw [struct_perm.derivative_cons, struct_perm.derivative_bot_smul, struct_perm.derivative_cons],
    rw allowable.derivative_to_struct_perm (show path (β : type_index) (γ : Iic_index α), from _),
    refine eq.trans _ (to_struct_perm_smul_f_map
      (γ : Iic_index α) δ ε (coe_lt hδ) (coe_lt hε) (Iio.coe_injective.ne hδε) _ _).symm,
    refine congr_arg _ _,
    rw [← inv_smul_eq_iff, smul_smul],
    refine (designated_support t).supports _ _,
    intros c hc,
    rw [mul_smul, inv_smul_eq_iff],
    rw [← allowable.to_struct_perm_smul, ← allowable.to_struct_perm_smul,
      ← allowable.derivative_cons_apply, ← allowable.derivative_cons_apply,
      ← allowable.derivative_to_struct_perm, ← allowable.derivative_to_struct_perm],
    have := ih (c.fst, (B.cons $ coe_lt hδ).comp c.snd) _ _,
    { refine prod.ext _ rfl,
      apply_fun prod.fst at this,
      change _ • _ = _ • _,
      rw [struct_perm.derivative_derivative, struct_perm.derivative_derivative],
      exact this, },
    { exact constrains.f_map _ _ _ _ _ _ hc, },
    { refine h.constrains (relation.refl_trans_gen.single _),
      exact constrains.f_map _ _ _ _ _ _ hc, }, },
  { rw [struct_perm.derivative_cons, struct_perm.derivative_bot_smul, struct_perm.derivative_cons],
    rw allowable.derivative_to_struct_perm (show path (β : type_index) (γ : Iic_index α), from _),
    refine (to_struct_perm_smul_f_map
      (γ : Iic_index α) ⊥ ε (bot_lt_coe _) (coe_lt hε) Iio_index.bot_ne_coe _ _).trans _,
    rw [struct_perm.derivative_cons, struct_perm.derivative_bot_smul, struct_perm.derivative_cons],
    rw allowable.derivative_to_struct_perm (show path (β : type_index) (γ : Iic_index α), from _),
    refine eq.trans _ (to_struct_perm_smul_f_map
      (γ : Iic_index α) ⊥ ε (bot_lt_coe _) (coe_lt hε) Iio_index.bot_ne_coe _ _).symm,
    refine congr_arg _ _,
    rw [← allowable.derivative_cons_apply, ← allowable.derivative_cons_apply],
    have := ih (inl a, B.cons $ bot_lt_coe _) _ _,
    { change (inl _, _) = (inl _, _) at this,
      simp only [prod.mk.inj_iff, eq_self_iff_true, and_true] at this,
      rw allowable.derivative_to_struct_perm
        (show path (β : type_index) (⊥ : Iic_index α), from _) at this,
      rw allowable.derivative_to_struct_perm
        (show path (β : type_index) (⊥ : Iic_index α), from _) at this,
      rw allowable.to_struct_perm_smul at this,
      rw allowable.to_struct_perm_smul at this,
      dsimp only,
      convert this using 2;
      { rw to_struct_perm_to_near_litter_perm, refl, }, },
    { exact constrains.f_map_bot _ _ _, },
    { refine h.constrains (relation.refl_trans_gen.single _),
      exact constrains.f_map_bot _ _ _, }, },
end


end struct_approx

end con_nf
