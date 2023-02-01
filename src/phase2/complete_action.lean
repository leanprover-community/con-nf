import phase2.near_litter_completion

open function quiver set sum with_bot
open_locale classical

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

noncomputable def complete_litter_map (π : struct_approx β) (L : litter) (A : extended_index β) :
  litter :=
(π.complete_near_litter_map L.to_near_litter A).1

noncomputable def foa_hypothesis (π : struct_approx β) {c : support_condition β} : hypothesis c :=
⟨λ b B hb, π.complete_atom_map b B, λ N B hb, π.complete_near_litter_map N B⟩

variable {π : struct_approx β}

section map_spec
variables {a : atom} {L : litter} {N : near_litter} {A : extended_index β}

lemma complete_atom_map_eq :
  π.complete_atom_map a A = π.atom_completion a A π.foa_hypothesis :=
hypothesis.fix_atom_eq _ _ _ _

lemma complete_near_litter_map_eq :
  π.complete_near_litter_map N A = π.near_litter_completion N A π.foa_hypothesis :=
hypothesis.fix_near_litter_eq _ _ _ _

lemma complete_litter_map_eq :
  π.complete_litter_map L A = (π.complete_near_litter_map L.to_near_litter A).1 := rfl

@[simp] lemma foa_hypothesis_atom_image {c : support_condition β}
  (h : relation.trans_gen (constrains α β) (inl a, A) c) :
  (π.foa_hypothesis : hypothesis c).atom_image a A h = π.complete_atom_map a A := rfl

@[simp] lemma foa_hypothesis_near_litter_image {c : support_condition β}
  (h : relation.trans_gen (constrains α β) (inr N, A) c) :
  (π.foa_hypothesis : hypothesis c).near_litter_image N A h = π.complete_near_litter_map N A := rfl

end map_spec

lemma complete_atom_map_eq_of_mem_domain {a} {A} (h : a ∈ (π A).atom_perm.domain) :
  π.complete_atom_map a A = π A • a :=
by rw [complete_atom_map_eq, atom_completion, dif_pos h]

lemma complete_atom_map_eq_of_not_mem_domain {a} {A} (h : a ∉ (π A).atom_perm.domain) :
  π.complete_atom_map a A = sublitter_bijection
    ((π A).largest_sublitter a.1)
    ((π A).largest_sublitter (π.complete_litter_map a.1 A))
    ⟨a, (π A).mem_largest_sublitter_of_not_mem_domain a h⟩ :=
by rw [complete_atom_map_eq, atom_completion, dif_neg h]; refl

/-- The inductive hypothesis used to prove that the induced action generated in the freedom of
action theorem is lawful. This is to be proven by well-founded recursion on `c`. -/
structure foa_props (π : struct_approx β) (c : support_condition β) : Prop :=
(atom_injective : ∀ a b (B : extended_index β),
  (relation.trans_gen (constrains α β)) ⟨inl a, B⟩ c →
  (relation.trans_gen (constrains α β)) ⟨inl b, B⟩ c →
  π.complete_atom_map a B = π.complete_atom_map b B → a = b)
(litter_injective : ∀ (L₁ L₂ : litter) (B : extended_index β),
  (relation.trans_gen (constrains α β)) ⟨inr L₁.to_near_litter, B⟩ c →
  (relation.trans_gen (constrains α β)) ⟨inr L₂.to_near_litter, B⟩ c →
  π.complete_litter_map L₁ B = π.complete_litter_map L₂ B → L₁ = L₂)

lemma eq_of_sublitter_bijection_apply_eq {π : near_litter_approx} {L₁ L₂ L₃ L₄ : litter} {a b} :
  ((sublitter_bijection (π.largest_sublitter L₁) (π.largest_sublitter L₂)) a : atom) =
  (sublitter_bijection (π.largest_sublitter L₃) (π.largest_sublitter L₄)) b →
  L₁ = L₃ → L₂ = L₄ → (a : atom) = b :=
begin
  rintros h₁ rfl rfl,
  simp only [subtype.coe_inj, embedding_like.apply_eq_iff_eq] at h₁,
  rw h₁,
end

/-- We show that injectivity of the atom map extends to atoms below the current support condition
`c`, given that certain properties hold for support conditions before `c`. -/
lemma atom_injective_extends {c : support_condition β} (H : π.foa_props c)
  {a b : atom} {A : extended_index β}
  (hac : (relation.refl_trans_gen (constrains α β)) ⟨inl a, A⟩ c)
  (hbc : (relation.refl_trans_gen (constrains α β)) ⟨inl b, A⟩ c)
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
    have h₂ := (sublitter_bijection
      ((π A).largest_sublitter b.1)
      ((π A).largest_sublitter (π.complete_litter_map b.1 A))
      ⟨b, (π A).mem_largest_sublitter_of_not_mem_domain b hb⟩).prop.1,
    have := H.litter_injective _ _ _
      (relation.trans_gen.head' (constrains.atom a A) hac)
      (relation.trans_gen.head' (constrains.atom b A) hbc)
      (h₁.symm.trans h₂),
    have := eq_of_sublitter_bijection_apply_eq h this (by rw this),
    rw [set_like.coe_mk, set_like.coe_mk] at this,
    exact this, },
end

/-!
We now start proving properties of the litter map.
First, we unfold the definition of the completed action.
-/

@[simp] def near_litter_hypothesis_eq (N : near_litter) (A : extended_index β) :
  near_litter_hypothesis N A π.foa_hypothesis = π.foa_hypothesis := rfl

/-- A basic definition unfold. -/
lemma complete_litter_map_eq_of_inflexible_coe {L : litter} {A : extended_index β}
  (h : inflexible_coe L A) :
  π.complete_litter_map L A = if hf : @struct_approx.free _ _ _ _ (h.δ : Iic α)
      (inflexible_litter_completion h.hδ h.hε h.hδε
        (π.foa_hypothesis :
          hypothesis ⟨inr (f_map (coe_ne_coe.mpr $ coe_ne' h.hδε) h.t).to_near_litter,
            (h.B.cons (coe_lt h.hε)).cons (bot_lt_coe _)⟩) _) then
      f_map (with_bot.coe_ne_coe.mpr $ coe_ne' h.hδε)
        ((freedom_of_action_of_lt (h.δ : Iic α) h.δ_lt_β
          (inflexible_litter_completion h.hδ h.hε h.hδε
            π.foa_hypothesis
            (λ B, π (path.cons (path.cons h.B (coe_lt h.hδ))
              (with_bot.bot_lt_coe h.δ))))
          hf).some • h.t)
    else
      L :=
begin
  rw [complete_litter_map_eq, complete_near_litter_map_eq, near_litter_completion],
  dsimp only,
  have : nonempty (inflexible_coe L.to_near_litter.fst A) := ⟨h⟩,
  rw [litter_completion, dif_pos this],
  cases subsingleton.elim this.some h,
  refl,
end

/-- A basic definition unfold. -/
lemma complete_litter_map_eq_of_inflexible_bot {L : litter} {A : extended_index β}
  (h : inflexible_bot L A) :
  π.complete_litter_map L A =
  f_map (show (⊥ : type_index) ≠ (h.ε : Λ), from with_bot.bot_ne_coe)
    (π.complete_atom_map h.a (h.B.cons (with_bot.bot_lt_coe _))) :=
begin
  rw [complete_litter_map_eq, complete_near_litter_map_eq, near_litter_completion],
  dsimp only,
  have h₁ : ¬nonempty (inflexible_coe L.to_near_litter.fst A) :=
    λ h', inflexible_bot_inflexible_coe h h'.some,
  have h₂ : nonempty (inflexible_bot L.to_near_litter.fst A) := ⟨h⟩,
  rw [litter_completion, dif_neg h₁, dif_pos h₂],
  cases subsingleton.elim h₂.some h,
  refl,
end

/-- A basic definition unfold. -/
lemma complete_litter_map_eq_of_flexible {L : litter} {A : extended_index β}
  (h₁ : inflexible_bot L A → false) (h₂ : inflexible_coe L A → false) :
  π.complete_litter_map L A = near_litter_approx.flexible_completion α (π A) A • L :=
begin
  rw [complete_litter_map_eq, complete_near_litter_map_eq, near_litter_completion],
  dsimp only,
  rw [litter_completion,
    dif_neg (show ¬nonempty (inflexible_coe L.to_near_litter.fst A), from λ h, h₂ h.some),
    dif_neg (show ¬nonempty (inflexible_bot L.to_near_litter.fst A), from λ h, h₁ h.some)],
  refl,
end

/-!
Lemmas about the proof-relevant `inflexible_*` objects.
-/

lemma inflexible_of_inflexible_bot {L : litter} {A : extended_index β} (h : inflexible_bot L A) :
  inflexible α L A :=
begin
  have := inflexible.mk_bot h.hε h.B h.a,
  rw [← h.hL, ← h.hA] at this,
  exact this,
end

lemma inflexible_of_inflexible_coe {L : litter} {A : extended_index β} (h : inflexible_coe L A) :
  inflexible α L A :=
begin
  have := inflexible.mk_coe h.hδ h.hε h.hδε h.B h.t,
  rw [← h.hL, ← h.hA] at this,
  exact this,
end

lemma inflexible_bot_or_inflexible_coe_of_inflexible {L : litter} {A : extended_index β}
  (h : inflexible α L A) : nonempty (inflexible_bot L A) ∨ nonempty (inflexible_coe L A) :=
begin
  obtain ⟨hδ, hε, hδε, B, t⟩ | ⟨hε, B, a⟩ := h,
  { refine or.inr ⟨⟨_, _, _, _, _, _, _, _, rfl, rfl⟩⟩,
    assumption, },
  { exact or.inl ⟨⟨_, _, _, _, _, rfl, rfl⟩⟩, },
end

lemma flexible_iff_not_inflexible_bot_coe {L : litter} {A : extended_index β} :
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

lemma litter_injective_extends {c : support_condition β} (H : π.foa_props c)
  {L₁ L₂ : litter} {A : extended_index β}
  (hac : (relation.refl_trans_gen (constrains α β)) ⟨inr L₁.to_near_litter, A⟩ c)
  (hbc : (relation.refl_trans_gen (constrains α β)) ⟨inr L₂.to_near_litter, A⟩ c)
  (h : π.complete_litter_map L₁ A = π.complete_litter_map L₂ A) :
  L₁ = L₂ := sorry

end struct_approx

end con_nf
