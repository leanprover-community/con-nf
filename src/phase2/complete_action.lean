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

/-!
We now start proving properties of the litter map.
First, we unfold the definition of the completed action.
-/

@[simp] def near_litter_hypothesis_eq (N : near_litter) (A : extended_index β) :
  near_litter_hypothesis N A (π.foa_hypothesis hπ) = (π.foa_hypothesis hπ) := rfl

/-- A basic definition unfold. -/
lemma complete_litter_map_eq_of_inflexible_coe (hπ : π.free) {L : litter} {A : extended_index β}
  (h : inflexible_coe L A) :
  π.complete_litter_map hπ L A = f_map (with_bot.coe_ne_coe.mpr $ coe_ne' h.hδε)
    (supported_perm π hπ h (π.foa_hypothesis hπ) • h.t) :=
begin
  have : nonempty (inflexible_coe L A) := ⟨h⟩,
  rw [complete_litter_map_eq, litter_completion, dif_pos this],
  cases subsingleton.elim this.some h,
  refl,
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
    exact this, },
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
end

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
  (hcL : (relation.refl_trans_gen (constrains α β)) ⟨inr L.to_near_litter, A⟩ c) (C a ha b hb)
  (hab : (inflexible_support_map (π.foa_hypothesis hπ)
    ⟨γ, δ, ε, hδ, hε, hδε, B, t, hL, hA⟩).atom_image a C ha =
  (inflexible_support_map (π.foa_hypothesis hπ)
    ⟨γ, δ, ε, hδ, hε, hδε, B, t, hL, hA⟩).atom_image b C hb) :
  a = b :=
begin
  unfold inflexible_support_map at hab,
  simp only [foa_hypothesis_atom_image] at hab,
  refine H.atom_injective _ _ _ _ _ hab,
  { refine relation.trans_gen.trans_left _ (by rw [hL, hA] at hcL; exact hcL),
    dsimp only [inflexible_support_map, inflexible_support, mem_preimage] at ha,
    rw reduction_singleton_of_not_reduced at ha,
    exact ha.1,
    rw not_reduced_iff,
    exact λ _, inflexible.mk_coe hδ hε hδε _ _, },
  { refine relation.trans_gen.trans_left _ (by rw [hL, hA] at hcL; exact hcL),
    dsimp only [inflexible_support_map, inflexible_support, mem_preimage] at hb,
    rw reduction_singleton_of_not_reduced at hb,
    exact hb.1,
    rw not_reduced_iff,
    exact λ _, inflexible.mk_coe hδ hε hδε _ _, },
end

lemma near_litter_image_inj_on {π : struct_approx β} (hπ : π.free)
  {c : support_condition β} (H : π.foa_props hπ c) {γ : Iic α} {δ ε : Iio α}
  {B : path (β : type_index) γ} {t : tangle δ} {L A} (hδ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
  (hL : L = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t)
  (hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _))
  (hcL : (relation.refl_trans_gen (constrains α β)) ⟨inr L.to_near_litter, A⟩ c)
  (C) (L₁ : litter) (hL₁) (L₂ : litter) (hL₂)
  (hL : (((inflexible_support_map (π.foa_hypothesis hπ)
    ⟨γ, δ, ε, hδ, hε, hδε, B, t, hL, hA⟩).near_litter_image L₁.to_near_litter C hL₁ : set atom) ∩
  (inflexible_support_map (π.foa_hypothesis hπ)
    ⟨γ, δ, ε, hδ, hε, hδε, B, t, hL, hA⟩).near_litter_image L₂.to_near_litter C hL₂).nonempty) :
  L₁ = L₂ :=
begin
  unfold inflexible_support_map at hL,
  simp only [foa_hypothesis_near_litter_image] at hL,
  obtain ⟨a, ha₁, ha₂⟩ := hL,
  simp only [complete_near_litter_map_eq] at ha₁ ha₂,
  obtain ⟨ha₁ | ha₁, ha₃⟩ := ha₁;
  obtain ⟨ha₂ | ha₂, ha₄⟩ := ha₂,
  { have := eq_of_mem_litter_set_of_mem_litter_set
      (sublitter.subset _ ha₁) (sublitter.subset _ ha₂),
    simp only [near_litter_hypothesis_eq, near_litter_approx.largest_sublitter_litter] at this,
    refine H.litter_injective L₁ L₂ ((B.cons $ coe_lt hδ).comp C) _ _ _,
    { -- TODO: Factor this out.
      refine relation.trans_gen.trans_left _ (by rw [hL, hA] at hcL; exact hcL),
      dsimp only [inflexible_support_map, inflexible_support, mem_preimage] at hL₁,
      rw reduction_singleton_of_not_reduced at hL₁,
      exact hL₁.1,
      rw not_reduced_iff,
      exact λ _, inflexible.mk_coe hδ hε hδε _ _, },
    { refine relation.trans_gen.trans_left _ (by rw [hL, hA] at hcL; exact hcL),
      dsimp only [inflexible_support_map, inflexible_support, mem_preimage] at hL₂,
      rw reduction_singleton_of_not_reduced at hL₂,
      exact hL₂.1,
      rw not_reduced_iff,
      exact λ _, inflexible.mk_coe hδ hε hδε _ _, },
    { rw [complete_litter_map_eq, complete_litter_map_eq],
      exact this, }, },
  { obtain ⟨b, hb, rfl⟩ := ha₂,
    have : b ∈ (π ((B.cons $ coe_lt hδ).comp C)).atom_perm.domain,
    -- TODO: Factor out this block.
    { contrapose! hb,
      intro h,
      simp only [litter.coe_to_near_litter, litter.to_near_litter_fst,
        near_litter_approx.coe_largest_sublitter, sdiff_sdiff_right_self, inf_eq_inter,
        mem_inter_iff, mem_litter_set] at h,
      exact hb h.2, },
    have := (π ((B.cons $ coe_lt hδ).comp C)).atom_perm.map_domain this,
    cases near_litter_approx.not_mem_domain_of_mem_largest_sublitter _ ha₁ this, },
  { obtain ⟨b, hb, rfl⟩ := ha₁,
    have : b ∈ (π ((B.cons $ coe_lt hδ).comp C)).atom_perm.domain,
    { contrapose! hb,
      intro h,
      simp only [litter.coe_to_near_litter, litter.to_near_litter_fst,
        near_litter_approx.coe_largest_sublitter, sdiff_sdiff_right_self, inf_eq_inter,
        mem_inter_iff, mem_litter_set] at h,
      exact hb h.2, },
    have := (π ((B.cons $ coe_lt hδ).comp C)).atom_perm.map_domain this,
    cases near_litter_approx.not_mem_domain_of_mem_largest_sublitter _ ha₂ this, },
  { obtain ⟨b, hb₁, hb₂⟩ := ha₁,
    obtain ⟨c, hc₁, hc₂⟩ := ha₂,
    have hb : b ∈ (π ((B.cons $ coe_lt hδ).comp C)).atom_perm.domain,
    { contrapose! hb₁,
      intro h,
      simp only [litter.coe_to_near_litter, litter.to_near_litter_fst,
        near_litter_approx.coe_largest_sublitter, sdiff_sdiff_right_self, inf_eq_inter,
        mem_inter_iff, mem_litter_set] at h,
      exact hb₁ h.2, },
    have hc : c ∈ (π ((B.cons $ coe_lt hδ).comp C)).atom_perm.domain,
    { contrapose! hc₁,
      intro h,
      simp only [litter.coe_to_near_litter, litter.to_near_litter_fst,
        near_litter_approx.coe_largest_sublitter, sdiff_sdiff_right_self, inf_eq_inter,
        mem_inter_iff, mem_litter_set] at h,
      exact hc₁ h.2, },
    rw ← hc₂ at hb₂,
    cases (π ((B.cons $ coe_lt hδ).comp C)).atom_perm.inj_on hb hc hb₂,
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
  (inflexible_support_map (π.foa_hypothesis hπ)
    ⟨γ, δ, ε, hδ, hε, hδε, B, t, hL, hA⟩).injective C :=
⟨atom_image_inj_on hπ H hδ hε hδε hL hA hcL C, near_litter_image_inj_on hπ H hδ hε hδε hL hA hcL C⟩

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
  intro c,
  sorry,
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

lemma inflexible_support_supports' {π : struct_approx β} (hπ : π.free)
  {c : support_condition β} (H : π.foa_props hπ c) {γ : Iic α} {δ ε : Iio α}
  {B : path (β : type_index) γ} {t : tangle δ} {L A} (hδ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
  (hL : L = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t)
  (hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _))
  (hcL : relation.refl_trans_gen (constrains α β) (inr L.to_near_litter, A) c) :
  (show struct_approx (δ : Iic α), from supported_action
    (inflexible_support_map (π.foa_hypothesis hπ) ⟨γ, δ, ε, hδ, hε, hδε, B, t, hL, hA⟩)
    (λ (C : extended_index (δ : Iic α)), π ((B.cons $ coe_lt hδ).comp C))).supports
  (inflexible_support ⟨γ, δ, ε, hδ, hε, hδε, B, t, hL, hA⟩) :=
begin
  constructor,
  { intros a C ha,
    rw inflexible_support at ha,
    simp only [supported_action, supported_action_index],
    rw [supported_action_atom_map_eq hπ H _ _ _ _ _ hcL, local_perm.complete_domain_eq],
    exact or.inl (or.inl (or.inl (or.inl ha))), },
  { intros N C hN,
    rw inflexible_support at hN,
    obtain ⟨hN₁, hN₂⟩ := hN,
    obtain (_ | ⟨L, B, h⟩) := hN₂,
    simp only [supported_action, supported_action_index, mem_set_of_eq, mem_singleton_iff,
      exists_prop, exists_eq_left] at hN₁ hN₂ h ⊢,
    rw near_litter_approx.flexible_completion_litter_perm_domain',
    exact or.inr (flexible_of_comp_flexible h), },
  { intros N C hN,
    rw inflexible_support at hN,
    obtain ⟨hN₁, hN₂⟩ := hN,
    obtain (_ | ⟨L, B, h⟩) := hN₂,
    refl, },
end

lemma support_map_union_supports {π : struct_approx β} (hπ : π.free)
  {c : support_condition β} (H : π.foa_props hπ c) {γ : Iic α} {δ ε : Iio α}
  {B : path (β : type_index) γ} {t₁ t₂ : tangle δ} {L₁ L₂ A} (hδ) (hε : (ε : Λ) < γ) (hδε)
  (hL₁ : L₁ = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t₁)
  (hL₂ : L₂ = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t₂)
  (hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _))
  (hcL₁ : relation.refl_trans_gen (constrains α β) (inr L₁.to_near_litter, A) c) : supports
  (λ (D : extended_index (δ : Iic α)),
     supported_action (support_map_union hπ hδ hε hδε hL₁ hL₂ hA)
       (λ (C : extended_index δ), π ((B.cons $ coe_lt hδ).comp C)) D)
  (inflexible_support ⟨γ, δ, ε, hδ, hε, hδε, B, t₁, hL₁, hA⟩) :=
begin
  have h := inflexible_support_supports' hπ H hδ hε hδε hL₁ hA hcL₁,
  -- Should be easy.
  sorry,
end

-- This lemma is false. Note the π_{L,M} fix.
lemma inflexible_support_supports'' {π : struct_approx β} (hπ : π.free) {γ : Iic α} {δ ε : Iio α}
  {B : path (β : type_index) γ} {t : tangle δ} {L A} (hδ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
  (hL : L = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t)
  (hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _)) :
mul_action.supports (allowable δ) (inflexible_support ⟨γ, δ, ε, hδ, hε, hδε, B, t, hL, hA⟩) t :=
sorry

lemma litter_set_inter_eq_of_banned {π : struct_approx β} (hπ : π.free)
  {c : support_condition β} (H : π.foa_props hπ c)
  {γ : Iic α} {δ ε : Iio α} {B : path (β : type_index) γ} {t₁ t₂ : tangle δ} {L₁ L₂ A}
  (hδ) (hε : (ε : Λ) < γ) (hδε)
  (hL₁ : L₁ = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t₁)
  (hL₂ : L₂ = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t₂)
  (hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _))
  (C : extended_index δ) :
  ∀ L, banned_litter
    (inflexible_support_map (π.foa_hypothesis hπ) ⟨γ, δ, ε, hδ, hε, hδε, B, t₁, hL₁, hA⟩) C L →
    litter_set L ∩ (supported_action
      (support_map_union hπ hδ hε hδε hL₁ hL₂ hA)
      (λ (C : extended_index (δ : Iic α)), π ((B.cons $ coe_lt hδ).comp C)) C).atom_perm.domain =
    litter_set L ∩ (supported_action
      (inflexible_support_map (π.foa_hypothesis hπ) ⟨γ, δ, ε, hδ, hε, hδε, B, t₁, hL₁, hA⟩)
      (λ (C : extended_index δ), π ((B.cons $ coe_lt hδ).comp C)) C).atom_perm.domain :=
sorry

lemma inflexible_support_map_smul_eq_smul {π : struct_approx β} (hπ : π.free)
  {d : support_condition β} (H : π.foa_props hπ d)
  {γ : Iic α} {δ ε : Iio α} {B : path (β : type_index) γ} {t₁ t₂ : tangle δ} {L₁ L₂ A}
  (hδ) (hε : (ε : Λ) < γ) (hδε)
  (hL₁ : L₁ = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t₁)
  (hL₂ : L₂ = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t₂)
  (hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _))
  (hdL₁ : relation.refl_trans_gen (constrains α β) (inr L₁.to_near_litter, A) d)
  (hdL₂ : relation.refl_trans_gen (constrains α β) (inr L₂.to_near_litter, A) d)
  (c : support_condition (δ : Iic α))
  (hc : c ∈ inflexible_support_map (π.foa_hypothesis hπ) ⟨γ, δ, ε, hδ, hε, hδε, B, t₁, hL₁, hA⟩) :
  (show struct_approx (δ : Iic α), from supported_action
    (support_map_union hπ hδ hε hδε hL₁ hL₂ hA)
    (λ (C : extended_index (δ : Iic α)), π ((B.cons $ coe_lt hδ).comp C))) • c =
  (show struct_approx (δ : Iic α), from supported_action
    (inflexible_support_map (π.foa_hypothesis hπ) ⟨γ, δ, ε, hδ, hε, hδε, B, t₁, hL₁, hA⟩)
    (λ (C : extended_index δ), π ((B.cons $ coe_lt hδ).comp C))) • c :=
begin
  rw [smul_support_condition_eq _ c, smul_support_condition_eq _ c],
  refine prod.ext _ rfl,
  obtain ⟨a | N, C⟩ := c,
  { dsimp only,
    refine congr_arg inl _,
    rw [supported_action_smul_atom_eq, supported_action_smul_atom_eq],
    refl,
    { exact hc, },
    { exact inflexible_support_map_injective hπ H hδ hε hδε hL₁ hA hdL₁ C, },
    { exact or.inl hc, },
    { exact support_map_union_injective hπ H hδ hε hδε hL₁ hL₂ hA hdL₁ hdL₂ C, }, },
  have := hc.2,
  simp only [reduced_iff, mem_set_of_eq, prod.mk.inj_iff, false_and, exists_false,
    exists_eq_right_right', false_or] at this,
  obtain ⟨L, h, rfl⟩ := this,
  dsimp only,
  refine congr_arg inr (set_like.ext' _),
  simp only [near_litter_approx.smul_near_litter_coe, litter.to_near_litter_fst,
    near_litter_approx.coe_largest_sublitter, litter.coe_to_near_litter,
    sdiff_sdiff_right_self, inf_eq_inter, supported_action_smul_litter_eq],
  refine congr_arg2 _ _ _,
  { rw [flexible_iff_not_inflexible_bot_coe, ← not_nonempty_iff_imp_false,
      ← not_nonempty_iff_imp_false] at h,
    rw [← diff_self_inter, litter_set_inter_eq_of_banned hπ H hδ hε hδε, diff_self_inter],
    convert banned_litter.map_litter _ hc using 1,
    simp only [inflexible_support_map, foa_hypothesis_near_litter_image,
      complete_near_litter_map_eq, near_litter_completion, litter_completion],
    rw [dif_neg, dif_neg],
    refl,
    exact h.1,
    exact h.2, },
  { rw litter_set_inter_eq_of_banned hπ H hδ hε hδε _ _ _ _ _ (banned_litter.support_litter _ hc),
    refine set.ext (λ a, _),
    simp only [mem_smul_set, mem_inter_iff, mem_litter_set],
    split,
    { rintro ⟨b, ⟨hb₁, hb₂⟩, hb₃⟩,
      refine ⟨b, ⟨hb₁, _⟩, _⟩,
      sorry,
      sorry, },
    sorry, },
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
    rw [complete_litter_map_eq_of_inflexible_coe hπ ⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₁, hL₁, hA₁⟩,
      complete_litter_map_eq_of_inflexible_coe hπ ⟨γ₁, δ₂, ε₁, hδ₂, hε₁, hδε₂, B₁, t₂, hL₂, hA₁⟩]
      at h,
    have := congr_arg litter.β h,
    cases subtype.coe_injective (coe_injective this),
    rw [hL₁, hL₂],
    refine congr_arg _ _,
    obtain ⟨ρ, hρ⟩ := freedom_of_action_of_lt (δ₁ : Iic α)
      (hδ₁.trans_le (show _, from with_bot.coe_le_coe.mp (le_of_path B₁)))
      (supported_action (support_map_union hπ hδ₁ hε₁ hδε₁ hL₁ hL₂ hA₁)
        (λ B, π ((B₁.cons $ coe_lt hδ₁).comp B)))
      (support_map_union_free hπ hδ₁ hε₁ hδε₁ hL₁ hL₂ hA₁),
    have left := smul_eq_smul_of_exactly_approximates hρ
      (supported_perm_spec π hπ ⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₁, hL₁, hA₁⟩
        (π.foa_hypothesis hπ))
      (inflexible_support ⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₁, hL₁, hA₁⟩) t₁
      (support_map_union_supports hπ H hδ₁ hε₁ hδε₁ hL₁ hL₂ hA₁ hcL₁)
      (inflexible_support_supports' hπ H hδ₁ hε₁ hδε₁ hL₁ hA₁ hcL₁)
      (inflexible_support_supports'' hπ hδ₁ hε₁ hδε₁ hL₁ hA₁)
      (inflexible_support_map_smul_eq_smul hπ H hδ₁ hε₁ hδε₁ hL₁ hL₂ hA₁ hcL₁ hcL₂),
    have right := smul_eq_smul_of_exactly_approximates hρ
      (supported_perm_spec π hπ ⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₂, hL₂, hA₁⟩
        (π.foa_hypothesis hπ))
      (inflexible_support ⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₂, hL₂, hA₁⟩) t₂
      (by rw support_map_union_symm;
        exact support_map_union_supports hπ H hδ₁ hε₁ hδε₁ hL₂ hL₁ hA₁ hcL₂)
      (inflexible_support_supports' hπ H hδ₁ hε₁ hδε₁ hL₂ hA₁ hcL₂)
      (inflexible_support_supports'' hπ hδ₁ hε₁ hδε₁ hL₂ hA₁) _,
    have := f_map_injective (coe_ne_coe.mpr $ coe_ne' hδε₁) h,
    rw [← left, ← right, smul_left_cancel_iff] at this,
    exact this,
    intros c hc,
    have := inflexible_support_map_smul_eq_smul hπ H hδ₁ hε₁ hδε₁ hL₂ hL₁ hA₁ hcL₂ hcL₁ c hc,
    rw support_map_union_symm at this,
    exact this, },
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

end struct_approx

end con_nf
