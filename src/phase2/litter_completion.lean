import phase2.flexible_completion
import phase2.reduction
import phase2.refine

open quiver set sum with_bot
open_locale classical

universe u

namespace con_nf

namespace struct_approx
variables [params.{u}] {α : Λ} [position_data.{}] [phase_2_assumptions α]

/-- The inductive hypothesis used for proving freedom of action:
Every free approximation exactly approximates some allowable permutation. -/
def foa_ih (β : Iic α) : Prop :=
∀ (π₀ : struct_approx β), π₀.free → ∃ (π : allowable β), π₀.exactly_approximates π.to_struct_perm

/-- A proof-relevant statement that `L` is `A`-inflexible (excluding `ε = ⊥`). -/
structure inflexible_coe {β : Iic α} (L : litter) (A : extended_index β) :=
(γ : Iic α) (δ ε : Iio α) (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
(B : quiver.path (β : type_index) γ) (t : tangle δ)
(hL : L = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t)
(hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _))

instance {β : Iic α} (L : litter) (A : extended_index β) : subsingleton (inflexible_coe L A) :=
begin
  constructor,
  rintros ⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₁, rfl, rfl⟩
    ⟨γ₂, δ₂, ε₂, hδ₂, hε₂, hδε₂, B₂, t₂, hL₂, hA₂⟩,
  cases subtype.coe_injective (coe_eq_coe.mp (path.obj_eq_of_cons_eq_cons hA₂)),
  cases subtype.coe_injective (coe_eq_coe.mp (path.obj_eq_of_cons_eq_cons
    (path.heq_of_cons_eq_cons hA₂).eq)),
  cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons hA₂).eq).eq,
  have h₁ := f_map_β (coe_ne_coe.mpr $ coe_ne' hδε₁) t₁,
  have h₂ := f_map_β (coe_ne_coe.mpr $ coe_ne' hδε₂) t₂,
  rw [hL₂, h₂] at h₁,
  cases subtype.coe_injective (coe_eq_coe.mp h₁),
  cases f_map_injective _ hL₂,
  refl,
end

/-- A proof-relevant statement that `L` is `A`-inflexible, where `δ = ⊥`. -/
structure inflexible_bot {β : Iic α} (L : litter) (A : extended_index β) :=
(γ : Iic α) (ε : Iio α) (hε : (ε : Λ) < γ)
(B : quiver.path (β : type_index) γ) (a : atom)
(hL : L = f_map (show (⊥ : type_index) ≠ (ε : Λ), from bot_ne_coe) a)
(hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _))

instance {β : Iic α} (L : litter) (A : extended_index β) : subsingleton (inflexible_bot L A) :=
begin
  constructor,
  rintros ⟨γ₁, ε₁, hε₁, B₁, a₁, rfl, rfl⟩ ⟨γ₂, ε₂, hε₂, B₂, a₂, hL₂, hA₂⟩,
  cases subtype.coe_injective (coe_eq_coe.mp (path.obj_eq_of_cons_eq_cons hA₂)),
  cases subtype.coe_injective (coe_eq_coe.mp (path.obj_eq_of_cons_eq_cons
    (path.heq_of_cons_eq_cons hA₂).eq)),
  cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons hA₂).eq).eq,
  cases f_map_injective _ hL₂,
  refl,
end

lemma inflexible_bot_inflexible_coe {β : Iic α} {L : litter} {A : extended_index β} :
  inflexible_bot L A → inflexible_coe L A → false :=
begin
  rintros ⟨γ₁, ε₁, hε₁, B₁, a₁, rfl, rfl⟩ ⟨γ₂, δ₂, ε₂, hδ₂, hε₂, hδε₂, B₂, t₂, hL₂, hA₂⟩,
  have h₁ := f_map_β (show (⊥ : type_index) ≠ (ε₁ : Λ), from bot_ne_coe) a₁,
  have h₂ := f_map_β (coe_ne_coe.mpr $ coe_ne' hδε₂) t₂,
  rw [hL₂, h₂] at h₁,
  cases h₁,
end

lemma inflexible_coe.δ_lt_β {β : Iic α} {L : litter} {A : extended_index β}
  (h : inflexible_coe L A) : (h.δ : Λ) < β :=
h.hδ.trans_le (show _, from coe_le_coe.mp (le_of_path h.B))

lemma inflexible_bot.constrains {β : Iic α} {L : litter} {A : extended_index β}
  (h : inflexible_bot L A) : (inl h.a, (h.B.cons (bot_lt_coe _))) <[α] (inr L.to_near_litter, A) :=
begin
  have := constrains.f_map_bot h.hε h.B h.a,
  rw [← h.hL, ← h.hA] at this,
  exact relation.trans_gen.single this,
end

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

lemma inflexible_iff_inflexible_bot_or_inflexible_coe
  {β : Iic α} {L : litter} {A : extended_index β} :
  inflexible α L A ↔ nonempty (inflexible_bot L A) ∨ nonempty (inflexible_coe L A) :=
begin
  split,
  exact inflexible_bot_or_inflexible_coe_of_inflexible,
  rintro (⟨⟨h⟩⟩ | ⟨⟨h⟩⟩),
  exact inflexible_of_inflexible_bot h,
  exact inflexible_of_inflexible_coe h,
end

lemma flexible_iff_not_inflexible_bot_coe {β : Iic α} {L : litter} {A : extended_index β} :
  flexible α L A ↔ is_empty (inflexible_bot L A) ∧ is_empty (inflexible_coe L A) :=
begin
  split,
  { intro h,
    exact ⟨
      ⟨λ h', h (inflexible_of_inflexible_bot h')⟩,
      ⟨λ h', h (inflexible_of_inflexible_coe h')⟩
    ⟩, },
  { intros h₁ h₂,
    cases inflexible_bot_or_inflexible_coe_of_inflexible h₂,
    exact h₁.1.false h.some,
    exact h₁.2.false h.some, },
end

lemma flexible_cases' {β : Iic α} (L : litter) (A : extended_index β) :
  flexible α L A ∨ nonempty (inflexible_bot L A) ∨ nonempty (inflexible_coe L A) :=
begin
  rw [← inflexible_iff_inflexible_bot_or_inflexible_coe, or_comm],
  exact flexible_cases α L A,
end

class freedom_of_action_hypothesis (β : Iic α) :=
(freedom_of_action_of_lt : ∀ γ < β, foa_ih γ)

export freedom_of_action_hypothesis (freedom_of_action_of_lt)

/-- The structural action associated to a given inductive hypothesis. -/
def ih_action {β : Iic α} {c : support_condition β} (H : hypothesis c) : struct_action β :=
λ B, {
  atom_map := λ a, ⟨_, λ h, H.atom_image a B h⟩,
  litter_map := λ L, ⟨_, λ h, H.near_litter_image L.to_near_litter B h⟩,
  atom_map_dom_small := begin
    simp only [pfun.dom_mk],
    have := reduction_small'' α (small_singleton c),
    simp only [mem_singleton_iff, exists_prop, exists_eq_left] at this,
    refine small.image_subset (λ a, (inl a, B)) _ this _,
    { intros a b h,
      simpa only [prod.mk.inj_iff, eq_self_iff_true, and_true] using h, },
    { rintros _ ⟨a, h, rfl⟩,
      exact h, },
  end,
  litter_map_dom_small := begin
    simp only [pfun.dom_mk],
    have := reduction_small'' α (small_singleton c),
    simp only [mem_singleton_iff, exists_prop, exists_eq_left] at this,
    refine small.image_subset (λ L, (inr L.to_near_litter, B)) _ this _,
    { intros L₁ L₂ h,
      simpa only [prod.mk.inj_iff, eq_self_iff_true, and_true,
        litter.to_near_litter_injective.eq_iff] using h, },
    { rintros _ ⟨a, h, rfl⟩,
      exact h, },
  end,
}

def _root_.con_nf.struct_action.comp {β γ : type_index} (φ : struct_action β) (A : path β γ) :
  struct_action γ :=
λ B, {
  atom_map := λ a, (φ (A.comp B)).atom_map a,
  litter_map := λ a, (φ (A.comp B)).litter_map a,
  atom_map_dom_small := begin
    refine small.image_subset id function.injective_id (φ (A.comp B)).atom_map_dom_small _,
    simp only [id.def, image_id'],
  end,
  litter_map_dom_small := begin
    refine small.image_subset id function.injective_id (φ (A.comp B)).litter_map_dom_small _,
    simp only [id.def, image_id'],
  end,
}

variables {β : Iic α} [freedom_of_action_hypothesis β]

noncomputable def _root_.con_nf.struct_action.allowable {γ : Iio α}
  (φ : struct_action γ) (h : (γ : Iic α) < β) (h₁ : φ.lawful) (h₂ : φ.map_flexible) :
  allowable γ :=
(freedom_of_action_of_lt _ h _ (struct_action.rc_free _ h₁ h₂)).some

lemma _root_.con_nf.struct_action.allowable_exactly_approximates {γ : Iio α}
  (φ : struct_action γ) (h : (γ : Iic α) < β) (h₁ : φ.lawful) (h₂ : φ.map_flexible) :
  (φ.rc h₁).exactly_approximates (φ.allowable h h₁ h₂).to_struct_perm :=
(freedom_of_action_of_lt _ h _ (struct_action.rc_free _ h₁ h₂)).some_spec

noncomputable def _root_.con_nf.struct_action.hypothesised_allowable
  (φ : struct_action β)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (h₁ : (φ.comp (h.B.cons (coe_lt h.hδ))).lawful)
  (h₂ : (φ.comp (h.B.cons (coe_lt h.hδ))).map_flexible) :
  allowable h.δ :=
(φ.comp (h.B.cons (coe_lt h.hδ))).allowable
  (h.hδ.trans_le (show _, from coe_le_coe.mp (le_of_path h.B))) h₁ h₂

noncomputable def litter_completion (π : struct_approx β)
  (L : litter) (A : extended_index β) (H : hypothesis ⟨inr L.to_near_litter, A⟩) : litter :=
if h : nonempty (inflexible_coe L A) then
  if hs : _ ∧ _ then
    f_map (coe_ne_coe.mpr $ coe_ne' h.some.hδε)
      ((ih_action H).hypothesised_allowable h.some hs.1 hs.2 • h.some.t)
  else
    near_litter_approx.flexible_completion α (π A) A • L
else if h : nonempty (inflexible_bot L A) then
  f_map (show (⊥ : type_index) ≠ (h.some.ε : Λ), from bot_ne_coe)
    (H.atom_image h.some.a (h.some.B.cons (bot_lt_coe _)) h.some.constrains)
else
  near_litter_approx.flexible_completion α (π A) A • L

lemma litter_completion_of_flexible (π : struct_approx β)
  (L : litter) (A : extended_index β) (H : hypothesis ⟨inr L.to_near_litter, A⟩)
  (hflex : flexible α L A) :
  litter_completion π L A H = near_litter_approx.flexible_completion α (π A) A • L :=
begin
  rw [litter_completion, dif_neg, dif_neg],
  { rintro ⟨⟨γ, ε, hε, C, a, rfl, rfl⟩⟩,
    exact hflex (inflexible.mk_bot _ _ _), },
  { rintro ⟨⟨γ, δ, ε, hδ, hε, hδε, C, t, rfl, rfl⟩⟩,
    exact hflex (inflexible.mk_coe hδ _ _ _ _), },
end

lemma litter_completion_of_inflexible_coe (π : struct_approx β)
  (L : litter) (A : extended_index β) (H : hypothesis ⟨inr L.to_near_litter, A⟩)
  (h : inflexible_coe L A)
  (h₁ : ((ih_action H).comp (h.B.cons (coe_lt h.hδ))).lawful)
  (h₂ : ((ih_action H).comp (h.B.cons (coe_lt h.hδ))).map_flexible) :
  litter_completion π L A H =
  f_map (coe_ne_coe.mpr $ coe_ne' h.hδε)
    ((ih_action H).hypothesised_allowable h h₁ h₂ • h.t) :=
begin
  rw [litter_completion, dif_pos, dif_pos],
  { repeat {
      congr' 1;
      try { rw subsingleton.elim h, },
    }, },
  { refine ⟨_, _⟩,
    { exact ⟨h⟩, },
    { rw subsingleton.elim h at h₁,
      exact h₁, },
    { rw subsingleton.elim h at h₂,
      exact h₂, }, },
end

lemma litter_completion_of_inflexible_bot (π : struct_approx β)
  (L : litter) (A : extended_index β) (H : hypothesis ⟨inr L.to_near_litter, A⟩)
  (h : inflexible_bot L A) :
  litter_completion π L A H =
  f_map (show (⊥ : type_index) ≠ (h.ε : Λ), from bot_ne_coe)
    (H.atom_image h.a (h.B.cons (bot_lt_coe _)) h.constrains) :=
begin
  rw [litter_completion, dif_neg, dif_pos, subsingleton.elim h],
  { exact ⟨h⟩, },
  { rintro ⟨h'⟩,
    exact inflexible_bot_inflexible_coe h h', },
end

end struct_approx

end con_nf
