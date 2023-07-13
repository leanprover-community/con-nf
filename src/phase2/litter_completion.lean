import phase2.flexible_completion
import phase2.reduction
import phase2.refine

open quiver set sum with_bot
open_locale classical

universe u

namespace con_nf

namespace struct_approx
variables [params.{u}] {α : Λ} [position_data.{}] [phase_2_assumptions α] {β : Iic α}
  {γ : Iic α} {δ ε : Iio α} (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
  {A : path (β : type_index) γ} {t : tangle δ}
  (H : hypothesis ⟨inr (f_map (coe_ne_coe.mpr $ coe_ne' hδε) t).to_near_litter,
    (A.cons (coe_lt hε)).cons (bot_lt_coe _)⟩)

/-- The inductive hypothesis used for proving freedom of action:
Every free approximation exactly approximates some allowable permutation. -/
def foa_ih (β : Iic α) : Prop :=
∀ (π₀ : struct_approx β), π₀.free → ∃ (π : allowable β), π₀.exactly_approximates π.to_struct_perm

/-- A proof-relevant statement that `L` is `A`-inflexible (excluding `ε = ⊥`). -/
structure inflexible_coe (L : litter) (A : extended_index β) :=
(γ : Iic α) (δ ε : Iio α) (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
(B : quiver.path (β : type_index) γ) (t : tangle δ)
(hL : L = f_map (coe_ne_coe.mpr $ coe_ne' hδε) t)
(hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _))

instance (L : litter) (A : extended_index β) : subsingleton (inflexible_coe L A) :=
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
structure inflexible_bot (L : litter) (A : extended_index β) :=
(γ : Iic α) (ε : Iio α) (hε : (ε : Λ) < γ)
(B : quiver.path (β : type_index) γ) (a : atom)
(hL : L = f_map (show (⊥ : type_index) ≠ (ε : Λ), from bot_ne_coe) a)
(hA : A = (B.cons (coe_lt hε)).cons (bot_lt_coe _))

instance (L : litter) (A : extended_index β) : subsingleton (inflexible_bot L A) :=
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

lemma inflexible_bot_inflexible_coe {L : litter} {A : extended_index β} :
  inflexible_bot L A → inflexible_coe L A → false :=
begin
  rintros ⟨γ₁, ε₁, hε₁, B₁, a₁, rfl, rfl⟩ ⟨γ₂, δ₂, ε₂, hδ₂, hε₂, hδε₂, B₂, t₂, hL₂, hA₂⟩,
  have h₁ := f_map_β (show (⊥ : type_index) ≠ (ε₁ : Λ), from bot_ne_coe) a₁,
  have h₂ := f_map_β (coe_ne_coe.mpr $ coe_ne' hδε₂) t₂,
  rw [hL₂, h₂] at h₁,
  cases h₁,
end

lemma inflexible_coe.δ_lt_β {L : litter} {A : extended_index β} (h : inflexible_coe L A) :
  (h.δ : Λ) < β :=
h.hδ.trans_le (show _, from coe_le_coe.mp (le_of_path h.B))

lemma inflexible_bot.constrains {L : litter} {A : extended_index β} (h : inflexible_bot L A) :
  relation.trans_gen (constrains α β)
    (inl h.a, (h.B.cons (bot_lt_coe _))) (inr L.to_near_litter, A) :=
begin
  have := constrains.f_map_bot h.hε h.B h.a,
  rw [← h.hL, ← h.hA] at this,
  exact relation.trans_gen.single this,
end

class freedom_of_action_hypothesis (β : Iic α) :=
(freedom_of_action_of_lt : ∀ γ < β, foa_ih γ)

export freedom_of_action_hypothesis (freedom_of_action_of_lt)

variable [freedom_of_action_hypothesis β]

/-- For the support map of `t`, we use everything that constrains `t`. -/
def inflexible_support {L : litter} {A : extended_index β} (h : inflexible_coe L A) :
  set (support_condition h.δ) :=
(λ c, (c.1, (h.B.cons (coe_lt h.hδ)).comp c.2)) ⁻¹'
{c | relation.trans_gen (constrains α β) c
  (inr (f_map (coe_ne_coe.mpr $ coe_ne' h.hδε) h.t).to_near_litter,
    (h.B.cons (coe_lt h.hε)).cons (bot_lt_coe _))}

lemma inflexible_support_small {L : litter} {A : extended_index β} (h : inflexible_coe L A) :
  small (inflexible_support h) :=
begin
  refine lt_of_le_of_lt (cardinal.mk_preimage_of_injective _ _ _) _,
  { intros c d h,
    simp only [prod.mk.inj_iff, path.comp_inj_right] at h,
    exact prod.ext h.1 h.2, },
  { refine small.mono _ (reduction_small' α (small_singleton
    (inr (f_map (coe_ne_coe.mpr $ coe_ne' h.hδε) h.t).to_near_litter,
      (h.B.cons (coe_lt h.hε)).cons (bot_lt_coe _)))),
    intros c hc,
    exact ⟨_, rfl, hc.to_refl⟩, },
end

lemma inflexible_support_supports_f_map {π : allowable β} {γ : Iic α} {δ ε : Iio α}
  (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
  {B : path (β : type_index) γ} {t : tangle δ}
  (hπ : ∀ ⦃a : support_condition ↑β⦄,
    a ≺[α] (inr (f_map (coe_ne_coe.mpr $ coe_ne' hδε) t).to_near_litter,
      (B.cons (coe_lt hε)).cons (bot_lt_coe _)) → π • a = a)
  (hc : (f_map (coe_ne_coe.mpr $ coe_ne' hδε) t).to_near_litter.is_litter →
    inflexible α (f_map (coe_ne_coe.mpr $ coe_ne' hδε) t)
      ((B.cons (coe_lt hε)).cons (bot_lt_coe _))) :
  (allowable.derivative (show path ((β : Iic_index α) : type_index) (ε : Iic_index α),
      from B.cons (coe_lt hε)) π : allowable (ε : Iic_index α)) •
    f_map (coe_ne_coe.mpr $ coe_ne' hδε) t =
    f_map (coe_ne_coe.mpr $ coe_ne' hδε) t :=
begin
  have h₁ := allowable.derivative_cons (show path ((β : Iic_index α) : type_index)
    (γ : Iic_index α), from B) (coe_lt hε),
  have h₂ := @smul_f_map _ _ _ _ (γ : Iic_index α) (δ : Iio_index α) ε
    (coe_lt hδ) (coe_lt hε) (Iio.coe_injective.ne hδε)
    (allowable.derivative (show path ((β : Iic_index α) : type_index)
      (γ : Iic_index α), from B) π) t,
  rw h₁,
  refine h₂.trans (congr_arg _ _),
  refine (designated_support t).supports _ (λ c hc, _),
  have := congr_arg prod.fst (hπ (constrains.f_map hδ hε hδε B t c hc)),
  obtain ⟨c, C⟩ := c,
  refine prod.ext (eq.trans _ this) rfl,
  rw ← allowable.to_struct_perm_smul at this ⊢,
  rw [← phase_2_assumptions.allowable_derivative_eq, ← allowable.derivative_to_struct_perm],
  change _ • _ = _ • _,
  simp only [struct_perm.derivative_derivative, path.comp_cons, path.comp_nil],
end

-- TODO: Does `litter_map_injective` follow from `atom_mem`?
structure hypothesis_injective_inflexible {L : litter} {A : extended_index β}
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (h : inflexible_coe L A) : Prop :=
(atom_map_injective : ∀ a b B
  (ha : (inl a, B) ∈ inflexible_support h) (hb : (inl b, B) ∈ inflexible_support h),
  H.atom_image a ((h.B.cons (coe_lt h.hδ)).comp B)
    (by rwa [inflexible_support, ← h.hL, ← h.hA] at ha) =
  H.atom_image b ((h.B.cons (coe_lt h.hδ)).comp B)
    (by rwa [inflexible_support, ← h.hL, ← h.hA] at hb) → a = b)
(litter_map_injective : ∀ (L₁ L₂ : litter) B
  (hL₁ : (inr L₁.to_near_litter, B) ∈ inflexible_support h)
  (hL₂ : (inr L₂.to_near_litter, B) ∈ inflexible_support h),
  (H.near_litter_image L₁.to_near_litter ((h.B.cons (coe_lt h.hδ)).comp B)
    (by rwa [inflexible_support, ← h.hL, ← h.hA] at hL₁) ∩
  H.near_litter_image L₂.to_near_litter ((h.B.cons (coe_lt h.hδ)).comp B)
    (by rwa [inflexible_support, ← h.hL, ← h.hA] at hL₂) : set atom).nonempty → L₁ = L₂)
(atom_mem : ∀ a (L : litter) B
  (ha : (inl a, B) ∈ inflexible_support h) (hL : (inr L.to_near_litter, B) ∈ inflexible_support h),
  a ∈ litter_set L ↔
    H.atom_image a ((h.B.cons (coe_lt h.hδ)).comp B)
      (by rwa [inflexible_support, ← h.hL, ← h.hA] at ha) ∈
    H.near_litter_image L.to_near_litter ((h.B.cons (coe_lt h.hδ)).comp B)
      (by rwa [inflexible_support, ← h.hL, ← h.hA] at hL))
(map_flexible : ∀ (L : litter) B (hL₁ : (inr L.to_near_litter, B) ∈ inflexible_support h)
  (hL₂ : flexible α L B),
  flexible α (H.near_litter_image L.to_near_litter ((h.B.cons (coe_lt h.hδ)).comp B)
    (by rwa [inflexible_support, ← h.hL, ← h.hA] at hL₁)).1 B)

/-

def hypothesised_near_litter_action {L : litter} {A : extended_index β}
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (h : inflexible_coe L A)
  (hH : hypothesis_injective_inflexible H h) : near_litter_action h.δ :=
λ B, {
  atom_map := λ a, ⟨(inl a, B) ∈ inflexible_support h,
    λ ha, H.atom_image a ((h.B.cons (coe_lt h.hδ)).comp B)
      (by rwa [inflexible_support, ← h.hL, ← h.hA] at ha)⟩,
  litter_map := λ L, ⟨(inr L.to_near_litter, B) ∈ inflexible_support h,
    λ hL, H.near_litter_image L.to_near_litter ((h.B.cons (coe_lt h.hδ)).comp B)
      (by rwa [inflexible_support, ← h.hL, ← h.hA] at hL)⟩,
  atom_map_dom_small := begin
    simp only [pfun.dom_mk],
    refine lt_of_le_of_lt _ (inflexible_support_small h),
    refine ⟨⟨λ a, ⟨_, a.prop⟩, λ a b h, _⟩⟩,
    simp only [subtype.mk_eq_mk, prod.mk.inj_iff, subtype.coe_inj, eq_self_iff_true, and_true] at h,
    exact h,
  end,
  litter_map_dom_small := begin
    simp only [pfun.dom_mk],
    refine lt_of_le_of_lt _ (inflexible_support_small h),
    refine ⟨⟨λ L, ⟨_, L.prop⟩, λ L₁ L₂ h, _⟩⟩,
    simp only [subtype.mk_eq_mk, prod.mk.inj_iff, eq_self_iff_true, and_true,
      litter.to_near_litter_injective.eq_iff, subtype.coe_inj] at h,
    exact h,
  end,
  atom_map_injective := λ a b ha hb, hH.atom_map_injective a b B ha hb,
  litter_map_injective := λ L₁ L₂ hL₁ hL₂, hH.litter_map_injective L₁ L₂ B hL₁ hL₂,
  atom_mem := λ a ha L hL, hH.atom_mem a L B ha hL,
}

@[simp] lemma hypothesised_near_litter_action_atom_map {L : litter} {A : extended_index β}
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (h : inflexible_coe L A)
  (hH : hypothesis_injective_inflexible H h) (B : extended_index h.δ) (a : atom) :
  (hypothesised_near_litter_action H h hH B).atom_map a = {
    dom := (inl a, B) ∈ inflexible_support h,
    get := λ ha, H.atom_image a ((h.B.cons (coe_lt h.hδ)).comp B)
      (by rwa [inflexible_support, ← h.hL, ← h.hA] at ha)
  } := rfl

@[simp] lemma hypothesised_near_litter_action_litter_map {L : litter} {A : extended_index β}
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (h : inflexible_coe L A)
  (hH : hypothesis_injective_inflexible H h) (B : extended_index h.δ) (L : litter) :
  (hypothesised_near_litter_action H h hH B).litter_map L = {
    dom := (inr L.to_near_litter, B) ∈ inflexible_support h,
    get := λ hL, H.near_litter_image L.to_near_litter ((h.B.cons (coe_lt h.hδ)).comp B)
      (by rwa [inflexible_support, ← h.hL, ← h.hA] at hL)
  } := rfl

lemma hypothesised_near_litter_action_free (π : struct_approx β) (hπ : π.free) {L : litter}
  {A : extended_index β} (H : hypothesis ⟨inr L.to_near_litter, A⟩) (h : inflexible_coe L A)
  (hH : hypothesis_injective_inflexible H h) :
  @struct_approx.free _ _ _ _ (h.δ : Iic α)
  (hypothesised_near_litter_action H h hH).refine.complete :=
begin
  rintros B L' ((hL' | ⟨L', hL', rfl⟩) | hL'),
  { exact hL'.2, },
  { rw weak_near_litter_approx.rough_litter_map_or_else_of_dom _ hL'.1,
    exact hH.map_flexible L' B hL'.1 hL'.2, },
  { exact (local_perm.sandbox_subset_subset _ _ hL').2, },
end

noncomputable def allowable_of_near_litter_action (π : struct_approx β) (hπ : π.free)
  {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ) (B : path (β : type_index) γ)
  (w : near_litter_action δ)
  (hw : (show struct_approx (δ : Iic α), from w.complete).free) :
  allowable δ :=
(freedom_of_action_of_lt (δ : Iic α)
  (hδ.trans_le (show _, from coe_le_coe.mp (le_of_path B))) _ hw).some

lemma allowable_of_near_litter_action_exactly_approximates (π : struct_approx β) (hπ : π.free)
  {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ) (B : path (β : type_index) γ)
  (w : near_litter_action δ)
  (hw : (show struct_approx (δ : Iic α), from w.complete).free) :
  w.complete.exactly_approximates (allowable_of_near_litter_action π hπ hδ B w hw).to_struct_perm :=
(freedom_of_action_of_lt (δ : Iic α)
  (hδ.trans_le (show _, from coe_le_coe.mp (le_of_path B))) _ hw).some_spec

noncomputable def hypothesised_allowable (π : struct_approx β) (hπ : π.free)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (hH : hypothesis_injective_inflexible H h) :
  allowable h.δ :=
allowable_of_near_litter_action π hπ h.hδ h.B _ (hypothesised_near_litter_action_free π hπ H h hH)

lemma hypothesised_allowable_exactly_approximates (π : struct_approx β) (hπ : π.free)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (hH : hypothesis_injective_inflexible H h) :
  (hypothesised_near_litter_action H h hH).refine.complete.exactly_approximates
    (hypothesised_allowable π hπ h H hH).to_struct_perm :=
allowable_of_near_litter_action_exactly_approximates π hπ h.hδ h.B _
  (hypothesised_near_litter_action_free π hπ H h hH)

-- TODO: Rename next few lemmas.
-- TODO: Trim assumptions from lots of these little lemmas, then package into `variables`.
lemma mem_inflexible_support (π : struct_approx β) (hπ : π.free)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (B : extended_index h.δ) (a : atom)
  (d : support_condition h.δ) (hd₁ : d ∈ designated_support h.t)
  (hd₂ : relation.refl_trans_gen (constrains α h.δ) (inl a, B) d) :
    (inl a, B) ∈ inflexible_support h :=
relation.trans_gen.tail'
  (refl_trans_gen_constrains_comp hd₂ _)
  (constrains.f_map h.hδ h.hε h.hδε h.B h.t d hd₁)

noncomputable def litter_completion (π : struct_approx β) (hπ : π.free)
  (L : litter) (A : extended_index β) (H : hypothesis ⟨inr L.to_near_litter, A⟩) : litter :=
if h : nonempty (inflexible_coe L A) then
  if hH : hypothesis_injective_inflexible H h.some then
    f_map (coe_ne_coe.mpr $ coe_ne' h.some.hδε)
      (hypothesised_allowable π hπ h.some H hH • h.some.t)
  else
    near_litter_approx.flexible_completion α (π A) A • L
else if h : nonempty (inflexible_bot L A) then
  f_map (show (⊥ : type_index) ≠ (h.some.ε : Λ), from bot_ne_coe)
    (H.atom_image h.some.a (h.some.B.cons (bot_lt_coe _)) h.some.constrains)
else
  near_litter_approx.flexible_completion α (π A) A • L

lemma litter_completion_of_flexible (π : struct_approx β) (hπ : π.free)
  (L : litter) (A : extended_index β) (H : hypothesis ⟨inr L.to_near_litter, A⟩)
  (hflex : flexible α L A) :
  litter_completion π hπ L A H = near_litter_approx.flexible_completion α (π A) A • L :=
begin
  rw [litter_completion, dif_neg, dif_neg],
  { rintro ⟨⟨γ, ε, hε, C, a, rfl, rfl⟩⟩,
    exact hflex (inflexible.mk_bot _ _ _), },
  { rintro ⟨⟨γ, δ, ε, hδ, hε, hδε, C, t, rfl, rfl⟩⟩,
    exact hflex (inflexible.mk_coe hδ _ _ _ _), },
end

lemma litter_completion_of_inflexible_coe (π : struct_approx β) (hπ : π.free)
  (L : litter) (A : extended_index β) (H : hypothesis ⟨inr L.to_near_litter, A⟩)
  (h : inflexible_coe L A) (hH : hypothesis_injective_inflexible H h) :
  litter_completion π hπ L A H =
  f_map (coe_ne_coe.mpr $ coe_ne' h.hδε) (hypothesised_allowable π hπ h H hH • h.t) :=
begin
  rw [litter_completion, dif_pos, dif_pos],
  { repeat {
      congr' 1;
      try { rw subsingleton.elim h, },
    }, },
  { rw subsingleton.elim h at hH,
    exact hH, },
  { exact ⟨h⟩, },
end

lemma litter_completion_of_inflexible_bot (π : struct_approx β) (hπ : π.free)
  (L : litter) (A : extended_index β) (H : hypothesis ⟨inr L.to_near_litter, A⟩)
  (h : inflexible_bot L A) :
  litter_completion π hπ L A H =
  f_map (show (⊥ : type_index) ≠ (h.ε : Λ), from bot_ne_coe)
    (H.atom_image h.a (h.B.cons (bot_lt_coe _)) h.constrains) :=
begin
  rw [litter_completion, dif_neg, dif_pos, subsingleton.elim h],
  { exact ⟨h⟩, },
  { rintro ⟨h'⟩,
    exact inflexible_bot_inflexible_coe h h', },
end

-/

end struct_approx

end con_nf
