import phase2.reduction
import phase2.supported_action
import phase2.weak_approx

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

def lawful_atom_map (π₀ : struct_approx β) (π : allowable β) : Prop :=
∀ (a : atom) (A : extended_index β) (h : a ∉ (π₀ A).atom_perm.domain),
  struct_perm.derivative A π.to_struct_perm • a =
  ((π₀ A).largest_sublitter a.1).order_iso
  ((π₀ A).largest_sublitter (struct_perm.derivative A π.to_struct_perm • a.1))
  ⟨a, (π₀ A).mem_largest_sublitter_of_not_mem_domain a h⟩

/-- The inductive hypothesis used for proving freedom of action:
Every free approximation exactly approximates some allowable permutation, and its action on atoms
not in the domain of the approximation is given by the order isomorphism between sublitters. -/
def foa_ih (β : Iic α) : Prop :=
∀ (π₀ : struct_approx β), π₀.free →
  ∃ (π : allowable β), π₀.exactly_approximates π.to_struct_perm ∧ π₀.lawful_atom_map π

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

structure hypothesis_injective_inflexible {L : litter} {A : extended_index β}
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (h : inflexible_coe L A) : Prop :=
(atom_map_injective : ∀ a b B
  (ha : (inl a, B) ∈ inflexible_support h) (hb : (inl b, B) ∈ inflexible_support h),
  H.atom_image a ((h.B.cons (coe_lt h.hδ)).comp B)
    (by rwa [inflexible_support, ← h.hL, ← h.hA] at ha) =
  H.atom_image b ((h.B.cons (coe_lt h.hδ)).comp B)
    (by rwa [inflexible_support, ← h.hL, ← h.hA] at hb) → a = b)
(atom_mem : ∀ a (L : litter) B
  (ha : (inl a, B) ∈ inflexible_support h) (hL : (inr L.to_near_litter, B) ∈ inflexible_support h),
  a ∈ litter_set L ↔
    H.atom_image a ((h.B.cons (coe_lt h.hδ)).comp B)
      (by rwa [inflexible_support, ← h.hL, ← h.hA] at ha) ∈
    H.near_litter_image L.to_near_litter ((h.B.cons (coe_lt h.hδ)).comp B)
      (by rwa [inflexible_support, ← h.hL, ← h.hA] at hL))

def hypothesised_weak_struct_approx {L : litter} {A : extended_index β}
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (h : inflexible_coe L A)
  (hH : hypothesis_injective_inflexible H h) : weak_struct_approx h.δ :=
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
  atom_mem := λ a ha L hL, hH.atom_mem a L B ha hL,
}

@[simp] lemma hypothesised_weak_struct_approx_atom_map {L : litter} {A : extended_index β}
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (h : inflexible_coe L A)
  (hH : hypothesis_injective_inflexible H h) (B : extended_index h.δ) (a : atom) :
  (hypothesised_weak_struct_approx H h hH B).atom_map a = ⟨(inl a, B) ∈ inflexible_support h,
    λ ha, H.atom_image a ((h.B.cons (coe_lt h.hδ)).comp B)
      (by rwa [inflexible_support, ← h.hL, ← h.hA] at ha)⟩ := rfl

@[simp] lemma hypothesised_weak_struct_approx_litter_map {L : litter} {A : extended_index β}
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (h : inflexible_coe L A)
  (hH : hypothesis_injective_inflexible H h) (B : extended_index h.δ) (L : litter) :
  (hypothesised_weak_struct_approx H h hH B).litter_map L =
  ⟨(inr L.to_near_litter, B) ∈ inflexible_support h,
    λ hL, H.near_litter_image L.to_near_litter ((h.B.cons (coe_lt h.hδ)).comp B)
      (by rwa [inflexible_support, ← h.hL, ← h.hA] at hL)⟩ := rfl

noncomputable def litter_perm_below (π : struct_approx β) {γ : Iic α} {δ : Iio α}
  (hδ : (δ : Λ) < γ) (B : path (β : type_index) γ) : extended_index δ → local_perm litter :=
λ C, (π ((B.cons (coe_lt hδ)).comp C)).flexible_completion_litter_perm α
    ((B.cons (coe_lt hδ)).comp C)

lemma hypothesised_weak_struct_approx_free (π : struct_approx β) (hπ : π.free) {L : litter}
  {A : extended_index β} (H : hypothesis ⟨inr L.to_near_litter, A⟩) (h : inflexible_coe L A)
  (hH : hypothesis_injective_inflexible H h) :
  @struct_approx.free _ _ _ _ (h.δ : Iic α)
  ((hypothesised_weak_struct_approx H h hH).complete (litter_perm_below π h.hδ h.B)) :=
begin
  intros B L' hL',
  cases hL',
  { exact flexible_of_comp_flexible (hπ _ L' hL'), },
  { exact flexible_of_comp_flexible hL'.1, },
end

noncomputable def allowable_of_weak_struct_approx (π : struct_approx β) (hπ : π.free)
  {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ) (B : path (β : type_index) γ)
  (w : weak_struct_approx δ)
  (hw : (show struct_approx (δ : Iic α), from w.complete (litter_perm_below π hδ B)).free) :
  allowable δ :=
(freedom_of_action_of_lt (δ : Iic α)
  (hδ.trans_le (show _, from coe_le_coe.mp (le_of_path B))) _ hw).some

lemma allowable_of_weak_struct_approx_exactly_approximates (π : struct_approx β) (hπ : π.free)
  {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ) (B : path (β : type_index) γ)
  (w : weak_struct_approx δ)
  (hw : (show struct_approx (δ : Iic α), from w.complete (litter_perm_below π hδ B)).free) :
  (w.complete (litter_perm_below π hδ B))
    .exactly_approximates (allowable_of_weak_struct_approx π hπ hδ B w hw).to_struct_perm :=
(freedom_of_action_of_lt (δ : Iic α)
  (hδ.trans_le (show _, from coe_le_coe.mp (le_of_path B))) _ hw).some_spec.1

-- lemma supported_perm_of_support_map_lawful_atom_map (π : struct_approx β) (hπ : π.free)
--   {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ) (B : path (β : type_index) γ) (S : support_map δ)
--   (hS : (show struct_approx (δ : Iic α), from supported_action S
--     (λ (C : extended_index δ), π ((B.cons $ coe_lt hδ).comp C))).free) :
--   (show struct_approx (δ : Iic α), from supported_action S
--     (λ C, π ((B.cons $ coe_lt hδ).comp C))).lawful_atom_map
--   (supported_perm_of_support_map π hπ hδ B S hS) :=
-- (freedom_of_action_of_lt (δ : Iic α)
--   (hδ.trans_le (show _, from coe_le_coe.mp (le_of_path B))) _ hS).some_spec.2

noncomputable def hypothesised_allowable (π : struct_approx β) (hπ : π.free)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (hH : hypothesis_injective_inflexible H h) :
  allowable h.δ :=
allowable_of_weak_struct_approx π hπ h.hδ h.B _ (hypothesised_weak_struct_approx_free π hπ H h hH)

lemma hypothesised_allowable_exactly_approximates (π : struct_approx β) (hπ : π.free)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (hH : hypothesis_injective_inflexible H h) :
  ((hypothesised_weak_struct_approx H h hH).complete (litter_perm_below π h.hδ h.B))
    .exactly_approximates (hypothesised_allowable π hπ h H hH).to_struct_perm :=
allowable_of_weak_struct_approx_exactly_approximates π hπ h.hδ h.B _
  (hypothesised_weak_struct_approx_free π hπ H h hH)

-- lemma supported_perm_lawful_atom_map (π : struct_approx β) (hπ : π.free)
--   {L : litter} {A : extended_index β} (h : inflexible_coe L A)
--   (H : hypothesis ⟨inr L.to_near_litter, A⟩) :
--   (show struct_approx (h.δ : Iic α), from supported_action
--     (inflexible_support_map H h) (λ C, π ((h.B.cons $ coe_lt h.hδ).comp C))).lawful_atom_map
--   (supported_perm π hπ h H) :=
-- supported_perm_of_support_map_lawful_atom_map π hπ h.hδ h.B _ (π.litter_approx_free hπ H h)

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

/- lemma supported_perm_smul_atom_eq (π : struct_approx β) (hπ : π.free)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (S : support_map h.δ)
  (hS₁ : (show struct_approx (h.δ : Iic α), from
    supported_action S (λ (B : extended_index h.δ), π ((h.B.cons $ coe_lt h.hδ).comp B))).free)
  (hS₂ : inflexible_support_map H h ≤ S)
  (hS₃ : ∀ B, S.injective B)
  (d : support_condition h.δ) (hd₁ : d ∈ designated_support h.t)
  (B : extended_index h.δ) (a : atom)
  (hd₂ : relation.refl_trans_gen (constrains α h.δ) (inl a, B) d) :
  struct_perm.derivative B (π.supported_perm_of_support_map hπ h.hδ h.B S hS₁).to_struct_perm • a =
  struct_perm.derivative B (π.supported_perm hπ h H).to_struct_perm • a :=
begin
  have := mem_inflexible_support π hπ h B a d hd₁ hd₂,
  rw [← struct_perm.of_bot_smul, ← struct_perm.of_bot_smul,
    ← (supported_perm_exactly_approximates π hπ h H B).map_atom,
    ← (supported_perm_of_support_map_exactly_approximates π hπ h.hδ h.B S hS₁ B).map_atom a _,
    supported_action_smul_atom_eq, supported_action_smul_atom_eq],
  refine (hS₂.map_atom _).symm,
  { exact this, },
  { exact (hS₃ B).le hS₂, },
  { exact hS₃ B, },
  { rw supported_action_atom_perm_domain_eq _ (hS₃ B),
    exact or.inl (or.inl (or.inl (or.inl (hS₂.carrier_subset this)))), },
  { rw supported_action_atom_perm_domain_eq _ ((hS₃ B).le hS₂),
    exact or.inl (or.inl (or.inl (or.inl this))), },
end

lemma supported_perm_smul_litter_eq (π : struct_approx β) (hπ : π.free)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (S : support_map h.δ)
  (hS₁ : (show struct_approx (h.δ : Iic α), from
    supported_action S (λ (B : extended_index h.δ), π ((h.B.cons $ coe_lt h.hδ).comp B))).free)
  (hS₂ : inflexible_support_map H h ≤ S) (hS₃ : ∀ B, S.injective B)
  (d : support_condition h.δ) (hd₁ : d ∈ designated_support h.t)
  (B : extended_index h.δ) (L' : litter)
  (ih : ∀ (y : support_condition h.δ), y ≺[α] (inr L'.to_near_litter, B) →
    (∃ d ∈ designated_support h.t, relation.refl_trans_gen (constrains α h.δ) y d) →
    π.supported_perm_of_support_map hπ h.hδ h.B S hS₁ • y =
      π.supported_perm hπ h H • y)
  (hd₂ : relation.refl_trans_gen (constrains α h.δ) (inr L'.to_near_litter, B) d) :
  struct_perm.derivative B (π.supported_perm_of_support_map hπ h.hδ h.B S hS₁).to_struct_perm • L' =
  struct_perm.derivative B (π.supported_perm hπ h H).to_struct_perm • L' :=
begin
  by_cases hflex : inflexible α L' B,
  rw inflexible_iff at hflex,
  obtain (⟨γ, δ, ε, hδ, hε, hδε, C, t, rfl, rfl⟩ | ⟨γ, ε, hε, C, a, rfl, rfl⟩) := hflex,
  { have hc := λ c hc, ih _ (constrains.f_map hδ hε hδε C t c hc)
      ⟨d, hd₁, relation.refl_trans_gen.head (constrains.f_map hδ hε hδε C t c hc) hd₂⟩,
    have := (designated_support t).supports
      ((allowable.derivative
        (show path ((h.δ : Iic_index α) : type_index) (δ : Iic_index α), from C.cons (coe_lt hδ))
        (π.supported_perm hπ h H))⁻¹ *
      (allowable.derivative
        (show path ((h.δ : Iic_index α) : type_index) (δ : Iic_index α), from C.cons (coe_lt hδ))
        (π.supported_perm_of_support_map hπ h.hδ h.B S hS₁))) _,
    { rw [mul_smul, inv_smul_eq_iff] at this,
      rw [struct_perm.derivative_cons, struct_perm.derivative_bot_smul,
        struct_perm.derivative_cons _ (C.cons _), struct_perm.derivative_bot_smul,
        struct_perm.derivative_cons _ C, struct_perm.derivative_cons _ C],
      rw allowable.derivative_to_struct_perm
        (show path ((h.δ : Iic_index α) : type_index)
          (⟨γ, coe_le_coe.mpr γ.prop⟩ : Iic_index α), from C),
      rw allowable.derivative_to_struct_perm
        (show path ((h.δ : Iic_index α) : type_index)
          (⟨γ, coe_le_coe.mpr γ.prop⟩ : Iic_index α), from C),
      have smul_f_map := to_struct_perm_smul_f_map (δ : Iio_index α) ε
        (show (δ : type_index) < (⟨γ, coe_le_coe.mpr γ.prop⟩ : Iic_index α), from coe_lt hδ)
        (coe_lt hε) (Iio.coe_injective.ne hδε),
      exact (smul_f_map _ _).trans ((smul_f_map _ _).trans (congr_arg2 _ rfl this.symm)).symm, },
    { intros d hd,
      rw [mul_smul, inv_smul_eq_iff],
      have := hc d hd,
      rw [← allowable.to_struct_perm_smul, ← allowable.to_struct_perm_smul,
        ← allowable.derivative_to_struct_perm, ← allowable.derivative_to_struct_perm],
      refine prod.ext _ rfl,
      change _ • _ = _ • _,
      rw [struct_perm.derivative_derivative, struct_perm.derivative_derivative],
      exact congr_arg prod.fst this, }, },
  { have hc := ih _ (constrains.f_map_bot hε C a)
      ⟨d, hd₁, relation.refl_trans_gen.head (constrains.f_map_bot hε C a) hd₂⟩,
    rw [struct_perm.derivative_cons, struct_perm.derivative_bot_smul,
      struct_perm.derivative_cons _ (C.cons _), struct_perm.derivative_bot_smul,
      struct_perm.derivative_cons _ C, struct_perm.derivative_cons _ C],
    rw allowable.derivative_to_struct_perm
      (show path ((h.δ : Iic_index α) : type_index)
        (⟨γ, coe_le_coe.mpr γ.prop⟩ : Iic_index α), from C),
    rw allowable.derivative_to_struct_perm
      (show path ((h.δ : Iic_index α) : type_index)
        (⟨γ, coe_le_coe.mpr γ.prop⟩ : Iic_index α), from C),
    have smul_f_map := to_struct_perm_smul_f_map (⊥ : Iio_index α) ε
        (show ⊥ < (⟨γ, coe_le_coe.mpr γ.prop⟩ : Iic_index α), from bot_lt_coe _)
        (coe_lt hε) (show (⊥ : Iio_index α) ≠ ε, from subtype.ne_of_val_ne bot_ne_coe),
    refine (smul_f_map _ _).trans ((smul_f_map _ _).trans (congr_arg2 _ rfl _)).symm,
    simp only,
    have := supported_perm_smul_atom_eq π hπ h H S hS₁ hS₂ hS₃ d hd₁ _ a
      (relation.refl_trans_gen.head (constrains.f_map_bot hε C a) hd₂),
    -- Should be done, but instance diamonds make this goal very annoying to solve.
    sorry, },
  { rw [← struct_perm.of_bot_smul, ← struct_perm.of_bot_smul,
      ← (supported_perm_exactly_approximates π hπ h H B).map_litter,
      ← (supported_perm_of_support_map_exactly_approximates π hπ h.hδ h.B S hS₁ B).map_litter L' _,
      supported_action_smul_litter_eq, supported_action_smul_litter_eq],
    { by_cases L' ∈ (π ((h.B.cons _).comp B)).litter_perm.domain,
      exact or.inl h,
      exact or.inr ⟨hflex, h⟩, },
    { by_cases L' ∈ (π ((h.B.cons _).comp B)).litter_perm.domain,
      exact or.inl h,
      exact or.inr ⟨hflex, h⟩, }, },
end

def support_map_supported (π : struct_approx β) (hπ : π.free)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (S : support_map h.δ)
  (hS₁ : (show struct_approx (h.δ : Iic α), from
    supported_action S (λ (B : extended_index h.δ), π ((h.B.cons $ coe_lt h.hδ).comp B))).free) :=
∀ (L : litter) (B : extended_index h.δ) (d : support_condition h.δ)
  (hd₁ : d ∈ designated_support h.t)
  (hd₂ : relation.refl_trans_gen (constrains α h.δ) (inr L.to_near_litter, B) d),
  struct_perm.derivative B
    (π.supported_perm_of_support_map hπ h.hδ h.B S hS₁).to_struct_perm • L =
  struct_perm.derivative B
    (π.supported_perm hπ h H).to_struct_perm • L →
  struct_perm.derivative B
    (π.supported_perm_of_support_map hπ h.hδ h.B S hS₁).to_struct_perm • L.to_near_litter =
  struct_perm.derivative B
    (π.supported_perm hπ h H).to_struct_perm • L.to_near_litter

lemma supported_perm_smul_to_near_litter_eq (π : struct_approx β) (hπ : π.free)
  {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ) (B : path (β : type_index) γ) (S : support_map δ)
  (hS : (show struct_approx (δ : Iic α), from supported_action S
    (λ (C : extended_index δ), π ((B.cons $ coe_lt hδ).comp C))).free)
  {L : litter} {C : extended_index δ} (hL : (inr L.to_near_litter, C) ∈ S)
  (hS' : S.injective C)
  (hL' : struct_perm.derivative C
    (π.supported_perm_of_support_map hπ hδ B S hS).to_struct_perm • L =
    (S.near_litter_image L.to_near_litter C hL).fst) :
  struct_perm.derivative C
    (π.supported_perm_of_support_map hπ hδ B S hS).to_struct_perm • L.to_near_litter =
  S.near_litter_image L.to_near_litter C hL :=
begin
  refine set_like.coe_injective (set.ext (λ a, _)),
  refine mem_smul_set.trans _,
  simp only [litter.coe_to_near_litter, mem_litter_set, set_like.mem_coe,
    struct_perm.to_near_litter_perm_smul],
  split,
  { rintro ⟨b, hb, rfl⟩,
    by_cases hpreimage : without_preimage S (struct_perm.derivative C
      (π.supported_perm_of_support_map hπ hδ B S hS).to_struct_perm • b) C,
    { by_contradiction,
      have : (struct_perm.derivative C
          (π.supported_perm_of_support_map hπ hδ B S hS).to_struct_perm •
          ((preimage_litter_equiv S C).symm ⟨_, hpreimage⟩ : atom)) =
        (struct_perm.derivative C
          (π.supported_perm_of_support_map hπ hδ B S hS).to_struct_perm • b),
      { have := (supported_perm_of_support_map_exactly_approximates π hπ hδ B S hS C).map_atom _ _,
        rw struct_perm.of_bot_smul at this,
        rw ← this,
        rw supported_action_smul_preimage_litter_equiv,
        refl,
        { exact hS', },
        { rw supported_action_atom_perm_domain_eq,
          exact or.inl (or.inl (or.inl (or.inr
            ((preimage_litter_equiv S C).symm ⟨_, hpreimage⟩).prop))),
          exact hS', }, },
      rw smul_left_cancel_iff at this,
      rw ← this at hb,
      have := preimage_litter_subset_subset C ((preimage_litter_equiv S C).symm ⟨_, hpreimage⟩).prop,
      rw [mem_litter_set, hb] at this,
      have h₁ := preimage_litter_not_banned S C,
      have h₂ := banned_litter.support_litter L hL,
      rw this at h₂,
      contradiction, },
    rw without_preimage_iff at hpreimage,
    simp only [mem_litter_set, ne.def, not_and, not_forall, not_not, bex_imp_distrib] at hpreimage,
    by_cases hb' : b ∈ supported_action_atom_map_core_domain S C,
    { have := (supported_perm_of_support_map_exactly_approximates π hπ hδ B S hS C).map_atom b _,
      rw struct_perm.of_bot_smul at this,
      rw ← this,
      clear this,
      obtain ((hb' | hb') | hb') := hb',
      { rw supported_action_smul_atom_eq _ _ _ _ hb' hS',
        -- Need an assumption on `S`.
        sorry },
      { cases eq_of_mem_litter_set_of_mem_litter_set hb (preimage_litter_subset_subset C hb'),
        cases preimage_litter_not_banned S C (banned_litter.support_litter _ hL), },
      { simp only [mem_Union] at hb',
        obtain ⟨L', hL', hbL'⟩ := hb',
        cases eq_of_mem_litter_set_of_mem_litter_set hb
          (mapped_outside_subset_subset L' C hL' hbL'),
        rw supported_action_smul_of_mem_mapped_outside_subset _ _ _ hbL' hS',
        exact (mapped_outside_equiv S L C hL' ⟨b, hbL'⟩).prop.mem_map, },
      { rw supported_action_atom_perm_domain_eq,
        exact or.inl (or.inl hb'),
        exact hS', }, },
    have himage : ∀ (c : atom) (hc : (inl c, C) ∈ S.carrier),
      struct_perm.derivative C (π.supported_perm_of_support_map hπ hδ B S hS).to_struct_perm • b ≠
      S.atom_image c C hc,
    { intros c hc hbc,
      have := (supported_perm_of_support_map_exactly_approximates π hπ hδ B S hS C).map_atom c _,
      rw [struct_perm.of_bot_smul, supported_action_smul_atom_eq, ← hbc,
        smul_left_cancel_iff] at this,
      cases this,
      exact hb' (or.inl (or.inl hc)),
      { exact hS', },
      { rw supported_action_atom_perm_domain_eq _ hS',
        exact or.inl (or.inl (or.inl (or.inl hc))), }, },
    by_cases hb'' : b ∈
      (supported_action S (λ C, π ((B.cons $ coe_lt hδ).comp C)) C).atom_perm.domain,
    { rw supported_action_atom_perm_domain_eq at hb'',
      obtain ((hb'' | hb'') | hb'') := hb'',
      { cases hb' hb'', },
      { rw mem_image at hb'',
        obtain ⟨c, hc, hbc⟩ := hb'',
        sorry,
        -- obtain ⟨c, (hc | hc) | hc, hbc⟩ := hb'',
        -- {  },
         },
      { cases eq_of_mem_litter_set_of_mem_litter_set hb (local_perm.sandbox_subset_subset _ _ hb''),
        cases sandbox_litter_not_banned S C (banned_litter.support_litter _ hL), },
      { exact hS', }, },
    have hlitter := (supported_perm_of_support_map_exactly_approximates
      π hπ hδ B S hS C).mem_litter_set b hb'',
    rw [hb, struct_perm.of_bot_smul, struct_perm.of_bot_smul, hL'] at hlitter,
    have := mt (hpreimage L hL hlitter),
    clear hpreimage,
    simp only [not_exists, not_forall, not_not] at this,
    obtain ⟨L', hL', hbL'⟩ := this himage,
    by_cases hLL' : L = L',
    { cases hLL',
      exact hbL', },
    have houtside := mapped_outside.mk hbL'
      (λ h, hLL' (hS'.near_litter_injective hL hL'
        (near_litter.inter_nonempty_of_fst_eq_fst
          (eq_of_mem_litter_set_of_mem_litter_set hlitter h)))) himage,
    have : (struct_perm.derivative C
        (π.supported_perm_of_support_map hπ hδ B S hS).to_struct_perm •
        ((mapped_outside_equiv S L' C hL').symm ⟨_, houtside⟩ : atom)) =
      struct_perm.derivative C
        (π.supported_perm_of_support_map hπ hδ B S hS).to_struct_perm • b,
    { have := (supported_perm_of_support_map_exactly_approximates π hπ hδ B S hS C).map_atom _ _,
      rw struct_perm.of_bot_smul at this,
      rw ← this,
      rw supported_action_smul_mapped_outside_equiv,
      refl,
      { exact hS', },
      { rw supported_action_atom_perm_domain_eq _ hS',
        refine or.inl (or.inl (or.inr _)),
        simp only [mem_Union],
        exact ⟨L', hL', ((mapped_outside_equiv S L' C hL').symm ⟨_, houtside⟩).prop⟩, }, },
    rw smul_left_cancel_iff at this,
    rw ← this at hb,
    have := mapped_outside_subset_subset L' C hL'
      ((mapped_outside_equiv S L' C hL').symm ⟨_, houtside⟩).prop,
    rw [mem_litter_set, hb] at this,
    have h₁ := preimage_litter_not_banned S C,
    have h₂ := banned_litter.support_litter L hL,
    rw this at h₂,
    contradiction, },
  { intro ha,
    by_cases himage : ∃ (b : atom) (hb : (inl b, C) ∈ S.carrier),
      struct_perm.derivative C (π.supported_perm_of_support_map hπ hδ B S hS).to_struct_perm • a =
      S.atom_image b C hb,
    { obtain ⟨b, hb, hab⟩ := himage,
      have : a = b,
      { have := (supported_perm_of_support_map_exactly_approximates π hπ hδ B S hS C).map_atom b _,
        have := hab.trans ((supported_action_smul_atom_eq _ _ _ _ _ _).symm.trans this),
        simp only [struct_perm.of_bot_smul, smul_left_cancel_iff] at this,
        exact this,
        exact hS',
        rw supported_action_atom_perm_domain_eq _ hS',
        exact or.inl (or.inl (or.inl (or.inl hb))), },
      cases this,
      refine ⟨(struct_perm.derivative C
        (π.supported_perm_of_support_map hπ hδ B S hS).to_struct_perm)⁻¹ • a, _, _⟩,
      { -- Need an assumption on S.
        sorry, },
      { rw smul_inv_smul, }, },
    simp only [not_exists] at himage,
    by_cases himage' : ∃ (b : atom) (hb : (inl b, C) ∈ S.carrier),
      a = S.atom_image b C hb,
    { obtain ⟨b, hb, hab⟩ := himage',
      refine ⟨b, _, _⟩,
      { -- Need an assumption on S.
        sorry, },
      { have := (supported_perm_of_support_map_exactly_approximates π hπ hδ B S hS C).map_atom b _,
        have := hab.trans ((supported_action_smul_atom_eq _ _ _ _ _ _).symm.trans this),
        rw struct_perm.of_bot_smul at this,
        exact this.symm,
        exact hS',
        rw supported_action_atom_perm_domain_eq _ hS',
        exact or.inl (or.inl (or.inl (or.inl hb))), }, },
    by_cases houtside : mapped_outside S L C hL a,
    { refine ⟨(mapped_outside_equiv S L C hL).symm ⟨_, houtside⟩,
        mapped_outside_subset_subset L C hL
          ((mapped_outside_equiv S L C hL).symm ⟨_, houtside⟩).prop, _⟩,
      have := (supported_perm_of_support_map_exactly_approximates π hπ hδ B S hS C).map_atom _ _,
      rw struct_perm.of_bot_smul at this,
      rw [← this, supported_action_smul_mapped_outside_equiv],
      refl,
      exact hS',
      rw supported_action_atom_perm_domain_eq _ hS',
      refine or.inl (or.inl (or.inr _)),
      simp only [mem_Union],
      exact ⟨_, _, ((mapped_outside_equiv S L C hL).symm ⟨_, houtside⟩).prop⟩, },
    { simp only [mapped_outside_iff, set_like.mem_coe, mem_litter_set, ne.def, not_and,
        not_forall, not_not] at houtside,
      have haL := not_not.mp (mt (houtside ha) (by simpa only using himage')),
      refine ⟨_, _, smul_inv_smul _ _⟩,
      -- Use `ha` and an assumption on S.
      sorry, }, },
end

lemma supported_perm_smul_near_litter_eq (π : struct_approx β) (hπ : π.free)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (S : support_map h.δ)
  (hS₁ : (show struct_approx (h.δ : Iic α), from
    supported_action S (λ (B : extended_index h.δ), π ((h.B.cons $ coe_lt h.hδ).comp B))).free)
  (hS₂ : inflexible_support_map H h ≤ S) (hS₃ : ∀ B, S.injective B)
  (hS₄ : support_map_supported π hπ h H S hS₁)
  (d : support_condition h.δ) (hd₁ : d ∈ designated_support h.t)
  (B : extended_index h.δ) (N : near_litter)
  (ih : ∀ (y : support_condition h.δ), y ≺[α] (inr N, B) →
    (∃ d ∈ designated_support h.t, relation.refl_trans_gen (constrains α h.δ) y d) →
    π.supported_perm_of_support_map hπ h.hδ h.B S hS₁ • y =
      π.supported_perm hπ h H • y)
  (hd₂ : relation.refl_trans_gen (constrains α h.δ) (inr N, B) d) :
  struct_perm.derivative B (π.supported_perm_of_support_map hπ h.hδ h.B S hS₁).to_struct_perm • N =
  struct_perm.derivative B (π.supported_perm hπ h H).to_struct_perm • N :=
begin
  by_cases hN : N.is_litter,
  { obtain ⟨L', rfl⟩ := hN.exists_litter_eq,
    exact hS₄ L' B d hd₁ hd₂
      (supported_perm_smul_litter_eq π hπ h H S hS₁ hS₂ hS₃ d hd₁ B L' ih hd₂), },
  have hL : (_, _) = (_, _) := ih _ (constrains.near_litter N (near_litter.not_is_litter hN) B)
    ⟨d, hd₁, relation.refl_trans_gen.head
      (constrains.near_litter N (near_litter.not_is_litter hN) B) hd₂⟩,
  have ha := λ a ha, ih _ (constrains.symm_diff N a ha B)
    ⟨d, hd₁, relation.refl_trans_gen.head (constrains.symm_diff N a ha B) hd₂⟩,
  change ∀ a h, (_, _) = (_, _) at ha,
  simp only [smul_inl, smul_inr, prod.mk.inj_iff, eq_self_iff_true, and_true] at hL ha,
  refine set_like.coe_injective _,
  refine (near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul _ _).trans
    ((near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul _ _).trans _).symm,
  simp only [struct_perm.to_near_litter_perm_smul, litter.coe_to_near_litter],
  congr' 1,
  { exact congr_arg (λ (N : near_litter), (N.2 : set atom)) hL.symm, },
  ext a : 1,
  simp only [struct_perm.to_near_litter_perm_smul, mem_smul_set_iff_inv_smul_mem],
  split,
  { intro ha',
    have := (ha _ ha').trans (smul_inv_smul _ _),
    rw smul_eq_iff_eq_inv_smul at this,
    refine mem_of_eq_of_mem _ ha',
    simp only [← map_inv] at this ⊢,
    exact this.symm, },
  { intro ha',
    have := (ha _ ha').symm.trans (smul_inv_smul _ _),
    rw smul_eq_iff_eq_inv_smul at this,
    refine mem_of_eq_of_mem _ ha',
    simp only [← map_inv] at this ⊢,
    exact this.symm, },
end

lemma supported_perm_smul_condition_eq (π : struct_approx β) (hπ : π.free)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (S : support_map h.δ)
  (hS₁ : (show struct_approx (h.δ : Iic α), from
    supported_action S (λ (B : extended_index h.δ), π ((h.B.cons $ coe_lt h.hδ).comp B))).free)
  (hS₂ : inflexible_support_map H h ≤ S)
  (hS₃ : ∀ B, S.injective B)
  (hS₄ : support_map_supported π hπ h H S hS₁)
  {c : support_condition h.δ} :
  (∃ d ∈ designated_support h.t, relation.refl_trans_gen (constrains α h.δ) c d) →
  supported_perm_of_support_map π hπ h.hδ h.B S hS₁ • c = supported_perm π hπ h H • c :=
begin
  refine (constrains_wf α h.δ).induction c _,
  rintros c ih ⟨d, hd₁, hd₂⟩,
  obtain ⟨a | N, B⟩ := c,
  { refine prod.ext _ rfl,
    change inl _ = inl _,
    exact congr_arg inl (supported_perm_smul_atom_eq π hπ h H S hS₁ hS₂ hS₃ d hd₁ B a hd₂), },
  { refine prod.ext _ rfl,
    change inr _ = inr _,
    exact congr_arg inr
      (supported_perm_smul_near_litter_eq π hπ h H S hS₁ hS₂ hS₃ hS₄ d hd₁ B N ih hd₂), },
end

/-- As long as a support map extends the `inflexible_support_map`, the supported action generated
by this map agrees with the supported action generated by the `inflexible_support_map` on `t`. -/
lemma supported_perm_smul_eq (π : struct_approx β) (hπ : π.free)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (S : support_map h.δ)
  (hS₁ : (show struct_approx (h.δ : Iic α), from
    supported_action S (λ (B : extended_index h.δ), π ((h.B.cons $ coe_lt h.hδ).comp B))).free)
  (hS₂ : inflexible_support_map H h ≤ S)
  (hS₃ : ∀ B, S.injective B)
  (hS₄ : support_map_supported π hπ h H S hS₁) :
  supported_perm π hπ h H • h.t = supported_perm_of_support_map π hπ h.hδ h.B S hS₁ • h.t :=
begin
  rw [smul_eq_iff_eq_inv_smul, smul_smul],
  symmetry,
  refine (designated_support h.t).supports _ _,
  intros c hc,
  rw [mul_smul, inv_smul_eq_iff],
  exact supported_perm_smul_condition_eq π hπ h H S hS₁ hS₂ hS₃ hS₄
    ⟨c, hc, relation.refl_trans_gen.refl⟩,
end-/

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

end struct_approx

end con_nf
