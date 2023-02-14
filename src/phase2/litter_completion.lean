import phase2.reduction
import phase2.supported_action

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

def inflexible_support {L : litter} {A : extended_index β} (h : inflexible_coe L A) :
  set (support_condition h.δ) :=
(λ c, (c.1, (h.B.cons (coe_lt h.hδ)).comp c.2)) ⁻¹'
reduction α {(inr (f_map (coe_ne_coe.mpr $ coe_ne' h.hδε) h.t).to_near_litter,
  (h.B.cons (coe_lt h.hε)).cons (bot_lt_coe _))}

lemma inflexible_support_small {L : litter} {A : extended_index β} (h : inflexible_coe L A) :
  small (inflexible_support h) :=
begin
  have := reduction_small α (small_singleton _),
  refine lt_of_le_of_lt ((cardinal.mk_preimage_of_injective _ _ _)) this,
  intros c d h,
  simp only [prod.mk.inj_iff, path.comp_inj_right] at h,
  exact prod.ext h.1 h.2,
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

/-
lemma inflexible_support_supports_condition'
  (π : allowable β) (c : support_condition β) (hc : ¬reduced α c)
  (hπ : ∀ ⦃a : support_condition β⦄, a ≺[α] c → π • a = a) :
  π • c = c :=
begin
  obtain ⟨a | N, A⟩ := c,
  { cases hc (reduced.mk_atom a A), },
  refine prod.ext _ rfl,
  change inr _ = inr _,
  refine congr_arg inr _,
  rw [not_reduced_iff] at hc,
  by_cases N.is_litter,
  { obtain ⟨L, rfl⟩ := h.exists_litter_eq,
    rw litter.to_near_litter_fst at *,
    have := hc (near_litter.is_litter.mk _),
    rw inflexible_iff at this,
    obtain (⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ | this') := this,
    { have := struct_perm.derivative_derivative π.to_struct_perm
        (B.cons (coe_lt hε)) (path.nil.cons (bot_lt_coe _)),
      rw [path.comp_cons, path.comp_nil] at this,
      rw ← this,
      rw @allowable.derivative_to_struct_perm _ _ _ _ (β : Iic_index α) (ε : Iic_index α)
        (B.cons $ coe_lt hε) π,
      rw [struct_perm.derivative_bot_smul, allowable.to_struct_perm_smul],
      have := inflexible_support_supports_f_map hδ hε hδε hπ hc,
      sorry, }, },
end

lemma inflexible_support_supports_condition {L : litter} {A : extended_index ↑β}
  (h : inflexible_coe L A) (π : allowable h.δ)
  (hπ : ∀ ⦃a : support_condition ↑(h.δ)⦄, a ∈ inflexible_support h → π • a = a)
  (c : support_condition ↑(h.δ))
  (hc : c ∈ (designated_support h.t).carrier) :
  π • c = c :=
begin
  sorry
end

lemma inflexible_support_supports_tangle {L : litter} {A : extended_index β}
  (h : inflexible_coe L A) : mul_action.supports (allowable h.δ) (inflexible_support h) h.t :=
λ π hπ, (designated_support h.t).supports π (inflexible_support_supports_condition h π hπ)
-/

-- lemma inflexible_support_supports {L : litter} {A : extended_index β} (h : inflexible_coe L A) :
--   ∀ ⦃π : allowable (h.γ : Iic_index α)⦄, (∀ c ∈ inflexible_support h,
--     (allowable_derivative (h.γ : Iic_index α) (h.δ : Iio_index α) (coe_lt h.hδ) π) • c = c) →
--   allowable_derivative (h.γ : Iic_index α) h.ε (coe_lt h.hε) π • L = L :=
-- begin
--   intros π hπ,
--   have := smul_f_map (Iio_coe h.δ) h.ε (coe_lt h.hδ) h.hε (Iio.coe_injective.ne h.hδε) π h.t,
--   rw inflexible_support_supports_tangle h _ hπ at this,
--   -- The `convert` and other nonsense won't be needed in Lean 4.
--   convert this;
--   { refine h.hL.trans _,
--     congr;
--     ext;
--     refl, },
-- end

def inflexible_support_map {L : litter} {A : extended_index β}
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (h : inflexible_coe L A) : support_map h.δ := {
  carrier := inflexible_support h,
  small := inflexible_support_small h,
  atom_image := λ a B ha, H.atom_image a ((h.B.cons (coe_lt h.hδ)).comp B)
    (begin
      rw [inflexible_support, ← h.hL, ← h.hA, reduction_singleton_of_not_reduced] at ha,
      exact ha.1,
      rintro (_ | ⟨_, _, hL⟩),
      have := inflexible.mk_coe h.hδ h.hε h.hδε h.B h.t,
      rw [← h.hL, ← h.hA] at this,
      exact hL this,
    end),
  near_litter_image := λ N B hN, H.near_litter_image N ((h.B.cons (coe_lt h.hδ)).comp B)
    (begin
      rw [inflexible_support, ← h.hL, ← h.hA, reduction_singleton_of_not_reduced] at hN,
      exact hN.1,
      rintro (_ | ⟨_, _, hL⟩),
      have := inflexible.mk_coe h.hδ h.hε h.hδε h.B h.t,
      rw [← h.hL, ← h.hA] at this,
      exact hL this,
    end),
}

lemma litter_approx_free (π : struct_approx β) (hπ : π.free) {L : litter} {A : extended_index β}
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (h : inflexible_coe L A) :
  @struct_approx.free _ _ _ _ (h.δ : Iic α)
  (supported_action (inflexible_support_map H h) (λ B, π ((h.B.cons $ coe_lt h.hδ).comp B))) :=
begin
  intros B L' hL',
  cases hL',
  exact flexible_of_comp_flexible (hπ _ L' hL'),
  exact hL'.1,
end

noncomputable def supported_perm_of_support_map (π : struct_approx β) (hπ : π.free)
  {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ) (B : path (β : type_index) γ) (S : support_map δ)
  (hS : (show struct_approx (δ : Iic α), from supported_action S
    (λ (C : extended_index δ), π ((B.cons $ coe_lt hδ).comp C))).free) : allowable δ :=
(freedom_of_action_of_lt (δ : Iic α)
  (hδ.trans_le (show _, from coe_le_coe.mp (le_of_path B))) _ hS).some

lemma supported_perm_of_support_map_exactly_approximates (π : struct_approx β) (hπ : π.free)
  {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ) (B : path (β : type_index) γ) (S : support_map δ)
  (hS : (show struct_approx (δ : Iic α), from supported_action S
    (λ (C : extended_index δ), π ((B.cons $ coe_lt hδ).comp C))).free) :
  (supported_action S (λ C, π ((B.cons $ coe_lt hδ).comp C)))
    .exactly_approximates (supported_perm_of_support_map π hπ hδ B S hS).to_struct_perm :=
(freedom_of_action_of_lt (δ : Iic α)
  (hδ.trans_le (show _, from coe_le_coe.mp (le_of_path B))) _ hS).some_spec.1

lemma supported_perm_of_support_map_lawful_atom_map (π : struct_approx β) (hπ : π.free)
  {γ : Iic α} {δ : Iio α} (hδ : (δ : Λ) < γ) (B : path (β : type_index) γ) (S : support_map δ)
  (hS : (show struct_approx (δ : Iic α), from supported_action S
    (λ (C : extended_index δ), π ((B.cons $ coe_lt hδ).comp C))).free) :
  (show struct_approx (δ : Iic α), from supported_action S
    (λ C, π ((B.cons $ coe_lt hδ).comp C))).lawful_atom_map
  (supported_perm_of_support_map π hπ hδ B S hS) :=
(freedom_of_action_of_lt (δ : Iic α)
  (hδ.trans_le (show _, from coe_le_coe.mp (le_of_path B))) _ hS).some_spec.2

noncomputable def supported_perm (π : struct_approx β) (hπ : π.free)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) : allowable h.δ :=
supported_perm_of_support_map π hπ h.hδ h.B _ (π.litter_approx_free hπ H h)

lemma supported_perm_exactly_approximates (π : struct_approx β) (hπ : π.free)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) :
  (supported_action (inflexible_support_map H h) (λ C, π ((h.B.cons $ coe_lt h.hδ).comp C)))
    .exactly_approximates (supported_perm π hπ h H).to_struct_perm :=
supported_perm_of_support_map_exactly_approximates π hπ h.hδ h.B _ (π.litter_approx_free hπ H h)

lemma supported_perm_lawful_atom_map (π : struct_approx β) (hπ : π.free)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) :
  (show struct_approx (h.δ : Iic α), from supported_action
    (inflexible_support_map H h) (λ C, π ((h.B.cons $ coe_lt h.hδ).comp C))).lawful_atom_map
  (supported_perm π hπ h H) :=
supported_perm_of_support_map_lawful_atom_map π hπ h.hδ h.B _ (π.litter_approx_free hπ H h)

lemma mem_inflexible_support (π : struct_approx β) (hπ : π.free)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (B : extended_index h.δ) (a : atom)
  (d : support_condition h.δ) (hd₁ : d ∈ designated_support h.t)
  (hd₂ : relation.refl_trans_gen (constrains α h.δ) (inl a, B) d) :
    (inl a, B) ∈ inflexible_support h :=
begin
  refine ⟨_, reduced.mk_atom _ _⟩,
  simp only [mem_singleton_iff, exists_prop, exists_eq_left, mem_set_of_eq],
  exact relation.refl_trans_gen.tail (refl_trans_gen_constrains_comp hd₂ _)
    (constrains.f_map h.hδ h.hε h.hδε h.B h.t d hd₁),
end

lemma supported_perm_smul_atom_eq (π : struct_approx β) (hπ : π.free)
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

lemma supported_perm_smul_near_litter_eq (π : struct_approx β) (hπ : π.free)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (S : support_map h.δ)
  (hS₁ : (show struct_approx (h.δ : Iic α), from
    supported_action S (λ (B : extended_index h.δ), π ((h.B.cons $ coe_lt h.hδ).comp B))).free)
  (hS₂ : inflexible_support_map H h ≤ S) (hS₃ : ∀ B, S.injective B)
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
  -- have := supported_perm_smul_litter_eq π hπ h H S hS₁ hS₂ hS₃ d hd₁ B N.fst,
  sorry
end

lemma supported_perm_smul_condition_eq (π : struct_approx β) (hπ : π.free)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (S : support_map h.δ)
  (hS₁ : (show struct_approx (h.δ : Iic α), from
    supported_action S (λ (B : extended_index h.δ), π ((h.B.cons $ coe_lt h.hδ).comp B))).free)
  (hS₂ : inflexible_support_map H h ≤ S)
  (hS₃ : ∀ B, S.injective B)
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
      (supported_perm_smul_near_litter_eq π hπ h H S hS₁ hS₂ hS₃ d hd₁ B N ih hd₂), },
end

/-- As long as a support map extends the `inflexible_support_map`, the supported action generated
by this map agrees with the supported action generated by the `inflexible_support_map` on `t`. -/
lemma supported_perm_smul_eq (π : struct_approx β) (hπ : π.free)
  {L : litter} {A : extended_index β} (h : inflexible_coe L A)
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (S : support_map h.δ)
  (hS₁ : (show struct_approx (h.δ : Iic α), from
    supported_action S (λ (B : extended_index h.δ), π ((h.B.cons $ coe_lt h.hδ).comp B))).free)
  (hS₂ : inflexible_support_map H h ≤ S)
  (hS₃ : ∀ B, S.injective B) :
  supported_perm π hπ h H • h.t = supported_perm_of_support_map π hπ h.hδ h.B S hS₁ • h.t :=
begin
  rw [smul_eq_iff_eq_inv_smul, smul_smul],
  symmetry,
  refine (designated_support h.t).supports _ _,
  intros c hc,
  rw [mul_smul, inv_smul_eq_iff],
  exact supported_perm_smul_condition_eq π hπ h H S hS₁ hS₂ hS₃
    ⟨c, hc, relation.refl_trans_gen.refl⟩,
end

noncomputable def litter_completion (π : struct_approx β) (hπ : π.free)
  (L : litter) (A : extended_index β) (H : hypothesis ⟨inr L.to_near_litter, A⟩) : litter :=
if h : nonempty (inflexible_coe L A) then
  f_map (coe_ne_coe.mpr $ coe_ne' h.some.hδε) (supported_perm π hπ h.some H • h.some.t)
else if h : nonempty (inflexible_bot L A) then
  f_map (show (⊥ : type_index) ≠ (h.some.ε : Λ), from bot_ne_coe)
    (H.atom_image h.some.a (h.some.B.cons (bot_lt_coe _)) h.some.constrains)
else
  near_litter_approx.flexible_completion α (π A) A • L

end struct_approx

end con_nf
