import phase2.strong_support
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

/-- We say *freedom of action* holds at level `β` if every `β`-free structural approximation
exactly approximates some `β`-allowable permutation. -/
def freedom_of_action (β : Iic α) : Prop :=
∀ (π₀ : struct_approx β), π₀.free → ∃ (π : allowable β), π₀.exactly_approximates π.to_struct_perm

/-- A proof-relevant statement that `L` is `A`-inflexible (excluding `ε = ⊥`). -/
structure inflexible_coe (L : litter) (A : extended_index β) :=
(γ : Iic α) (δ ε : Iio α) (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
(B : quiver.path (β : type_index) γ) (t : tangle δ)
(hL : L = f_map (with_bot.coe_ne_coe.mpr $ coe_ne' hδε) t)
(hA : A = (B.cons (coe_lt hε)).cons (with_bot.bot_lt_coe _))

instance (L : litter) (A : extended_index β) : subsingleton (inflexible_coe L A) :=
begin
  constructor,
  rintros ⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₁, rfl, rfl⟩
    ⟨γ₂, δ₂, ε₂, hδ₂, hε₂, hδε₂, B₂, t₂, hL₂, hA₂⟩,
  cases subtype.coe_injective (coe_eq_coe.mp (path.obj_eq_of_cons_eq_cons hA₂)),
  cases subtype.coe_injective (coe_eq_coe.mp (path.obj_eq_of_cons_eq_cons
    (path.heq_of_cons_eq_cons hA₂).eq)),
  cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons hA₂).eq).eq,
  have h₁ := f_map_β (with_bot.coe_ne_coe.mpr $ coe_ne' hδε₁) t₁,
  have h₂ := f_map_β (with_bot.coe_ne_coe.mpr $ coe_ne' hδε₂) t₂,
  rw [hL₂, h₂] at h₁,
  cases subtype.coe_injective (coe_eq_coe.mp h₁),
  cases f_map_injective _ hL₂,
  refl,
end

/-- A proof-relevant statement that `L` is `A`-inflexible, where `δ = ⊥`. -/
structure inflexible_bot (L : litter) (A : extended_index β) :=
(γ : Iic α) (ε : Iio α) (hε : (ε : Λ) < γ)
(B : quiver.path (β : type_index) γ) (a : atom)
(hL : L = f_map (show (⊥ : type_index) ≠ (ε : Λ), from with_bot.bot_ne_coe) a)
(hA : A = (B.cons (coe_lt hε)).cons (with_bot.bot_lt_coe _))

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
  have h₁ := f_map_β (show (⊥ : type_index) ≠ (ε₁ : Λ), from with_bot.bot_ne_coe) a₁,
  have h₂ := f_map_β (with_bot.coe_ne_coe.mpr $ coe_ne' hδε₂) t₂,
  rw [hL₂, h₂] at h₁,
  cases h₁,
end

lemma inflexible_coe.δ_lt_β {L : litter} {A : extended_index β} (h : inflexible_coe L A) :
  (h.δ : Λ) < β :=
h.hδ.trans_le (show _, from with_bot.coe_le_coe.mp (le_of_path h.B))

lemma inflexible_bot.constrains {L : litter} {A : extended_index β} (h : inflexible_bot L A) :
  relation.trans_gen (constrains α β)
    (inl h.a, (h.B.cons (with_bot.bot_lt_coe _))) (inr L.to_near_litter, A) :=
begin
  have := constrains.f_map_bot h.hε h.B h.a,
  rw [← h.hL, ← h.hA] at this,
  exact relation.trans_gen.single this,
end

class freedom_of_action_hypothesis (β : Iic α) :=
(freedom_of_action_of_lt : ∀ γ < β, freedom_of_action γ)

export freedom_of_action_hypothesis (freedom_of_action_of_lt)

variable [freedom_of_action_hypothesis β]

-- TODO: Move!
instance {δ : Iio α} : mul_action (allowable (δ : Iic α)) (tangle (δ : Λ)) :=
show mul_action (allowable δ) (tangle δ), from infer_instance

def inflexible_support_map {L : litter} {A : extended_index β}
  (H : hypothesis ⟨inr L.to_near_litter, A⟩) (h : inflexible_coe L A) : support_map h.δ := {
  carrier := {c | relation.trans_gen (constrains α β)
    (c.1, (h.B.cons (coe_lt h.hδ)).comp c.2)
    (inr (f_map (coe_ne_coe.mpr $ coe_ne' h.hδε) h.t).to_near_litter,
      (h.B.cons (coe_lt h.hε)).cons (bot_lt_coe _))},
  small := begin
    have := constrains_closure_small' α (small_singleton
      (inr (f_map (coe_ne_coe.mpr $ coe_ne' h.hδε) h.t).to_near_litter,
        (h.B.cons (coe_lt h.hε)).cons (bot_lt_coe _))),
    simp only [mem_singleton_iff, exists_prop, exists_eq_left] at this,
    refine lt_of_le_of_lt _ this,
    refine ⟨⟨λ c, ⟨_, c.prop.to_refl⟩, λ c d h, _⟩⟩,
    simp only [subtype.mk_eq_mk, prod.mk.inj_iff, path.comp_inj_right] at h,
    ext, exact h.1, exact h.2,
  end,
  atom_image := λ a B ha, H.atom_image a ((h.B.cons (coe_lt h.hδ)).comp B)
    (by rwa [← h.hL, ← h.hA] at ha),
  near_litter_image := λ N B hN, H.near_litter_image N ((h.B.cons (coe_lt h.hδ)).comp B)
    (by rwa [← h.hL, ← h.hA] at hN),
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

noncomputable def litter_completion (π : struct_approx β) (hπ : π.free)
  (L : litter) (A : extended_index β) (H : hypothesis ⟨inr L.to_near_litter, A⟩) : litter :=
if h : nonempty (inflexible_coe L A) then
  f_map (with_bot.coe_ne_coe.mpr $ coe_ne' h.some.hδε)
  ((freedom_of_action_of_lt (h.some.δ : Iic α) h.some.δ_lt_β _
    (π.litter_approx_free hπ H h.some)).some • h.some.t)
else if h : nonempty (inflexible_bot L A) then
  f_map (show (⊥ : type_index) ≠ (h.some.ε : Λ), from with_bot.bot_ne_coe)
    (H.atom_image h.some.a (h.some.B.cons (with_bot.bot_lt_coe _)) h.some.constrains)
else
  near_litter_approx.flexible_completion α (π A) A • L

end struct_approx

end con_nf
