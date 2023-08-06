import phase2.flexible
import phase2.near_litter_action

open cardinal quiver set sum with_bot
open_locale cardinal classical pointwise

universe u

namespace con_nf
variable [params.{u}]

/-!
# Structural actions
-/

/-- A `β`-structural action is a product that assigns a near-litter action to each `β`-extended
index. -/
def struct_action (β : type_index) := extended_index β → near_litter_action

namespace struct_action

def lawful {β : type_index} (φ : struct_action β) : Prop := ∀ B, (φ B).lawful

/-- This structural action maps flexible litters to flexible litters. -/
def map_flexible {α : Λ} [position_data.{}] [phase_2_assumptions α]
  {β : Iio α} (φ : struct_action β) : Prop :=
∀ (L : litter) B hL,
  flexible α L B → flexible α (((φ B).litter_map L).get hL).1 B

section precise

def precise {β : type_index} (φ : struct_action β) : Prop :=
∀ B, (φ B).precise

variables {α : Λ} [position_data.{}] [phase_2_assumptions α] {β : Iio α} (φ : struct_action β)

noncomputable def complete (hφ : φ.lawful) : struct_approx β :=
λ B, (φ B).complete (hφ B) B

lemma complete_apply (hφ : φ.lawful) (B : extended_index β) :
  φ.complete hφ B = (φ B).complete (hφ B) B := rfl

lemma smul_atom_eq {hφ : φ.lawful}
  {π : struct_perm β} (hπ : (φ.complete hφ).exactly_approximates π)
  {a : atom} {B : extended_index β} (ha : ((φ B).atom_map a).dom) :
  struct_perm.derivative B π • a = ((φ B).atom_map a).get ha :=
begin
  have := (φ B).smul_atom_eq (hπ B) ha,
  rw struct_perm.of_bot_smul at this,
  exact this,
end

lemma smul_to_near_litter_eq_of_precise {hφ : φ.lawful} (hφp : φ.precise)
  {π : struct_perm β} (hπ : (φ.complete hφ).exactly_approximates π)
  {L : litter} {B : extended_index β} (hL : ((φ B).litter_map L).dom)
  (hπL : struct_perm.derivative B π • L = (((φ B).litter_map L).get hL).1) :
  struct_perm.derivative B π • L.to_near_litter = ((φ B).litter_map L).get hL :=
begin
  have := (φ B).smul_to_near_litter_eq_of_precise_at (hπ B) hL (hφp B hL) _,
  { rw struct_perm.of_bot_smul at this,
    exact this, },
  { rw struct_perm.of_bot_smul,
    exact hπL, },
end

lemma smul_near_litter_eq_of_precise {hφ : φ.lawful} (hφp : φ.precise)
  {π : struct_perm β} (hπ : (φ.complete hφ).exactly_approximates π)
  {N : near_litter} {B : extended_index β} (hN : ((φ B).litter_map N.1).dom)
  (hπL : struct_perm.derivative B π • N.1 = (((φ B).litter_map N.1).get hN).1) :
  ((struct_perm.derivative B π • N : near_litter) : set atom) =
  ((φ B).litter_map N.1).get hN ∆ (struct_perm.derivative B π • (litter_set N.1 ∆ N)) :=
begin
  have := (φ B).smul_near_litter_eq_of_precise_at (hπ B) hN (hφp B hN) _,
  { rw struct_perm.of_bot_smul at this,
    exact this, },
  { rw struct_perm.of_bot_smul,
    exact hπL, },
end

end precise

variables {α : Λ} [position_data.{}] [phase_2_assumptions α] {β : Iio α}

/-- A structural action *supports* a tangle if it defines an image for everything
in the reduction of its designated support. -/
structure supports (φ : struct_action β) (t : tangle β) : Prop :=
(atom_mem : ∀ a B, (inl a, B) ∈ reduced_support α t → ((φ B).atom_map a).dom)
(litter_mem : ∀ (L : litter) B,
  (inr L.to_near_litter, B) ∈ reduced_support α t → ((φ B).litter_map L).dom)

/-- Two structural actions are *compatible* for a tangle if they both support the
tangle and agree on the reduction of its designated support. -/
structure compatible (φ ψ : struct_action β) (t : tangle β) : Prop :=
(φ_supports : φ.supports t)
(ψ_supports : ψ.supports t)
(atom_map : ∀ a B ha, ((φ B).atom_map a).get (φ_supports.atom_mem a B ha) =
  ((ψ B).atom_map a).get (ψ_supports.atom_mem a B ha))
(litter_map : ∀ L B hL, ((φ B).litter_map L).get (φ_supports.litter_mem L B hL) =
  ((ψ B).litter_map L).get (ψ_supports.litter_mem L B hL))

/-- The action of a structural action on support conditions. -/
noncomputable def support_condition_map_or_else (φ : struct_action β) :
  support_condition β → support_condition β
| (inl a, B) := (inl ((φ B).atom_map_or_else a), B)
| (inr N, B) := (inr ((φ B).near_litter_map_or_else N), B)

def coherent_coe (φ : struct_action β) (hφ : φ.lawful) (t : tangle β) : Prop :=
∀ ⦃π : allowable β⦄ (hπ : (φ.complete hφ).exactly_approximates π.to_struct_perm)
  (γ : Iic α) (δ ε : Iio α) (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
  (C : path (β : type_index) γ) (t' : tangle δ) (hL)
  (hc₁ : ∃ (d : support_condition β), d ∈ (designated_support t).carrier ∧
    (inr (f_map (coe_ne_coe.mpr (coe_ne' hδε)) t').to_near_litter,
      (C.cons (coe_lt hε)).cons (bot_lt_coe _)) ≤[α] d)
  (hc₂ : ∀ (c : support_condition δ), c ∈ (designated_support t').carrier →
    π • (show support_condition β, from (c.fst, (C.cons (coe_lt hδ)).comp c.snd)) =
      φ.support_condition_map_or_else (c.fst, (C.cons (coe_lt hδ)).comp c.snd)),
  f_map (subtype.coe_injective.ne (Iio.coe_injective.ne hδε))
      (show tangle δ, from
        (show allowable δ, from allowable_derivative (γ : Iic_index α) δ (coe_lt_coe.mpr hδ)
          (allowable.derivative
            (show path ((β : Iic_index α) : type_index) (γ : Iic_index α), from C) π)) • t') =
    (((φ ((C.cons (coe_lt hε)).cons (bot_lt_coe _))).litter_map
      (f_map (subtype.coe_injective.ne (Iio.coe_injective.ne hδε)) t')).get hL).fst

def coherent_bot (φ : struct_action β) (hφ : φ.lawful) : Prop :=
∀ ⦃π : allowable β⦄ (hπ : (φ.complete hφ).exactly_approximates π.to_struct_perm)
  (γ : Iic α) (ε : Iio α) (hε : (ε : Λ) < γ)
  (C : path (β : type_index) γ) (a : tangle ⊥) (hL)
  (hc : struct_perm.derivative (C.cons (bot_lt_coe _)) π.to_struct_perm • a =
    (φ (C.cons (bot_lt_coe _))).atom_map_or_else a),
  f_map (show ((⊥ : Iio_index α) : type_index) ≠ (ε : Iio_index α),
    from subtype.coe_injective.ne Iio_index.bot_ne_coe)
      ((show allowable (⊥ : Iio_index α), from
        (allowable.derivative (show path ((β : Iic_index α) : type_index) (⊥ : Iic_index α), from
          C.cons (bot_lt_coe _))) π) • a) =
    (((φ ((C.cons (coe_lt hε)).cons (bot_lt_coe _))).litter_map
      (f_map (show (⊥ : type_index) ≠ (ε : Λ), from bot_ne_coe) a)).get hL).fst

@[mk_iff] structure coherent (φ : struct_action β) (hφ : φ.lawful) (t : tangle β) : Prop :=
(coe : φ.coherent_coe hφ t)
(bot : φ.coherent_bot hφ)

lemma smul_litter_eq_of_supports (φ : struct_action β) (hφ : φ.lawful)
  {π : allowable β} (hπ : (φ.complete hφ).exactly_approximates π.to_struct_perm)
  (t : tangle β) (hφc : φ.coherent hφ t) (hφs : φ.supports t)
  (d : support_condition β) (hd : d ∈ designated_support t)
  (B : extended_index β) (L : litter)
  (ih : ∀ (e : support_condition β),
    e <[α] (inr L.to_near_litter, B) → π • e = φ.support_condition_map_or_else e)
  (hc : (inr L.to_near_litter, B) ≤[α] d) :
  struct_perm.derivative B π.to_struct_perm • L =
  (((φ B).litter_map L).get
    (hφs.litter_mem L B ⟨⟨d, hd, refl_trans_gen_near_litter hc⟩, reduced.mk_litter _ _⟩)).fst :=
begin
  by_cases hflex : inflexible α L B,
  { rw inflexible_iff at hflex,
    obtain (⟨γ, δ, ε, hδ, hε, hδε, C, t', rfl, rfl⟩ | ⟨γ, ε, hε, C, a, rfl, rfl⟩) := hflex,
    { have hc₂ := λ c hc, ih _ (relation.trans_gen.single $ constrains.f_map hδ hε hδε C t' c hc),
      have := smul_f_map (δ : Iio_index α) ε _ _ (Iio.coe_injective.ne hδε)
        (allowable.derivative
          (show path ((β : Iic_index α) : type_index) (γ : Iic_index α), from C) π) t',
      rw [← allowable.derivative_cons_apply, allowable.derivative_smul,
        ← struct_perm.derivative_bot_smul, ← struct_perm.derivative_cons] at this,
      exact this.trans (hφc.coe hπ γ δ ε hδ hε hδε C t' _ ⟨d, hd, hc⟩ hc₂), },
    { have hc : (_, _) = (_, _) := ih _ (relation.trans_gen.single $ constrains.f_map_bot hε C a),
      simp only [smul_inl, prod.mk.inj_iff, eq_self_iff_true, and_true] at hc,
      rw ← hφc.bot hπ γ ε hε C a _ hc,
      have := smul_f_map (⊥ : Iio_index α) ε _ _ (by intro h; cases h)
        (allowable.derivative
          (show path ((β : Iic_index α) : type_index) (γ : Iic_index α), from C) π) a,
      rw [← allowable.derivative_cons_apply, allowable.derivative_smul,
        ← struct_perm.derivative_bot_smul, ← struct_perm.derivative_cons,
        ← allowable.derivative_cons_apply] at this,
      exact this, }, },
  { have := hφs.litter_mem L B ⟨⟨d, hd, refl_trans_gen_near_litter hc⟩, reduced.mk_litter _ _⟩,
    rw [← struct_perm.of_bot_smul, ← (hπ B).map_litter _ (or.inl (or.inl ⟨this, hflex⟩))],
    refine ((φ B).complete_smul_litter_eq L).trans _,
    rw [near_litter_action.flexible_litter_perm_apply_eq, (φ B).rough_litter_map_or_else_of_dom],
    exact this,
    exact hflex, },
end

lemma smul_support_condition_eq (φ : struct_action β) (hφ : φ.lawful) (hφp : φ.precise)
  {π : allowable β} (hπ : (φ.complete hφ).exactly_approximates π.to_struct_perm)
  (t : tangle β) (hwc : φ.coherent hφ t) (hws : φ.supports t)
  (c d : support_condition β)
  (hc : c ≤[α] d)
  (hd : d ∈ designated_support t) :
  π • c = φ.support_condition_map_or_else c :=
begin
  revert d,
  refine (constrains_wf α β).trans_gen.induction c _,
  rintros c ih d hc hd,
  obtain ⟨a | N, B⟩ := c,
  { refine prod.ext _ rfl,
    change inl _ = inl _,
    refine congr_arg inl _,
    rw [φ.smul_atom_eq hπ (hws.atom_mem a B ⟨⟨d, hd, hc⟩, reduced.mk_atom a B⟩),
      near_litter_action.atom_map_or_else_of_dom], },
  refine prod.ext _ rfl,
  change inr _ = inr _,
  refine congr_arg inr (set_like.coe_injective _),
  have ih' := λ e he, ih e (relation.trans_gen.single he) d
    (relation.refl_trans_gen.head he hc) hd,
  rw φ.smul_near_litter_eq_of_precise hφp hπ (hws.litter_mem N.1 B _) _,
  { simp only [near_litter_action.near_litter_map_or_else,
      near_litter.coe_mk, subtype.coe_mk],
    rw (φ B).litter_map_or_else_of_dom (hws.litter_mem N.1 B _),
    congr' 1,
    ext a : 1,
    rw [mem_smul_set, mem_image],
    split,
    { rintro ⟨b, hb₁, hb₂⟩,
      have : (_, _) = (_, _) := ih' _ (constrains.symm_diff N _ hb₁ B),
      simp only [smul_inl, smul_inv_smul, prod.mk.inj_iff] at this,
      rw this.1 at hb₂,
      exact ⟨b, hb₁, hb₂⟩, },
    { rintro ⟨b, hb₁, hb₂⟩,
      have : (_, _) = (_, _) := ih' _ (constrains.symm_diff N _ hb₁ B),
      simp only [smul_inl, smul_inv_smul, prod.mk.inj_iff] at this,
      rw ← this.1 at hb₂,
      exact ⟨b, hb₁, hb₂⟩, },
    { exact ⟨⟨d, hd, refl_trans_gen_near_litter hc⟩, reduced.mk_litter _ _⟩, }, },
  refine φ.smul_litter_eq_of_supports hφ hπ t hwc hws d hd B N.1 _ (refl_trans_gen_near_litter hc),
  exact λ e he, ih e (trans_gen_near_litter he) d
    (relation.refl_trans_gen.trans he.to_refl (refl_trans_gen_near_litter hc)) hd,
end

lemma smul_eq_smul_tangle (φ ψ : struct_action β)
  (hφ : φ.lawful) (hψ : ψ.lawful)
  (hφp : φ.precise) (hψp : ψ.precise)
  (t : tangle β) (h : compatible φ ψ t)
  (hφc : φ.coherent hφ t) (hψc : ψ.coherent hψ t)
  {πφ πψ : allowable β}
  (hπφ : (φ.complete hφ).exactly_approximates πφ.to_struct_perm)
  (hπψ : (ψ.complete hψ).exactly_approximates πψ.to_struct_perm) :
  πφ • t = πψ • t :=
begin
  rw [smul_eq_iff_eq_inv_smul, smul_smul],
  symmetry,
  refine (designated_support t).supports _ _,
  intros c hc,
  rw [mul_smul, inv_smul_eq_iff],
  symmetry,
  rw smul_support_condition_eq φ hφ hφp hπφ t hφc h.φ_supports c c relation.refl_trans_gen.refl hc,
  rw smul_support_condition_eq ψ hψ hψp hπψ t hψc h.ψ_supports c c relation.refl_trans_gen.refl hc,
  obtain ⟨a | N, B⟩ := c,
  { simp only [support_condition_map_or_else, prod.mk.inj_iff, eq_self_iff_true, and_true],
    rw [(φ B).atom_map_or_else_of_dom, (ψ B).atom_map_or_else_of_dom],
    refine h.atom_map a B _,
    exact ⟨⟨_, hc, relation.refl_trans_gen.refl⟩, reduced.mk_atom _ _⟩, },
  { simp only [support_condition_map_or_else, prod.mk.inj_iff, eq_self_iff_true, and_true,
      near_litter_action.near_litter_map_or_else],
    refine set_like.coe_injective _,
    simp only [near_litter.coe_mk, subtype.coe_mk],
    congr' 1,
    { rw [(φ B).litter_map_or_else_of_dom, (ψ B).litter_map_or_else_of_dom, h.litter_map N.1 B _],
      exact ⟨⟨_, hc, refl_trans_gen_near_litter relation.refl_trans_gen.refl⟩,
        reduced.mk_litter _ _⟩, },
    { ext a : 1,
      rw [mem_image, mem_image],
      split;
      rintro ⟨b, hb₁, hb₂⟩;
      refine ⟨b, hb₁, _⟩;
      rw [← hb₂, (φ B).atom_map_or_else_of_dom, (ψ B).atom_map_or_else_of_dom],
      { refine (h.atom_map b B _).symm,
        exact ⟨⟨_, hc, relation.refl_trans_gen.single (constrains.symm_diff N b hb₁ B)⟩,
          reduced.mk_atom _ _⟩, },
      { refine h.atom_map b B _,
        exact ⟨⟨_, hc, relation.refl_trans_gen.single (constrains.symm_diff N b hb₁ B)⟩,
          reduced.mk_atom _ _⟩, }, }, },
end

instance {β : type_index} : partial_order (struct_action β) := {
  le := λ φ ψ, ∀ B, φ B ≤ ψ B,
  le_refl := λ φ B, le_rfl,
  le_trans := λ φ ψ χ h₁ h₂ B, (h₁ B).trans (h₂ B),
  le_antisymm := λ φ ψ h₁ h₂, funext (λ B, le_antisymm (h₁ B) (h₂ B)),
}

lemma lawful.le {β : type_index} {φ ψ : struct_action β} (h : φ.lawful) (hψ : ψ ≤ φ) : ψ.lawful :=
λ B, (h B).le (hψ B)

def comp {β γ : type_index} (φ : struct_action β) (A : path β γ) :
  struct_action γ :=
λ B, {
  atom_map := (φ (A.comp B)).atom_map,
  litter_map := (φ (A.comp B)).litter_map,
  atom_map_dom_small := begin
    refine small.image_subset id function.injective_id (φ (A.comp B)).atom_map_dom_small _,
    simp only [id.def, image_id'],
  end,
  litter_map_dom_small := begin
    refine small.image_subset id function.injective_id (φ (A.comp B)).litter_map_dom_small _,
    simp only [id.def, image_id'],
  end,
}

@[simp] lemma comp_apply {β γ : type_index}
  {φ : struct_action β} {A : path β γ} {B : extended_index γ} :
  φ.comp A B = φ (A.comp B) := by ext : 1; refl

lemma comp_comp {β γ δ : type_index}
  {φ : struct_action β} {A : path β γ} {B : path γ δ} :
  (φ.comp A).comp B = φ.comp (A.comp B) :=
begin
  ext : 2,
  simp only [comp_apply, path.comp_assoc],
  simp only [comp_apply, path.comp_assoc],
end

lemma le_comp {β γ : type_index} {φ ψ : struct_action β} (h : φ ≤ ψ) (A : path β γ) :
  φ.comp A ≤ ψ.comp A := λ B, h (A.comp B)

lemma lawful.comp {β γ : type_index} {φ : struct_action β} (h : φ.lawful) (A : path β γ) :
  lawful (φ.comp A) := λ B, {
  atom_map_injective := (h (A.comp B)).atom_map_injective,
  litter_map_injective := (h (A.comp B)).litter_map_injective,
  atom_mem := (h (A.comp B)).atom_mem,
}

end struct_action

end con_nf
