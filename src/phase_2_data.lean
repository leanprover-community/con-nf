import tangle

open set with_bot
open_locale pointwise

noncomputable theory

universe u

namespace con_nf
variable [params.{u}]

variables (α : Λ) [phase_1a.{u} α] [phase_1b.{u} α] [phase_1b_coherence.{u} α]

class phase_1c :=
(pretangle_inj : Π (β : Λ) hβ, tangle α β hβ ↪ pretangle β)
(pretangle_inj_comm : Π (β : Λ) hβ (t : tangle α β $ coe_lt_coe.2 hβ) (π : allowable β hβ),
  pretangle_inj β (coe_lt_coe.2 hβ) (π • t) =
    (to_struct_perm β hβ π) • (pretangle_inj β (coe_lt_coe.2 hβ) t))

export phase_1c (pretangle_inj pretangle_inj_comm)

variable [phase_1c.{u} α]

namespace nonempty_semitangle

def to_pretangle (t : nonempty_semitangle α) : pretangle α :=
pretangle.mk t.pref.atoms (λ β hβ, pretangle_inj β (coe_lt_coe.mpr hβ) ''
  (t.exts β hβ : set (tangle α β $ coe_lt_coe.mpr hβ)))

lemma to_pretangle_ne_empty (t : nonempty_semitangle α) :
  to_pretangle α t ≠ pretangle.mk ∅ (λ β hβ, ∅) :=
begin
  by_cases hzero : ∃ β, β < α,
  { obtain ⟨β, hβ⟩ := hzero,
    intro h,
    have := congr_arg pretangle.extension h,
    rw pretangle.extension_mk at this,
    have := congr_fun₂ this β hβ,
    rw [to_pretangle, pretangle.extension_mk, set.image_eq_empty] at this,
    exact (t.exts β hβ).property.ne_empty this },
  { intro h,
    have := congr_arg pretangle.atom_extension h,
    rw [to_pretangle, pretangle.atom_extension_mk, pretangle.atom_extension_mk] at this,
    obtain ⟨ts, ⟨atoms, hne, rep, hA⟩ | ⟨β, hβ, rep, hA⟩⟩ := t,
    { exact hne.ne_empty this },
    { exfalso, exact hzero ⟨β, hβ⟩ } }
end

lemma to_pretangle_injective : injective (to_pretangle α) :=
begin
  intros s t hst, unfold to_pretangle at hst,
  by_cases h : ∃ β, β < α,
  { obtain ⟨β, hβ⟩ := h,
    have := congr_arg pretangle.extension hst,
    rw [pretangle.extension_mk, pretangle.extension_mk] at this,
    have := congr_fun₂ this β hβ,
    rw set.image_eq_image (embedding.injective _) at this,
    exact ext _ _ _ (subtype.coe_inj.mp this) },
  { have := congr_arg pretangle.atom_extension hst,
    rw [pretangle.atom_extension_mk, pretangle.atom_extension_mk] at this,
    exact ext_zero _ _ h this }
end

end nonempty_semitangle

namespace semitangle

def to_pretangle : semitangle α → pretangle α
| ⊥ := pretangle.mk ∅ (λ β hβ, ∅)
| (t : nonempty_semitangle α) := nonempty_semitangle.to_pretangle α t

lemma to_pretangle_injective : injective (to_pretangle α) :=
begin
  intros s t hst,
  induction s using with_bot.rec_bot_coe; induction t using with_bot.rec_bot_coe,
  { refl },
  { exfalso, rw [to_pretangle, to_pretangle] at hst,
    exact nonempty_semitangle.to_pretangle_ne_empty _ _ hst.symm },
  { exfalso, rw [to_pretangle, to_pretangle] at hst,
    exact nonempty_semitangle.to_pretangle_ne_empty _ _ hst },
  { rw nonempty_semitangle.to_pretangle_injective α hst }
end

end semitangle

namespace new_tangle

def to_pretangle (t : new_tangle α) : pretangle α := semitangle.to_pretangle α t

lemma to_pretangle_injective : injective (to_pretangle α) :=
λ s t hst, subtype.coe_inj.mp (semitangle.to_pretangle_injective α hst)

end new_tangle

class phase_1 :=
(typed_singleton (β : Λ) (hβ) : atom ↪ tangle α β hβ)
(designated_support (β : Λ) (hβ : β < α) (t : tangle α β $ coe_lt_coe.mpr hβ) :
  support (to_struct_perm β hβ) t)
(litter_lt (β : Λ) hβ (L : litter) (a ∈ litter_set L) :
  of_tangle _ hβ (to_tangle β (coe_lt_coe.mp hβ) L.to_near_litter) <
    of_tangle _ hβ (typed_singleton β _ a))
(litter_lt_near_litter (β : Λ) hβ (N : near_litter) (hN : litter_set N.fst ≠ N.snd) :
  of_tangle α hβ (to_tangle β (coe_lt_coe.mp hβ) N.fst.to_near_litter) <
    of_tangle _ hβ (to_tangle β (coe_lt_coe.mp hβ) N))
(symm_diff_lt_near_litter (β : Λ) hβ (N : near_litter) (a ∈ litter_set N.fst ∆ N.snd) :
  of_tangle _ hβ (typed_singleton β hβ a) < of_tangle _ hβ (to_tangle β (coe_lt_coe.mp hβ) N))
(support_lt (β : Λ) hβ (t : tangle α β hβ) (c : support_condition β)
  (hc : c ∈ (designated_support β (coe_lt_coe.mp hβ) t).to_potential_support) :
  of_tangle _ hβ (c.fst.elim (typed_singleton β hβ) (to_tangle β $ coe_lt_coe.mp hβ)) <
    of_tangle _ hβ t)

end con_nf
