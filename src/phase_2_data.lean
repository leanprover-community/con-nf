import tangle

noncomputable theory

universe u

namespace con_nf
variable [params.{u}]

open function params set with_bot
open_locale pointwise

variables (α : Λ) [phase_1a.{u} α] [phase_1b.{u} α] [phase_1b_coherence.{u} α]

class phase_1c :=
(pretangle_inj : Π (β : Λ) hβ, tangle α β hβ ↪ pretangle β)
(pretangle_inj_comm : Π (β : Λ) hβ (t : tangle α β $ coe_lt_coe.2 hβ) (π : allowable β hβ),
  pretangle_inj β (coe_lt_coe.2 hβ) (π • t) =
    (to_struct_perm β hβ π) • (pretangle_inj β (coe_lt_coe.2 hβ) t))

variable [phase_1c.{u} α]

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
