import phase0.struct_perm

/-!
# Phase 1 of the recursion

This file contains the induction hypothesis for the first phase of the recursion. In this phase at
level `α`, we assume phase 1 at all levels `β < α`, but we do not assume any interaction between the
levels. Interaction will be introduced in phase 2.

## Main declarations

* `con_nf.phase_1`: The data for the first phase of the recursion.
-/

open with_bot

noncomputable theory

universe u

namespace con_nf
variable [params.{u}]

/-- The motor of the initial recursion. This contains all the information needed for phase 1 of the
recursion. Note that this is slightly different to the blueprint's formulation; here, we keep phase
1 data *cumulatively*, for all previous iterations of the recursion at once. -/
class phase_1 (α : Λ) :=
(tangle : Π β < α, Type u)
(to_tangle : Π β hβ, near_litter ↪ tangle β hβ)
(of_tangle : Π β hβ, tangle β hβ ↪ μ)
(allowable : Π β < α, Type u)
[allowable_group : Π β hβ, group (allowable β hβ)]
(allowable_to_struct_perm : Π β hβ, allowable β hβ →* struct_perm β)
[allowable_action : Π β hβ, mul_action (allowable β hβ) (tangle _ hβ)]
(smul_to_tangle : Π β hβ (π : allowable β hβ) N,
  π • to_tangle β hβ N = to_tangle β hβ (allowable_to_struct_perm _ _ π • N))
(pretangle_inj : Π β hβ, tangle β hβ ↪ pretangle β)
(smul_pretangle_inj : Π β hβ (π : allowable β hβ) (t : tangle β hβ),
  allowable_to_struct_perm β hβ π • pretangle_inj β hβ t = pretangle_inj β hβ (π • t))
(typed_singleton : Π β hβ, atom ↪ tangle β hβ)
(designated_support : Π β hβ (t : tangle β hβ), support (allowable_to_struct_perm β hβ) t)
(litter_lt : Π β hβ (L : litter) (a ∈ litter_set L),
  of_tangle _ hβ (to_tangle β hβ L.to_near_litter) < of_tangle _ hβ (typed_singleton β _ a))
(litter_lt_near_litter : Π β hβ (N : near_litter) (hN : litter_set N.fst ≠ N.snd),
  of_tangle β hβ (to_tangle β hβ N.fst.to_near_litter) < of_tangle β hβ (to_tangle β hβ N))
(symm_diff_lt_near_litter : Π β hβ (N : near_litter) (a ∈ litter_set N.fst ∆ N.snd),
  of_tangle _ hβ (typed_singleton β hβ a) < of_tangle _ hβ (to_tangle β hβ N))
(support_lt : Π β hβ (t : tangle β hβ) (c : support_condition β)
  (hc : c ∈ (designated_support β hβ t).to_potential_support),
  of_tangle _ hβ (c.fst.elim (typed_singleton β hβ) (to_tangle β hβ)) < of_tangle _ hβ t)

export phase_1 (to_tangle allowable allowable_group allowable_action smul_to_tangle
  pretangle_inj)

attribute [instance] allowable_group allowable_action

variables (α : Λ) [phase_1 α]

/-- The tangles already constructed at stage `α`. -/
def tangle : Π β < (α : type_index), Type u
| ⊥ h := atom
| ((β : Λ) : type_index) h := phase_1.tangle β $ coe_lt_coe.1 h

/-- For each type index less than `α`, there is an embedding from tangles at that level into `μ`. -/
@[irreducible] def of_tangle : Π {β : type_index} (h : β < α), tangle α β h ↪ μ
| ⊥ h := let equiv := (cardinal.eq.mp mk_atom).some in ⟨equiv.to_fun, equiv.injective⟩
| (some β) h := phase_1.of_tangle β (coe_lt_coe.mp h)

/-- Nonempty sets of tangles. -/
abbreviation tangles (γ : type_index) (hγ : γ < α) : Type u :=
{s : set (tangle α γ hγ) // s.nonempty}

end con_nf
