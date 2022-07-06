import phase0.litter
import phase0.struct_perm

/-!
# Phase 1 of the recursion

This file contains the induction hypothesis for the first phase of the recursion. In this phase at
level `α`, we assume phase 1 at all levels `β < α`, but we do not assume any interaction between the
levels. Interaction will be introduced in phase 2.

## Main declarations

* `conf_`
-/

open equiv equiv.perm with_bot

noncomputable theory

universe u

namespace con_nf
variable [params.{u}]

/-- The motor of the initial recursion. This contains all the information needed for phase 1a of the
recursion. Note that this is slightly different to the blueprint's formulation; here, we keep phase
1a data *cumulatively*, for all previous iterations of the recursion at once. -/
class phase_1a (α : Λ) :=
(tangle : Π β < α, Type u)
(to_tangle : Π β hβ, near_litter ↪ tangle β hβ)
(of_tangle : Π β hβ, tangle β hβ ↪ μ)

export phase_1a (to_tangle)

variables (α : Λ) [phase_1a α] {β : Λ} {hβ : β ≤ α}

/-- The tangles already constructed at stage `α`. -/
def tangle : Π β < (α : type_index), Type u
| ⊥ h := atom
| ((β : Λ) : type_index) h := phase_1a.tangle β $ coe_lt_coe.1 h

/-- For each type index less than `α`, there is an embedding from tangles at that level into `μ`. -/
@[irreducible] def of_tangle : Π {β : type_index} (h : β < α), tangle α β h ↪ μ
| ⊥ h := let equiv := (cardinal.eq.mp mk_atom).some in ⟨equiv.to_fun, equiv.injective⟩
| (some β) h := phase_1a.of_tangle β (coe_lt_coe.mp h)

/-- Nonempty sets of tangles. -/
abbreviation tangles (γ : type_index) (hγ : γ < α) : Type u :=
{s : set (tangle α γ hγ) // s.nonempty}

/-- Contains all the information needed for phase 1b of the recursion. -/
class phase_1b :=
(allowable : Π β < α, Type u)
[allowable_group : Π β hβ, group (allowable β hβ)]
(to_struct_perm : Π β hβ, allowable β hβ →* struct_perm β)
[allowable_action : Π β hβ, mul_action (allowable β hβ) (tangle α β $ coe_lt_coe.2 hβ)]

export phase_1b (allowable allowable_group to_struct_perm allowable_action)

attribute [instance] allowable_group allowable_action

end con_nf
