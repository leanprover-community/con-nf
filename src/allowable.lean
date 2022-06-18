import code
import struct_perm

/-!
# Allowable permutations
-/

universe u

namespace con_nf
variable [params.{u}]

open params with_bot

variables (α : Λ) [phase_1a.{u} α]

/-- Contains all the information needed for phase 1b of the recursion.
We use an explicit `→*` here instead of a `monoid_hom_class` so that we don't need to worry
about typeclass instances not firing under a `β < α` condition. -/
class phase_1b :=
(allowable : Π β < α, Type*) [allowable_group : Π β (h : β < α), group (allowable β h)]
(to_structural : Π β (h : β < α), allowable β h →* struct_perm α)
[allowable_action : Π β (h : β < α), mul_action (allowable β h) (tangle α β (coe_lt_coe.mpr h))]

export phase_1b (allowable allowable_group to_structural allowable_action)

variables [phase_1b.{u} α]

instance allowable_group_pi : group (Π β (h : β < α), allowable β h) := sorry

/-- A semiallowable permutation is a `-1`-allowable permutation of atoms (a near-litter permutation)
together with allowable permutations on all `β < α`. This forms a group structure automatically. -/
def semiallowable_perm := near_litter_perm × Π β (h : β < α), allowable β h

instance semiallowable_perm_group : group (semiallowable_perm α) := prod.group

instance semiallowable_perm_scalar {β : Λ} {h : β ≤ α} :
has_scalar (semiallowable_perm α) (code α β h) :=
⟨λ π ⟨γ, hγ, G⟩, begin
  refine ⟨γ, hγ, _⟩,
  cases γ,
  { exact π.fst.atom_perm '' G },
  { rw with_bot.some_eq_coe at hγ, simp at hγ,
    haveI := allowable_action γ (lt_of_lt_of_le hγ h),
    simp_rw with_bot.some_eq_coe,
    exact (λ g, (π.snd γ (lt_of_lt_of_le hγ h)) • g) '' G }
end⟩

-- TODO(zeramorphic)
instance semiallowable_perm_action {β : Λ} {h : β ≤ α} :
mul_action (semiallowable_perm α) (code α β h) := sorry

end con_nf
