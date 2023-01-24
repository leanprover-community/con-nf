import phase2.approximation

open set
open_locale cardinal classical

universe u

namespace con_nf
variables [params.{u}] {α : Λ} [core_tangle_cumul α] [positioned_tangle_cumul α]
  [position_data.{}] [almost_tangle_cumul α]

namespace near_litter_approx

variables (α) {β : type_index} (π : near_litter_approx) (A : extended_index β)

def id_on_flexible : local_perm litter := {
  to_fun := id,
  inv_fun := id,
  domain := {L | flexible α L A} \ π.litter_perm.domain,
  to_fun_domain' := λ L h, h,
  inv_fun_domain' := λ L h, h,
  left_inv' := λ L h, rfl,
  right_inv' := λ L h, rfl,
}

lemma id_on_flexible_domain :
  (id_on_flexible α π A).domain = {L | flexible α L A} \ π.litter_perm.domain := rfl

lemma id_on_flexible_domain_disjoint :
  disjoint π.litter_perm.domain (id_on_flexible α π A).domain :=
by rw [disjoint_iff_inter_eq_empty, id_on_flexible_domain, inter_diff_self]

noncomputable def flexible_completion_litter_perm : local_perm litter :=
local_perm.piecewise π.litter_perm (id_on_flexible α π A) (id_on_flexible_domain_disjoint α π A)

lemma flexible_completion_litter_perm_domain :
  (flexible_completion_litter_perm α π A).domain = π.litter_perm.domain ∪ {L | flexible α L A} :=
by rw [flexible_completion_litter_perm, local_perm.piecewise_domain,
  id_on_flexible_domain, union_diff_self]

noncomputable def flexible_completion : near_litter_approx := {
  atom_perm := π.atom_perm,
  litter_perm := flexible_completion_litter_perm α π A,
  domain_small := π.domain_small,
}

end near_litter_approx

end con_nf
