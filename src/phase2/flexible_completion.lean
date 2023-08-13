import phase2.approximation

open set
open_locale classical

universe u

namespace con_nf
variables [params.{u}] (α : Λ) [position_data.{}] [phase_2_assumptions α] {β : type_index}
  (π : near_litter_approx) (A : extended_index β)

namespace near_litter_approx

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

lemma flexible_completion_litter_perm_domain' :
  (flexible_completion_litter_perm α π A).domain = π.litter_perm.domain ∪ {L | flexible α L A} :=
by rw [flexible_completion_litter_perm, local_perm.piecewise_domain,
  id_on_flexible_domain, union_diff_self]

noncomputable def flexible_completion : near_litter_approx := {
  atom_perm := π.atom_perm,
  litter_perm := flexible_completion_litter_perm α π A,
  domain_small := π.domain_small,
}

lemma flexible_completion_litter_perm_domain :
  (flexible_completion α π A).litter_perm.domain = π.litter_perm.domain ∪ {L | flexible α L A} :=
by rw [flexible_completion, flexible_completion_litter_perm_domain']

lemma flexible_completion_litter_perm_domain_free (hπ : π.free α A) :
  (flexible_completion α π A).litter_perm.domain = {L | flexible α L A} :=
begin
  rw [flexible_completion_litter_perm_domain, union_eq_right_iff_subset],
  exact λ L hL, hπ L hL,
end

lemma flexible_completion_smul_eq (L : litter) :
  flexible_completion α π A • L = flexible_completion_litter_perm α π A L := rfl

lemma flexible_completion_smul_of_mem_domain (L : litter) (hL : L ∈ π.litter_perm.domain) :
  flexible_completion α π A • L = π.litter_perm L :=
begin
  rw [flexible_completion_smul_eq, flexible_completion_litter_perm,
    local_perm.piecewise_apply_eq_left hL],
end

lemma flexible_completion_smul_flexible (hπ : π.free α A) (L : litter) (hL : flexible α L A) :
  flexible α (flexible_completion α π A • L) A :=
begin
  have := local_perm.map_domain (flexible_completion α π A).litter_perm,
  rw flexible_completion_litter_perm_domain_free α π A hπ at this,
  exact this hL,
end

lemma flexible_completion_symm_smul_flexible (hπ : π.free α A) (L : litter) (hL : flexible α L A) :
  flexible α ((flexible_completion α π A).symm • L) A :=
begin
  have := local_perm.map_domain (flexible_completion α π A).symm.litter_perm,
  rw [symm_litter_perm, local_perm.symm_domain,
    flexible_completion_litter_perm_domain_free α π A hπ] at this,
  exact this hL,
end

end near_litter_approx

end con_nf
