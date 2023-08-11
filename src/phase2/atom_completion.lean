import phase2.approximation

open set sum
open_locale classical

universe u

namespace con_nf
variables [params.{u}] {α : Λ} [position_data.{}] [phase_2_assumptions α] {β : Iic α}
  (π : struct_approx β)

namespace struct_approx

open near_litter_approx hypothesis

lemma order_iso_apply_mem {S T : sublitter} {a} {L : litter}
  (h : (S.order_iso T a : atom) ∈ litter_set L) : T.litter = L :=
begin
  rw [← litter.litter_to_sublitter L, ← sublitter.inter_nonempty_iff],
  exact ⟨_, (S.order_iso T a).prop, h⟩,
end

lemma order_iso_apply_eq {S T U V : sublitter} {a b}
  (h : (S.order_iso T a : atom) = U.order_iso V b) :
  T.litter = V.litter :=
begin
  rw subtype.coe_eq_iff at h,
  exact (order_iso_apply_mem (T.subset h.some)).symm,
end

/-- Computes the action of a structural approximation `π` on an atom `a`. -/
noncomputable def atom_completion (A : extended_index β) (a : atom)
  (H : hypothesis ⟨inl a, A⟩) : atom :=
if h : a ∈ (π A).atom_perm.domain then π A • a else
((π A).largest_sublitter a.1).order_iso
  ((π A).largest_sublitter (H.near_litter_image A a.1.to_near_litter
    (relation.trans_gen.single $ constrains.atom a A)).1)
  ⟨a, (π A).mem_largest_sublitter_of_not_mem_domain a h⟩

end struct_approx

end con_nf
