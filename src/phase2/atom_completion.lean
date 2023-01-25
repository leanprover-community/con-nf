import phase2.approximation

open set sum
open_locale classical

universe u

namespace con_nf
variables [params.{u}] {α : Λ} [core_tangle_cumul α] [positioned_tangle_cumul α]
  [position_data.{}] [almost_tangle_cumul α] [tangle_cumul α] {β : Iio α} (π : struct_approx β)

namespace struct_approx

open near_litter_approx hypothesis

/-- An arbitrary equivalence between sublitters. -/
@[irreducible] noncomputable def sublitter_bijection (S T : sublitter) : S ≃ T :=
(cardinal.eq.mp $ S.mk_eq_κ.trans T.mk_eq_κ.symm).some

lemma sublitter_bijection_apply_mem {S T : sublitter} {a} {L : litter}
  (h : (sublitter_bijection S T a : atom) ∈ litter_set L) : T.litter = L :=
begin
  rw [← litter.litter_to_sublitter L, ← sublitter.inter_nonempty_iff],
  exact ⟨_, (sublitter_bijection S T a).prop, h⟩,
end

lemma sublitter_bijection_apply_eq {S T U V : sublitter} {a b}
  (h : (sublitter_bijection S T a : atom) = sublitter_bijection U V b) :
  T.litter = V.litter :=
begin
  rw subtype.coe_eq_iff at h,
  exact (sublitter_bijection_apply_mem (T.subset h.some)).symm,
end

/-- Computes the action of a structural approximation `π` on an atom `a`. -/
noncomputable def atom_completion (a : atom) (A : extended_index β)
  (H : hypothesis ⟨inl a, A⟩) : atom :=
if h : a ∈ (π A).atom_perm.domain then π A • a else
sublitter_bijection
  ((π A).largest_sublitter a.1)
  ((π A).largest_sublitter (H.near_litter_image a.1.to_near_litter A
    (relation.trans_gen.single $ constrains.atom a A)).1)
  ⟨a, (π A).mem_largest_sublitter_of_not_mem_domain a h⟩

lemma atom_completion_compatible {a} {A : extended_index β} {H₁ H₂} (h : compatible H₁ H₂) :
  π.atom_completion a A H₁ = π.atom_completion a A H₂ :=
begin
  unfold atom_completion,
  split_ifs with ha,
  refl,
  rw h.near_litter_compatible a.1.to_near_litter A (relation.trans_gen.single $ constrains.atom a A)
    (relation.trans_gen.single $ constrains.atom a A),
end

end struct_approx

end con_nf
