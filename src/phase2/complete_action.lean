import phase2.near_litter_completion

open function set
open_locale classical

universe u

namespace con_nf

namespace struct_approx
variables [params.{u}] {α : Λ} [position_data.{}] [phase_2_assumptions α]
  {β : Iic α} [freedom_of_action_hypothesis β]

/-!
We now construct the completed action of a structural approximation using well-founded recursion
on support conditions. It remains to prove that this map yields an allowable permutation.
TODO: Rename `complete_atom_map`, `atom_completion` etc.
TODO: Swap argument order for things that take an atom/near-litter and an extended index.
-/

noncomputable def complete_atom_map (π : struct_approx β) :
  atom → extended_index β → atom :=
hypothesis.fix_atom π.atom_completion π.near_litter_completion

noncomputable def complete_near_litter_map (π : struct_approx β) :
  near_litter → extended_index β → near_litter :=
hypothesis.fix_near_litter π.atom_completion π.near_litter_completion

noncomputable def complete_litter_map (π : struct_approx β) (L : litter) (A : extended_index β) :
  litter :=
(π.complete_near_litter_map L.to_near_litter A).1

variables {π : struct_approx β} {a : atom} {L : litter} {N : near_litter} {A : extended_index β}

lemma complete_atom_map_eq :
  π.complete_atom_map a A = π.atom_completion a A
    ⟨λ b B hb, π.complete_atom_map b B, λ N B hb, π.complete_near_litter_map N B⟩ :=
hypothesis.fix_atom_eq _ _ _ _

lemma complete_near_litter_map_eq :
  π.complete_near_litter_map N A = π.near_litter_completion N A
    ⟨λ b B hb, π.complete_atom_map b B, λ N B hb, π.complete_near_litter_map N B⟩ :=
hypothesis.fix_near_litter_eq _ _ _ _

lemma complete_litter_map_eq :
  π.complete_litter_map L A = (π.complete_near_litter_map L.to_near_litter A).1 := rfl

/-!
# Atom map properties
We show that the completed map is a permutation of atoms.
-/

lemma complete_atom_map_eq_of_mem_domain (h : a ∈ (π A).atom_perm.domain) :
  π.complete_atom_map a A = π A • a :=
by rw [complete_atom_map_eq, atom_completion, dif_pos h]

lemma complete_atom_map_eq_of_not_mem_domain (h : a ∉ (π A).atom_perm.domain) :
  π.complete_atom_map a A = sublitter_bijection
    ((π A).largest_sublitter a.1)
    ((π A).largest_sublitter (π.complete_litter_map a.1 A))
    ⟨a, (π A).mem_largest_sublitter_of_not_mem_domain a h⟩ :=
by rw [complete_atom_map_eq, atom_completion, dif_neg h]; refl

-- TODO: We can't even prove basic facts like injectivity without lots of well-founded recursion.
lemma complete_atom_map_injective : injective (λ a, π.complete_atom_map a A) :=
begin
  intros a b h,
  dsimp only at h,
  by_cases ha : a ∈ (π A).atom_perm.domain;
  by_cases hb : b ∈ (π A).atom_perm.domain,
  { rw [complete_atom_map_eq_of_mem_domain ha, complete_atom_map_eq_of_mem_domain hb] at h,
    exact (π A).atom_perm.inj_on ha hb h, },
  { rw [complete_atom_map_eq_of_mem_domain ha, complete_atom_map_eq_of_not_mem_domain hb] at h,
    cases (π A).not_mem_domain_of_mem_largest_sublitter ((subtype.coe_eq_iff.mp h.symm).some)
      ((π A).atom_perm.map_domain ha), },
  { rw [complete_atom_map_eq_of_not_mem_domain ha, complete_atom_map_eq_of_mem_domain hb] at h,
    cases (π A).not_mem_domain_of_mem_largest_sublitter ((subtype.coe_eq_iff.mp h).some)
      ((π A).atom_perm.map_domain hb), },
  { rw [complete_atom_map_eq_of_not_mem_domain ha, complete_atom_map_eq_of_not_mem_domain hb] at h,
    have h₁ := (subtype.coe_eq_iff.mp h).some.1,
    have h₂ := (sublitter_bijection
      ((π A).largest_sublitter b.1)
      ((π A).largest_sublitter (π.complete_litter_map b.1 A))
      ⟨b, (π A).mem_largest_sublitter_of_not_mem_domain b hb⟩).prop.1,
    have := h₁.symm.trans h₂,
    sorry, },
end

end struct_approx

end con_nf
