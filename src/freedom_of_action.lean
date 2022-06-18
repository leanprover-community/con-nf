import type_index
import litter

/-!
# The freedom of action theorem
-/

open function

universe u

namespace con_nf
variables [params.{u}]

open params

/-- An α-local bijection associates to each extended type index `A` a domain of atoms,
and defines an injection from that domain to itself.
It must satisfy two conditions, that the map is really an injection, and that the
intersection of the domain with any litter is small. -/
structure local_bijection (α : Λ) :=
(domain (A : extended_index α) : set atom)
(to_fun (A) : equiv.perm (domain A))
(litter_inter (A) (i : litter) : small $ domain A ∩ litter_set i)

instance (α : Λ) : has_coe_to_fun (local_bijection α) (λ π₀, Π A, π₀.domain A → π₀.domain A) :=
⟨λ π₀ A, (π₀.to_fun A).to_fun⟩

/-- `a` is an exception of the near-litter permutation `f` if it is not sent to the corresponding
litter under either `f` or `f⁻¹`. -/
def near_litter_perm.exception (f : near_litter_perm) (a : atom) : Prop :=
f.atom_perm a ∉ litter_set (f.litter_perm a.1) ∨ f.atom_perm⁻¹ a ∉ litter_set (f.litter_perm⁻¹ a.1)

end con_nf
