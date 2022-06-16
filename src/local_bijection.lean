import extended_index
import litter
import params

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
(bij (A) : domain A → domain A)
(inj (A) : function.injective (bij A))
(litter_inter (A) (i : litter) : small $ domain A ∩ litter_set i)

instance local_bijection_coe (α : Λ) :
has_coe_to_fun (local_bijection α) (λ π₀, Π A, π₀.domain A → π₀.domain A) :=
⟨λ π₀, π₀.bij⟩

end con_nf
