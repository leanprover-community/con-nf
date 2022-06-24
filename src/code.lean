import litter
import type_index

open equiv equiv.perm with_bot

noncomputable theory

universe u

namespace con_nf
variable [params.{u}]

open params

/-- The motor of the initial recursion. This contains all the information needed for phase 1a of the
recursion. Note that this is slightly different to the blueprint's formulation; here, we keep phase
1a data *cumulatively*, for all previous iterations of the recursion at once. -/
class phase_1a (α : Λ) :=
(tangle : Π β < α, Type u)
(to_tangle : Π β (h : β < α), (Σ i, {s // is_near_litter i s}) ↪ tangle β h)
(of_tangle : Π β (h : β < α), tangle β h ↪ μ)

export phase_1a (of_tangle to_tangle)

variables (α : Λ) [phase_1a.{u} α]

/-- The tangles already constructed at stage `α`. -/
def tangle : Π β < (α : type_index), Type u
| ⊥ h := atom
| ((β : Λ) : type_index) h := phase_1a.tangle β $ coe_lt_coe.1 h

/-- A type-`β` code is a type index `γ < β` together with a set of tangles of type `γ`. -/
structure code (β : Λ) (β_lt_α : β < α) :=
(extension : type_index)
(extension_lt : extension < β)
(elts : set (tangle α extension (extension_lt.trans $ coe_lt_coe.mpr β_lt_α)))

/-- Suppose that the set of tangles embeds into the set of codes. -/
class phase_1a_embedding :=
(tangle_embedding : Π (β < α), tangle _ β (coe_lt_coe.mpr ‹_›) ↪ code _ β ‹_›)

open phase_1a_embedding
variable [phase_1a_embedding.{u} α]

def code.is_tangle {β < α} (c : code α β ‹_›) : Prop :=
∃ t : tangle α β (coe_lt_coe.2 ‹_›), c = tangle_embedding β ‹_› t

end con_nf
