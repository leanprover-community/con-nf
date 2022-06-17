import litter
import type_index

open equiv equiv.perm with_bot

noncomputable theory

universe u

namespace con_nf
variable [params.{u}]

open params

/-- The motor of the recursion. -/
class recursion_motor (α : Λ) :=
(tangle : Π β < α, Type u)

variables (α : Λ) [recursion_motor.{u} α]

/-- The tangles already constructed at stage `α`. -/
def tangle : Π β < (α : type_index), Type u
| ⊥ h := atom
| ((β : Λ) : type_index) h := recursion_motor.tangle β $ coe_lt_coe.1 h

/-- A type-`β` code is a type index `γ < β` together with a set of tangles of type `γ`. -/
structure code (β : Λ) (β_le_α : β ≤ α) :=
(extension : type_index)
(extension_lt : extension < β)
(elts : set (tangle α extension (extension_lt.trans_le $ coe_le_coe.mpr β_le_α)))

/-- Suppose that the set of tangles embeds into the set of codes. -/
class recursion_motor_embedding :=
(tangle_embedding : Π (β < α), tangle _ β (coe_lt_coe.mpr ‹_›) ↪ code _ β (le_of_lt ‹_›))

open recursion_motor_embedding
variable [recursion_motor_embedding.{u} α]

def code.is_tangle {β < α} (c : code α β (le_of_lt ‹_›)) : Prop :=
∃ t : tangle α β (coe_lt_coe.2 ‹_›), c = tangle_embedding β ‹_› t

end con_nf
