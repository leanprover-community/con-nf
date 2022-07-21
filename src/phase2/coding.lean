import phase2.strong_support

universe u

namespace con_nf

variables [params.{u}] {α : Λ} [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [phase_2_assumptions α] (B : le_index α)

inductive label (S : word_support B)
| flexible_litter : label
| atom : Π (L : S.carrier) (A : extended_index B), label
-- ...

/-- An *`S`-labelling* is a function which assigns a label to each element of `S`. -/
def word_support.labelling (S : word_support B) := Π (c : S.carrier), label B S

end con_nf
