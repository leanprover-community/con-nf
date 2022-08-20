import phase2.strong_support

open quiver

universe u

namespace con_nf

variables [params.{u}] {α : Λ} [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [typed_positions.{}] [phase_2_assumptions α] (B : le_index α)

-- TODO: This is an incomplete definition - I'm (zeramorphic) not sure exactly what the parameters
-- to these intro rules should be.
inductive label (S : word_support B)
| atom (L : S.carrier) (A : extended_index B) : label
| near_litter : label
| flex_litter : label
| non_flex_litter ⦃β δ : Λ⦄ ⦃γ : type_index⦄
  (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
  (C : path (α : type_index) β) (t : tangle_path ((lt_index.mk' hγ C) : le_index α)) : label

/-- An *`S`-labelling* is a function which assigns a label to each element of `S`. -/
def word_support.labelling (S : word_support B) := Π (c : S.carrier), label B S

end con_nf
