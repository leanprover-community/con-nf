import phase1.tangle
import phase3.ttt_model

/-!
# Our model of tangled type theory

We prove that our construction is indeed a model of tangled type theory, as defined in
`ttt_model.lean`. This completes the Con(NF) project.
-/

noncomputable theory

universe u

namespace con_nf

open set

variables [params.{u}] [typed_positions.{}]

class core_tangle_cumul' (α : Λ) := (data : Π β : Iic α, core_tangle_data β)

instance core_tangle_cumul'.to_core_tangle_data {α : Λ} [core_tangle_cumul' α] :
  Π β : Iic_index α, core_tangle_data β
| ⟨⊥, h⟩ := bot.core_tangle_data
| ⟨(β : Λ), hβ⟩ := core_tangle_cumul'.data ⟨β, with_bot.coe_le_coe.1 hβ⟩

instance core_tangle_cumul'.to_core_tangle_data' {α : Λ} [core_tangle_cumul' α] (β : Iic α) :
  core_tangle_data β :=
show core_tangle_data (Iic_coe β), by apply_instance

instance core_tangle_cumul'.to_core_tangle_data'' {α : Λ} [core_tangle_cumul' α] (β : Iic α) :
  core_tangle_data (β : Λ) :=
show core_tangle_data (Iic_coe β), by apply_instance

class positioned_tangle_cumul' (α : Λ) [core_tangle_cumul' α] := (data : Π β : Iic α, positioned_tangle_data β)

instance positioned_tangle_cumul'.to_positioned_tangle_data
  {α : Λ} [core_tangle_cumul' α] [positioned_tangle_cumul' α] :
  Π β : Iic_index α, positioned_tangle_data β
| ⟨⊥, h⟩ := bot.positioned_tangle_data
| ⟨(β : Λ), hβ⟩ := positioned_tangle_cumul'.data ⟨β, with_bot.coe_le_coe.1 hβ⟩

instance positioned_tangle_cumul'.to_positioned_tangle_data'
  {α : Λ} [core_tangle_cumul' α] [positioned_tangle_cumul' α] (β : Iic α) :
  positioned_tangle_data β :=
show positioned_tangle_data (Iic_coe β), by apply_instance

instance positioned_tangle_cumul'.to_positioned_tangle_data''
  {α : Λ} [core_tangle_cumul' α] [positioned_tangle_cumul' α] (β : Iic α) :
  positioned_tangle_data (β : Λ) :=
show positioned_tangle_data (Iic_coe β), by apply_instance

/-- The construction of the model of TTT up to a particular level `α : Λ`. These constructions will
then be put together to construct our full model of TTT.

This structure is subject to a lot of change as this part of the codebase matures. In particular,
we need to find a good way to equate the tangles accessed through different paths in the main
recursion. -/
structure ttt_model_segment (α : Λ) :=
[core_tangle_cumul' : core_tangle_cumul' α]
[positioned_tangle_cumul' : positioned_tangle_cumul' α]
[almost_tangle_cumul : Π β : Iic α, almost_tangle_data β]
[tangle_data_cumul : Π β : Iic α, tangle_data β]
(mem (β : Iio α) : tangle (β : Iic α) → tangle (⟨α, le_rfl⟩ : Iic α) → Prop)
(ext (β : Iio α) (t₁ t₂ : tangle (⟨α, le_rfl⟩ : Iic α)) :
  (∀ (s : tangle (β : Iic α)), mem β s t₁ ↔ mem β s t₂) → t₁ = t₂)
(structure_is_incomplete : false)

attribute [instance] ttt_model_segment.core_tangle_cumul'

/-- The main inductive step. -/
def model_segment_step (α : Λ) (h : Π β < α, ttt_model_segment β) : ttt_model_segment α := sorry

/-- We can construct a segment of our TTT model for any `α : Λ` using well-founded recursion. -/
noncomputable def main_recursion : Π (α : Λ), ttt_model_segment α
| α := model_segment_step α (λ β hβ, main_recursion β)
using_well_founded { dec_tac := `[assumption] }

/-- The endgame for the project. This definition asserts that we have a model of
tangled type theory. If this definition can be satisfied without any transitive sorries,
the Con(NF) project is complete. -/
def exists_ttt_model : ttt_model.{u} :=
begin
  refine_struct ({ Λ := Λ, Λ_preorder := infer_instance, .. } : ttt_model.{u}),
  { intro α,
    exact @tangle _ (⟨α, le_rfl⟩ : Iic_index α)
      (@core_tangle_cumul'.data _ _ _ (main_recursion α).core_tangle_cumul' ⟨α, le_rfl⟩) },
  all_goals { sorry }
end

end con_nf
