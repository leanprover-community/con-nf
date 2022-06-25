import code
import f_map
import litter

open with_bot
open_locale cardinal

universe u

namespace con_nf
open params
variables [params.{u}] {α β : Λ} [phase_1a.{u} α]

def local_cardinal (i : litter) : set (Σ j, {s // is_near_litter j s}) := {s : (Σ j, {s // is_near_litter j s}) | s.1 = i}

def A_map {γ δ : Λ} (hγ : γ < α) (hδ : δ < α) (hγδ : γ ≠ δ) :
    {s : set (tangle α γ (coe_lt_coe.2 hγ)) // s.nonempty} → {t : set (tangle α δ (coe_lt_coe.2 hδ)) // t.nonempty}
| c := ⟨⋃ (b ∈ c.1), to_tangle δ hδ '' (local_cardinal (f_map γ δ hγ hδ b)), begin
  simp,
  cases c.2 with t ht,
  refine ⟨t, ⟨ht, _⟩⟩,
  unfold set.nonempty local_cardinal,
  set i := f_map γ δ hγ hδ t,
  use ⟨i, ⟨litter_set i, is_near_litter_litter_set i⟩⟩,
  simp,
end⟩

lemma A_map_injective {γ δ : Λ} (hγ : γ < α) (hδ : δ < α) (hγδ : γ ≠ δ) : function.injective (A_map hγ hδ hγδ) := sorry

end con_nf
