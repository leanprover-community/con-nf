import code
import f_map
import litter

open with_bot
open_locale cardinal

universe u

namespace con_nf
open params
variables [params.{u}] {α β : Λ} [phase_1a.{u} α]

/-- The *local cardinal* of a litter is the set of all near-litters to that litter. -/
@[reducible] def local_cardinal (i : litter) : set (Σ j, {s // is_near_litter j s}) :=
{s : (Σ j, {s // is_near_litter j s}) | s.1 = i}

lemma local_cardinal_disjoint : pairwise (disjoint on local_cardinal) :=
begin
  rintros i j h ⟨k, s, hs₁⟩ ⟨hs₂, hs₃⟩,
  exfalso, dsimp at hs₂ hs₃, rw [← hs₂, ← hs₃] at h, exact h rfl
end

/-- The *alternative extension* map. For a non-empty set of tangles `Γ`, consider the code
`(α, γ, Γ)`. We then construct the non-empty set `Δ` such that `(α, δ, Δ)` is an alternative
extension of the same object in TTT. -/
def A_map {γ δ : Λ} (hγ : γ < α) (hδ : δ < α) (hγδ : γ ≠ δ) :
{s : set (tangle α γ (coe_lt_coe.2 hγ)) // s.nonempty} →
{t : set (tangle α δ (coe_lt_coe.2 hδ)) // t.nonempty}
| ⟨G, hG⟩ := ⟨⋃ b ∈ G, to_tangle δ hδ '' local_cardinal (f_map γ δ hγ hδ b), begin
  simp,
  cases hG with t ht,
  exact ⟨t, ht, ⟨f_map γ δ hγ hδ t, litter_set _, is_near_litter_litter_set _⟩, by simp⟩,
end⟩

lemma exists_inter_of_Union_eq_Union {α β : Type*} {S T : set α} {f : α → set β}
(h : (⋃ b ∈ S, f b) = ⋃ c ∈ T, f c) : ∀ b ∈ S, (f b).nonempty → ∃ c ∈ T, (f b ∩ f c).nonempty :=
begin
  rintros b hb ⟨x, hx⟩,
  have : f b ⊆ ⋃ b ∈ S, f b := set.subset_Union₂ b hb, rw h at this,
  have := set.mem_of_mem_of_subset hx this, simp at this,
  obtain ⟨c, hc₁, hc₂⟩ := this, exact ⟨c, hc₁, x, hx, hc₂⟩
end

lemma A_map_injective_inner {γ δ : Λ} (hγ : γ < α) (hδ : δ < α) (hγδ : γ ≠ δ)
(s t : {s : set (tangle α γ (coe_lt_coe.2 hγ)) // s.nonempty})
(h : A_map hγ hδ hγδ s = A_map hγ hδ hγδ t) :
∀ x ∈ s.val, x ∈ t.val :=
begin
  cases s with G₁ hG₁, cases t with G₂ hG₂,
  intros g hg,
  unfold A_map at h,
  have := subtype.ext_iff_val.mp h, dsimp at this,
  obtain ⟨x, hx, y, hy₁, hy₂⟩ := exists_inter_of_Union_eq_Union this g hg
    ⟨to_tangle δ hδ $ ⟨f_map γ δ hγ hδ g, litter_set _, is_near_litter_litter_set _⟩, by simp⟩,
  rw set.mem_image at hy₁ hy₂,
  obtain ⟨s, hs₁, hs₂⟩ := hy₁, obtain ⟨t, ht₁, ht₂⟩ := hy₂,
  rw ← ht₂ at hs₂, have s_eq_t := (to_tangle δ hδ).inj' hs₂, rw s_eq_t at hs₁,
  suffices : g = x, by { rw ← this at hx, exact hx },
  by_contradiction,
  have := local_cardinal_disjoint (f_map γ δ hγ hδ g) (f_map γ δ hγ hδ x)
    ((f_map_injective γ δ hγ hδ).ne h),
  exact this ⟨hs₁, ht₁⟩,
end

lemma A_map_injective {γ δ : Λ} (hγ : γ < α) (hδ : δ < α) (hγδ : γ ≠ δ) :
function.injective (A_map hγ hδ hγδ) :=
begin
  rintros s t h,
  ext, dsimp, split,
  exact A_map_injective_inner hγ hδ hγδ s t h x,
  exact A_map_injective_inner hγ hδ hγδ t s h.symm x
end

end con_nf
