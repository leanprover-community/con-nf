import code
import f_map
import litter

open with_bot
open_locale cardinal

universe u

namespace con_nf
open params
variables [params.{u}] {α : Λ} [phase_1a.{u} α]

/-- The *local cardinal* of a litter is the set of all near-litters to that litter. -/
@[reducible] def local_cardinal (i : litter) : set (Σ j, {s // is_near_litter j s}) :=
{s : (Σ j, {s // is_near_litter j s}) | s.1 = i}

lemma local_cardinal_nonempty (i : litter) : (local_cardinal i).nonempty :=
⟨⟨i, litter_set _, is_near_litter_litter_set _⟩, by simp⟩

lemma local_cardinal_disjoint : pairwise (disjoint on local_cardinal) :=
begin
  rintros i j h ⟨k, s, hs₁⟩ ⟨hs₂, hs₃⟩,
  exfalso, dsimp at hs₂ hs₃, rw [← hs₂, ← hs₃] at h, exact h rfl
end

/-- The *alternative extension* map. For a non-empty set of tangles `Γ`, consider the code
`(α, γ, Γ)`. We then construct the non-empty set `Δ` such that `(α, δ, Δ)` is an alternative
extension of the same object in TTT. -/
def A_map {γ : type_index} {δ : Λ} (hγ : γ < α) (hδ : δ < α) (hγδ : γ ≠ δ)
(c : {s : set (tangle α γ hγ) // s.nonempty}) :
{t : set (tangle α δ (coe_lt_coe.2 hδ)) // t.nonempty} :=
⟨⋃ b ∈ c.val, to_tangle δ hδ '' local_cardinal (f_map γ δ hγ hδ b), begin
  simp,
  cases c.property with t ht,
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

lemma A_map_injective_inner {γ : type_index} {δ : Λ} (hγ : γ < α) (hδ : δ < α) (hγδ : γ ≠ δ)
(s t : {s : set (tangle α γ hγ) // s.nonempty}) (h : A_map hγ hδ hγδ s = A_map hγ hδ hγδ t) :
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

lemma A_map_injective {γ : type_index} {δ : Λ} (hγ : γ < α) (hδ : δ < α) (hγδ : γ ≠ δ) :
function.injective (A_map hγ hδ hγδ) :=
begin
  rintros s t h,
  ext, dsimp, split,
  exact A_map_injective_inner hγ hδ hγδ s t h x,
  exact A_map_injective_inner hγ hδ hγδ t s h.symm x
end

/-!
We don't need to prove that the ranges of the `A_δ` are disjoint for different `δ`, since this holds
at the type level.

We now show that there are only finitely many iterated images under any inverse A-map.
-/

lemma well_founded_of_tangle {β : type_index} (h : β < α) :
  well_founded (λ a b, of_tangle α h a < of_tangle α h b) :=
well_founded.inv_image _ is_well_order.wf

noncomputable def min_tangle {γ : type_index} (hγ : γ < α)
(c : {s : set (tangle α γ hγ) // s.nonempty}) : tangle α γ hγ :=
well_founded.min (well_founded_of_tangle hγ) c.val c.property

lemma min_tangle_mem {γ : type_index} (hγ : γ < α) (c : {s : set (tangle α γ hγ) // s.nonempty}) :
min_tangle hγ c ∈ c.val :=
well_founded.min_mem (well_founded_of_tangle hγ) c.val c.property

lemma min_tangle_le {γ : type_index} (hγ : γ < α) (c : {s : set (tangle α γ hγ) // s.nonempty}) :
∀ x ∈ c.val, ¬ of_tangle α hγ x < (of_tangle α hγ $ min_tangle hγ c) :=
λ x hx, well_founded.not_lt_min (well_founded_of_tangle hγ) c.val c.property hx

lemma A_map_order {γ : type_index} {δ : Λ} (hγ : γ < α) (hδ : δ < α) (hγδ : γ ≠ δ)
(c : {s : set (tangle α γ hγ) // s.nonempty}) :
(of_tangle α hγ $ min_tangle hγ c) <
(of_tangle α (coe_lt_coe.mpr hδ) $ min_tangle (coe_lt_coe.mpr hδ) (A_map hγ hδ hγδ c)) :=
begin
  obtain ⟨s, ⟨t, ht⟩, hs⟩ := min_tangle_mem (coe_lt_coe.mpr hδ) (A_map hγ hδ hγδ c),
  rw ← ht at hs, clear ht,
  rw set.mem_Union at hs, obtain ⟨ht, hs⟩ := hs, rw set.mem_image at hs, obtain ⟨N, hN₁, hN₂⟩ := hs,
  rw ← hN₂, clear hN₂,
  have : is_near_litter (f_map γ δ hγ hδ t) N.snd.val,
  { convert N.snd.property, exact hN₁.symm },
  convert lt_of_le_of_lt _ (f_map_position_raising γ δ hγ hδ t N.snd.val this),
  { cases N, cases N_snd, dsimp at hN₁, subst hN₁ },
  { have := min_tangle_le hγ c t ht, push_neg at this, exact this }
end

/-- Tool that lets us use well-founded recursion on codes via `μ`. -/
noncomputable def code_min_map (c : {c : code α α le_rfl // c.elts.nonempty}) : μ :=
of_tangle α c.val.extension_lt $ min_tangle c.val.extension_lt ⟨c.val.elts, c.property⟩

/-- The pullback `<` relation on codes is well-founded. -/
lemma code_wf : well_founded (inv_image μr (@code_min_map _ α _)) :=
inv_image.wf code_min_map μwf.wf

/-- The A-map, phrased as a function on non-empty `α`-codes. -/
def A_map_code {δ : Λ} (hδ : δ < α) (c : {c : code α α le_rfl // c.elts.nonempty})
(hne : c.val.extension ≠ δ) : {c : code α α le_rfl // c.elts.nonempty} :=
⟨⟨δ, coe_lt_coe.mpr hδ, A_map c.val.extension_lt hδ hne ⟨c.val.elts, c.property⟩⟩, begin
  obtain ⟨x, hx⟩ := c.property,
  dsimp, unfold A_map, simp,
  exact ⟨x, hx, local_cardinal_nonempty _⟩
end⟩

lemma A_map_code_elts {δ : Λ} (hδ : δ < α) (c : {c : code α α le_rfl // c.elts.nonempty})
(hne : c.val.extension ≠ δ) :
(↑(A_map_code hδ c hne) : code α α le_rfl).elts =
  (A_map c.val.extension_lt hδ hne ⟨c.val.elts, c.property⟩).val := rfl

lemma A_map_code_order {δ : Λ} (hδ : δ < α)
(c : {c : code α α le_rfl // c.elts.nonempty}) (hne : c.val.extension ≠ δ) :
code_min_map c < code_min_map (A_map_code hδ c hne) :=
A_map_order c.val.extension_lt hδ hne ⟨c.val.elts, c.property⟩

/-- This relation on `α`-codes allows us to state that there are only finitely many iterated images
under the inverse A-map. -/
def A_map_relation (c d : {c : code α α le_rfl // c.elts.nonempty}) : Prop :=
begin
  obtain ⟨⟨δ, hδ, D⟩, hD⟩ := d,
  cases δ,
  { exact false },
  { by_cases c.val.extension = δ,
    { exact false },
    { exact D = (A_map_code (coe_lt_coe.mp hδ) c h).val.elts } }
end

lemma A_map_subrelation : subrelation (@A_map_relation _ α _) (inv_image μr code_min_map) :=
begin
  intros c d h,
  obtain ⟨⟨δ, hδ, D⟩, hD⟩ := d,
  unfold A_map_relation at h,
  cases δ, { exfalso, exact h },
  dsimp at h,
  split_ifs at h, { exfalso, exact h },
  simp_rw h,
  refine A_map_code_order _ _ ‹_›
end

/-- There are only finitely many iterated images under any inverse A-map. -/
lemma A_map_relation_well_founded : well_founded (@A_map_relation _ α _) :=
subrelation.wf A_map_subrelation code_wf

def A_map_predecessor_subsingleton (c : {c : code α α le_rfl // c.elts.nonempty}) :
{d | A_map_relation d c}.subsingleton :=
begin
  obtain ⟨⟨γ, hγ, G⟩, hG⟩ := c,
  intros x hx y hy, dsimp at hx hy, unfold A_map_relation at hx hy, simp at hx hy,
  cases γ,
  { exfalso, dsimp at hx, exact hx },
  dsimp at hx hy,
  split_ifs at hx hy; try { exfalso, assumption },
  rw [hy, A_map_code_elts, A_map_code_elts, subtype.val_inj] at hx,
  obtain ⟨⟨δ, hδ, D⟩, hD⟩ := x, obtain ⟨⟨ε, hε, E⟩, hE⟩ := y,
  suffices : δ = ε,
  { subst this,
    have := A_map_injective _ _ _ hx,
    dsimp at this, cases this, refl },
  obtain ⟨t, ht⟩ := (A_map _ (coe_lt_coe.mp hγ) _ ⟨D, hD⟩).property,
  have ht' : t ∈ (A_map _ (coe_lt_coe.mp hγ) _ ⟨E, hE⟩).val,
  { rw hx, exact ht },
  unfold A_map at ht ht',
  simp at ht ht',
  obtain ⟨i, hi₁, x, hx₁, hx₂⟩ := ht,
  obtain ⟨j, hj₁, y, hy₁, hy₂⟩ := ht',
  rw ← hy₂ at hx₂, have := (to_tangle γ _).inj' hx₂, simp at this,
  have fδ := f_map_range δ γ hδ (coe_lt_coe.mp hγ) i,
  have fε := f_map_range ε γ hε (coe_lt_coe.mp hγ) j,
  simp_rw [this.left, fε] at fδ, simp at fδ, exact fδ.symm
end

end con_nf
