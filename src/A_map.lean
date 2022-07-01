import data.nat.parity
import f_map
import mathlib.logic
import mathlib.with_bot

open function set with_bot
open_locale cardinal

universe u

namespace con_nf
open params
variables [params.{u}] {α β γ δ : Λ} [phase_1a.{u} α] {hβ : β ≤ α}

/-- The *local cardinal* of a litter is the set of all near-litters to that litter. -/
def local_cardinal (i : litter) : set near_litter := {s : near_litter | s.1 = i}

lemma local_cardinal_nonempty (i : litter) : (local_cardinal i).nonempty :=
⟨⟨i, litter_set _, is_near_litter_litter_set _⟩, rfl⟩

lemma local_cardinal_disjoint : pairwise (disjoint on local_cardinal) :=
λ i j h N hN, h $ hN.1.symm.trans hN.2

@[simp] lemma mk_local_cardinal (i : litter) : #(local_cardinal i) = #μ :=
begin
  refine eq.trans (cardinal.eq.2 ⟨⟨_, λ x, ⟨⟨i, x⟩, rfl⟩, _, _⟩⟩) (mk_near_litter' i),
  { rintro ⟨x, (rfl : x.1 = i)⟩,
    exact x.snd },
  { rintro ⟨⟨j, S⟩, (rfl : j = i)⟩,
    refl },
  { exact λ x, rfl }
end

/-- The *alternative extension* map. For a non-empty set of tangles `G`, consider the code
`(α, γ, G)`. We then construct the non-empty set `D` such that `(α, δ, D)` is an alternative
extension of the same object in TTT. -/
def A_map {γ : type_index} (hγ : γ < α) (hδ : δ < α) (c : {s : set (tangle α γ hγ) // s.nonempty}) :
  {s : set (tangle α δ (coe_lt_coe.2 hδ)) // s.nonempty} :=
⟨⋃ b ∈ (c : set (tangle α γ hγ)), to_tangle δ hδ '' local_cardinal (f_map γ δ hγ hδ b), begin
  simp only [nonempty_bUnion, nonempty_image_iff],
  exact c.2.imp (λ t ht, ⟨ht, ⟨f_map γ δ hγ hδ _, litter_set _, is_near_litter_litter_set _⟩, rfl⟩),
end⟩

@[simp] lemma coe_A_map {γ : type_index} {hγ : γ < α} (hδ : δ < α)
  (c : {s : set (tangle α γ hγ) // s.nonempty}) :
  (A_map hγ hδ c : set (tangle α δ (coe_lt_coe.2 hδ))) =
    ⋃ b ∈ (c : set (tangle α γ hγ)), to_tangle δ hδ '' local_cardinal (f_map γ δ hγ hδ b) := rfl

lemma subset_A_map {γ : type_index} (hγ : γ < α) (hδ : δ < α)
  (c : {s : set (tangle α γ hγ) // s.nonempty}) :
  to_tangle δ hδ '' local_cardinal (f_map γ δ hγ hδ c.property.some) ⊆ (A_map hγ hδ c).val :=
begin
  convert subset_Union₂ c.property.some _,
  { refl },
  { exact c.property.some_spec }
end

lemma μ_le_mk_A_map {γ : type_index} {hγ : γ < α} (hδ : δ < α)
  (c : {s : set (tangle α γ hγ) // s.nonempty}) :
  #μ ≤ #(A_map hγ hδ c : set (tangle α δ (coe_lt_coe.2 hδ))) :=
begin
  refine (cardinal.mk_le_mk_of_subset $ subset_A_map _ _ _).trans_eq' _,
  rw [cardinal.mk_image_eq, mk_local_cardinal],
  exact (to_tangle δ hδ).inj',
end

lemma A_map_injective_aux {γ : type_index} (hγ : γ < α) (hδ : δ < α)
  {s t : {s : set (tangle α γ hγ) // s.nonempty}} (h : A_map hγ hδ s = A_map hγ hδ t) :
  ∀ x ∈ s.val, x ∈ t.val :=
begin
  cases s with G₁ hG₁, cases t with G₂ hG₂,
  intros g hg,
  unfold A_map at h,
  have := subtype.ext_iff_val.mp h, dsimp at this,
  obtain ⟨x, hx, y, hy₁, hy₂⟩ := exists_inter_of_Union_eq_Union this g hg
    ⟨to_tangle δ hδ $ ⟨f_map γ δ hγ hδ g, litter_set _, is_near_litter_litter_set _⟩,
      by simp [local_cardinal] ⟩,
  rw mem_image at hy₁ hy₂,
  obtain ⟨s, hs₁, hs₂⟩ := hy₁, obtain ⟨t, ht₁, ht₂⟩ := hy₂,
  rw ← ht₂ at hs₂, have s_eq_t := (to_tangle δ hδ).inj' hs₂, rw s_eq_t at hs₁,
  suffices : g = x, by { rw ← this at hx, exact hx },
  by_contradiction,
  have := local_cardinal_disjoint (f_map γ δ hγ hδ g) (f_map γ δ hγ hδ x)
    ((f_map_injective γ δ hγ hδ).ne h),
  exact this ⟨hs₁, ht₁⟩
end

lemma A_map_injective {γ : type_index} (hγ : γ < α) (hδ : δ < α) : injective (A_map hγ hδ) :=
λ s t h, by { ext, exact ⟨A_map_injective_aux _ _ h x, A_map_injective_aux _ _ h.symm x⟩ }

/-!
We don't need to prove that the ranges of the `A_δ` are disjoint for different `δ`, since this holds
at the type level.

We now show that there are only finitely many iterated images under any inverse A-map.
-/

lemma well_founded_of_tangle {β : type_index} (h : β < α) :
  well_founded (λ a b, of_tangle α h a < of_tangle α h b) :=
inv_image.wf _ is_well_order.wf

/-- The minimum tangle of a nonempty set of tangles. -/
noncomputable def min_tangle {γ : type_index} (hγ : γ < α)
  (c : {s : set (tangle α γ hγ) // s.nonempty}) : tangle α γ hγ :=
(well_founded_of_tangle hγ).min c.val c.property

lemma min_tangle_mem {γ : type_index} (hγ : γ < α) (c : {s : set (tangle α γ hγ) // s.nonempty}) :
  min_tangle hγ c ∈ c.val :=
well_founded.min_mem _ c.val c.property

lemma min_tangle_le {γ : type_index} (hγ : γ < α) (c : {s : set (tangle α γ hγ) // s.nonempty}) :
  ∀ x ∈ c.val, of_tangle α hγ (min_tangle hγ c) ≤ of_tangle α hγ x :=
λ x hx, not_lt.1 $ (well_founded_of_tangle hγ).not_lt_min c.val c.property hx

lemma A_map_order {γ : type_index} (hγ : γ < α) (hδ : δ < α)
  (c : {s : set (tangle α γ hγ) // s.nonempty}) :
  of_tangle α hγ (min_tangle hγ c) <
    of_tangle α (coe_lt_coe.2 hδ) (min_tangle (coe_lt_coe.2 hδ) (A_map hγ hδ c)) :=
begin
  obtain ⟨s, ⟨t, rfl⟩, hs⟩ := min_tangle_mem (coe_lt_coe.2 hδ) (A_map hγ hδ c),
  rw mem_Union at hs,
  obtain ⟨ht, N, hN₁, hN₂⟩ := hs,
  rw ← hN₂, clear hN₂,
  have : is_near_litter (f_map γ δ hγ hδ t) N.snd.val,
  { convert N.snd.property,
    exact hN₁.symm },
  convert (min_tangle_le hγ c t ht).trans_lt (f_map_position_raising γ δ hγ hδ t N.snd.val this),
  obtain ⟨i, N, hN⟩ := N,
  change i = f_map γ δ hγ hδ t at hN₁,
  subst hN₁,
end

/-- Tool that lets us use well-founded recursion on codes via `μ`. -/
noncomputable def code_min_map (c : nonempty_code α β hβ) : μ :=
of_tangle α (c.val.extension_lt.trans_le $ coe_le_coe.2 hβ) $
  min_tangle (c.val.extension_lt.trans_le $ coe_le_coe.2 hβ) ⟨c.val.elts, c.property⟩

/-- The pullback `<` relation on codes is well-founded. -/
lemma code_wf : well_founded (inv_image μr (code_min_map : nonempty_code α β hβ → μ)) :=
inv_image.wf (code_min_map) μwf.wf

/-- The A-map, phrased as a function on non-empty `α`-codes. -/
def A_map_code (hδ : δ < β) (c : nonempty_code α β hβ) : nonempty_code α β hβ :=
⟨⟨δ, coe_lt_coe.2 hδ,
  A_map (c.val.extension_lt.trans_le $ coe_le_coe.2 hβ) (hδ.trans_le hβ) ⟨c.val.elts, c.property⟩⟩,
    begin
      obtain ⟨x, hx⟩ := c.property,
      dsimp,
      simp only [subtype.coe_mk, nonempty_bUnion, nonempty_image_iff, exists_prop, coe_lt_coe,
        coe_le_coe],
      exact ⟨x, hx, local_cardinal_nonempty _⟩,
    end⟩

@[simp] lemma coe_A_map_code (hδ : δ < β) (c : nonempty_code α β hβ) :
  (A_map_code hδ c : code α β hβ) =
    ⟨δ, coe_lt_coe.2 hδ, A_map (c.val.extension_lt.trans_le $ coe_le_coe.2 hβ) (hδ.trans_le hβ)
     ⟨c.val.elts, c.property⟩⟩ := rfl

@[simp] lemma A_map_code_extension (hδ : δ < β) (c : nonempty_code α β hβ) :
  (↑(A_map_code hδ c) : code α β hβ).extension = δ := rfl

@[simp] lemma A_map_code_elts (hδ : δ < β) (c : nonempty_code α β hβ) :
  (↑(A_map_code hδ c) : code α β hβ).elts =
    (A_map (c.val.extension_lt.trans_le $ coe_le_coe.2 hβ) (hδ.trans_le hβ)
      ⟨c.val.elts, c.property⟩).val := rfl

lemma A_map_code_eq_iff (hδ : δ < β) (c : nonempty_code α β hβ)
  (D : set (tangle α δ $ coe_lt_coe.2 $ hδ.trans_le hβ)) (hD : D.nonempty) :
  A_map_code hδ c = ⟨⟨δ, coe_lt_coe.2 hδ, D⟩, hD⟩ ↔
    (A_map_code hδ c : code α β hβ).elts = D :=
by split; { intro h, cases h, refl }

lemma A_map_code_coe_eq_iff (hδ : δ < β) (c : nonempty_code α β hβ)
  (D : set (tangle α δ $ coe_lt_coe.2 $ hδ.trans_le hβ)) :
  (A_map_code hδ c : code α β hβ) = ⟨δ, coe_lt_coe.2 hδ, D⟩
    ↔ (↑(A_map_code hδ c) : code α β hβ).elts = D :=
by split; { intro h, cases h, refl }

lemma A_map_code_injective (hδ : δ < α) :
  injective (A_map_code hδ : nonempty_code α α le_rfl → nonempty_code α α le_rfl) := sorry

lemma A_map_code_ne (hδ : δ < β) (c : nonempty_code α β hβ) : c ≠ A_map_code hδ c := sorry

lemma A_map_code_order (hδ : δ < β) (c : nonempty_code α β hβ) :
  code_min_map c < code_min_map (A_map_code hδ c) :=
A_map_order (c.val.extension_lt.trans_le $ coe_le_coe.2 hβ) (hδ.trans_le hβ) ⟨c.val.elts, c.2⟩

/-- This relation on `α`-codes allows us to state that there are only finitely many iterated images
under the inverse A-map. -/
@[mk_iff] inductive A_map_rel (c : nonempty_code α β hβ) : nonempty_code α β hβ → Prop
| intro (δ : Λ) (hδ : δ < β) : (c : code α β hβ).extension ≠ δ → A_map_rel (A_map_code hδ c)

lemma A_map_subrelation :
  subrelation A_map_rel (inv_image μr (code_min_map : nonempty_code α β hβ → μ))
| c _ (A_map_rel.intro δ hδ hc) := A_map_code_order _ _

/-- There are only finitely many iterated images under any inverse A-map. -/
lemma A_map_rel_well_founded (hβ : β ≤ α) :
  well_founded (A_map_rel : nonempty_code α β hβ → nonempty_code α β hβ → Prop) :=
A_map_subrelation.wf code_wf

lemma A_map_disjoint_range {hγ : γ < α} {δ ε : type_index} {hδ : δ < α} {hε : ε < α}
  (c : {c : set (tangle α δ _) // c.nonempty}) (d : {d : set (tangle α ε _) // d.nonempty})
  (h : A_map hδ hγ c = A_map hε hγ d) : δ = ε :=
begin
  unfold A_map at h,
  rw subtype.ext_iff_val at h,
  dsimp at h,
  obtain ⟨b, hb⟩ := c.property,
  have mem : to_tangle γ hγ ⟨f_map δ γ hδ hγ b, litter_set _, is_near_litter_litter_set _⟩
    ∈ to_tangle γ hγ '' local_cardinal (f_map δ γ hδ hγ b),
  { exact mem_image_of_mem _ rfl },
  have := subset_Union₂ b hb mem,
  simp [h] at this,
  obtain ⟨i, hi₁, hi₂⟩ := this,
  exact f_map_range_eq hi₂,
end

/-- There is at most one inverse under an A-map. This corresponds to the fact that there is only one
code which is related (on the left) to any given code under the A-map relation. -/
lemma A_map_rel_subsingleton (c : nonempty_code α β hβ) :
  {d : nonempty_code α β hβ  | A_map_rel d c}.subsingleton :=
begin
  intros x hx y hy,
  simp only [subtype.val_eq_coe, ne.def, A_map_rel_iff, mem_set_of_eq] at hx hy,
  obtain ⟨δ, hδ, hx, rfl⟩ := hx,
  obtain ⟨ε, hε, hy, h⟩ := hy,
  rw [subtype.ext_iff, code.ext_iff] at ⊢ h,
  have : δ = ε := coe_injective h.1,
  subst this,
  obtain ⟨⟨γ, hγ, C⟩, hC⟩ := x,
  obtain ⟨⟨δ, hδ, D⟩, hD⟩ := y,
  have : γ = δ := A_map_disjoint_range _ _ (subtype.coe_injective h.2.eq),
  subst this,
  refine ⟨rfl, _⟩,
  simpa using A_map_injective _ _ (subtype.coe_injective h.2.eq),
end
end con_nf
