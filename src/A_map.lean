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
  suffices : # {x : near_litter // x.fst = i} = #{s // is_near_litter i s},
  { simp [local_cardinal, this] },
  refine cardinal.eq.2 ⟨⟨_, λ x, ⟨⟨i, x⟩, rfl⟩, _, _⟩⟩,
  { rintro ⟨x, rfl⟩,
    exact x.snd },
  { rintro ⟨⟨j, S⟩, rfl⟩,
    simp },
  { rintro ⟨j, S⟩,
    simp }
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

@[simp] lemma coe_A_map {γ : type_index} (hγ : γ < α) (hδ : δ < α)
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
  A_map (c.val.extension_lt.trans_le $ coe_le_coe.2 hβ) (hδ.trans_le hβ)
    ⟨c.val.elts, c.property⟩⟩, begin
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
inductive A_map_rel (c : nonempty_code α β hβ) : nonempty_code α β hβ → Prop
| intro (δ : Λ) (hδ : δ < β) : (c : code α β hβ).extension ≠ δ → A_map_rel (A_map_code hδ c)

@[simp] lemma A_map_rel_iff {c d : nonempty_code α β hβ} :
  A_map_rel c d ↔ ∃ δ (hδ : δ < β), (c : code α β hβ).extension ≠ δ ∧ A_map_code hδ c = d :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain ⟨δ, hδ, hc⟩ := h,
    exact ⟨δ, hδ, hc, rfl⟩ },
  { rintro ⟨δ, hδ, hc, rfl⟩,
    exact A_map_rel.intro _ _ hc }
end

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
lemma A_map_rel_subsingleton (hβ : β ≤ α) (c : nonempty_code α β hβ) :
  {d : nonempty_code α β hβ  | A_map_rel d c}.subsingleton :=
begin
  intros x hx y hy,
  simp only [subtype.val_eq_coe, ne.def, A_map_rel_iff, mem_set_of_eq] at hx hy,
  obtain ⟨δ, hδ, hx, rfl⟩ := hx,
  obtain ⟨ε, hε, hy, h⟩ := hy,
  rw [subtype.ext_iff, code.ext_iff] at ⊢ h,
  have : ε = δ := coe_injective h.1,
  subst this,
  obtain ⟨⟨γ, hγ, C⟩, hC⟩ := x,
  obtain ⟨⟨δ, hδ, D⟩, hD⟩ := y,
  have : δ = γ := A_map_disjoint_range _ _ (subtype.coe_injective h.2.eq),
  subst this,
  refine ⟨rfl, _⟩,
  simpa using A_map_injective _ _ (subtype.coe_injective h.2.eq).symm,
end

/-! ### Height of a code -/

/-- The height of a code is the amount of iterated images under an inverse alternative extension map
that it admits. This is uniquely defined since any code has at most one inverse image under the
A-map, and we can just repeat this process until no inverse image exists. -/
noncomputable def height : nonempty_code α β hβ → ℕ
| c := @dite _ (∃ d, A_map_rel d c) (classical.dec _) (λ h, height h.some + 1) (λ _, 0)
using_well_founded
{ rel_tac := λ _ _, `[exact ⟨A_map_rel, A_map_rel_well_founded hβ⟩],
  dec_tac := `[exact h.some_spec] }

lemma height_eq_zero {c : nonempty_code α β hβ} : height c = 0 ↔ ∀ d, ¬ A_map_rel d c :=
begin
  classical,
  rw height,
  refine (ne.dite_eq_right_iff $ λ h, _).trans not_exists,
  exact nat.succ_ne_zero _,
end

lemma height_ne_zero {c : nonempty_code α β hβ} : height c ≠ 0 ↔ {d | A_map_rel d c}.nonempty :=
height_eq_zero.not.trans $ by { push_neg, refl }

@[simp] lemma height_A_map_code {hδ : δ < β} (c : nonempty_code α β hβ) (hcδ : c.1.extension ≠ δ) :
  height (A_map_code hδ c) = height c + 1 :=
begin
  classical,
  have h : ∃ d, A_map_rel d (A_map_code hδ c) := ⟨c, A_map_rel.intro _ _ hcδ⟩,
  rw [height, dif_pos h, A_map_rel_subsingleton _ _ h.some_spec (A_map_rel.intro _ _ hcδ)],
end

lemma height_even_of_A_map_code_not_even {γ : Λ} (hγ : γ < β) (c : nonempty_code α β hβ)
  (hcγ : c.1.extension ≠ γ) (hc : ¬ even (height c)) : even (height $ A_map_code hγ c) :=
by { rw [height_A_map_code c hcγ, nat.even_succ], exact hc }

lemma coe_A_map_code_ne_singleton {γ : type_index} {hγ : γ < β} {hδ : δ < β}
  {g : tangle α γ (hγ.trans_le $ coe_le_coe.2 hβ)} {c : nonempty_code α β hβ} :
  (A_map_code hδ c : code α β hβ) ≠ ⟨γ, hγ, {g}⟩ :=
begin
  simp only [A_map_code, coe_A_map, subtype.coe_mk, ne.def, eq_self_iff_true, heq_iff_eq, true_and],
  rintro ⟨rfl, h⟩,
  refine (cardinal.one_lt_aleph_0.trans_le $ κ_regular.aleph_0_le.trans κ_le_μ).not_le _,
  rw [←cardinal.mk_singleton g, ←h.eq],
  exact μ_le_mk_A_map _ ⟨(c : code α β hβ).elts, c.2⟩,
end

@[simp] lemma height_singleton {γ : type_index} {hγ : γ < β}
  (g : tangle α γ $ hγ.trans_le $ coe_le_coe.2 hβ) :
  height (⟨⟨γ, hγ, {g}⟩, singleton_nonempty _⟩ : nonempty_code α β hβ) = 0 :=
begin
  refine height_eq_zero.2 (λ c hc, _),
  obtain ⟨δ, hδ, hc, h⟩ := A_map_rel_iff.1 hc,
  exact coe_A_map_code_ne_singleton (congr_arg subtype.val h),
end

@[simp] lemma height_base (c : nonempty_code α β hβ) (hc : c.val.extension = ⊥) :
  height c = 0 :=
by { rw height_eq_zero, rintros d ⟨γ, hγ, -⟩, simp at hc, exact hc }

/-! ### A⁻¹ and equivalence of codes -/

/-- The inverse map to `A_map_code`. -/
noncomputable def A_inverse (c : nonempty_code α β hβ) (hc : height c ≠ 0) : nonempty_code α β hβ :=
(height_ne_zero.1 hc).some

lemma A_inverse_spec (c : nonempty_code α β hβ) (hc) : A_map_rel (A_inverse c hc) c :=
(height_ne_zero.1 hc).some_spec

namespace code
variables {c d : code α β hβ}

/-- Equivalence of codes. -/
@[mk_iff] inductive equiv : code α β hβ → code α β hβ → Prop
| refl (c) : equiv c c
| empty_empty ⦃γ⦄ (hγ) ⦃δ⦄ (hδ) : equiv ⟨γ, hγ, ∅⟩ ⟨δ, hδ, ∅⟩
| A_map_left (γ) (hγ : γ < β) (c : nonempty_code α β hβ) :
  c.1.extension ≠ γ → even (height c) → equiv (A_map_code hγ c) c
| A_map_right (γ) (hγ : γ < β) (c : nonempty_code α β hβ) :
  c.1.extension ≠ γ → even (height c) → equiv c (A_map_code hγ c)

/-! We declare new notation for code equivalence. -/
infix ` ≡ `:50 := equiv

attribute [refl] equiv.refl

lemma equiv.rfl : c ≡ c := equiv.refl _

lemma equiv.symm : symmetric ((≡) : code α β hβ → code α β hβ → Prop)
| _ _ (equiv.refl _) := equiv.refl _
| _ _ (equiv.empty_empty hγ hδ) := equiv.empty_empty _ _
| _ _ (equiv.A_map_left γ hγ c hcγ hc) := equiv.A_map_right γ hγ c hcγ hc
| _ _ (equiv.A_map_right γ hγ c hcγ hc) := equiv.A_map_left γ hγ c hcγ hc

lemma equiv_transitive : transitive ((≡) : code α β hβ → code α β hβ → Prop) := sorry
-- | _ _ _ (equiv.refl _) _ := ‹_›
-- | _ _ _ _ (equiv.refl _) := ‹_›
-- | _ _ _ (equiv.empty_empty hγ hδ) (equiv.empty_empty _ hε) := equiv.empty_empty _ _
-- | _ _ _ (equiv.A_map_left γ hγ _ hcγ _) (equiv.A_map_right δ hδ c hcδ h) := sorry
-- | _ _ _ (equiv.A_map_right γ hγ c hc h) (equiv.A_map_left _ _ _ _ _) := equiv.refl _
-- | _ _ _ (equiv.empty_empty hγ _) (equiv.A_map_right δ hδ c hcδ h) := _

lemma equiv_equivalence : equivalence ((≡) : code α β hβ → code α β hβ → Prop) :=
⟨equiv.refl, equiv.symm, equiv_transitive⟩

lemma equiv.nonempty_iff_nonempty :
  ∀ {c d : code α β hβ}, c ≡ d → (c.elts.nonempty ↔ d.elts.nonempty)
| _ _ (equiv.refl _) := iff.rfl
| _ _ (equiv.empty_empty hγ hδ) := iff_of_false not_nonempty_empty not_nonempty_empty
| _ _ (equiv.A_map_left γ hγ c hc h) := iff_of_true (A_map_code _ _).2 c.2
| _ _ (equiv.A_map_right γ hγ c hc h) := iff_of_true c.2 (A_map_code _ _).2

lemma equiv.ext : ∀ {c d : code α β hβ}, c ≡ d → c.extension = d.extension → c = d
| _ _ (equiv.refl _) _ := rfl
| _ _ (equiv.empty_empty hγ hδ) rfl := rfl
| _ _ (equiv.A_map_left γ hγ c hc h) H := (hc H.symm).elim
| _ _ (equiv.A_map_right γ hγ c hc h) H := (hc H).elim

lemma singleton_equiv (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ) (g : tangle α γ _) :
  (⟨γ, coe_lt_coe.2 hγ, {g}⟩ : code α β hβ) ≡
    ⟨δ, coe_lt_coe.2 hδ, to_tangle δ (hδ.trans_le hβ) ''
      local_cardinal (f_map γ δ (coe_lt_coe.2 (hγ.trans_le hβ)) (hδ.trans_le hβ) g)⟩ :=
begin
  convert code.equiv.A_map_right _ hδ
    ⟨⟨γ, coe_lt_coe.2 hγ, {g}⟩, singleton_nonempty g⟩ (coe_ne_coe.2 hγδ) _,
  { simp only [coe_A_map, subtype.coe_mk, mem_singleton_iff, Union_Union_eq_left] },
  { rw height_singleton,
    exact even_zero }
end

lemma singleton_equiv_iff {hγ : γ < β} {g : tangle _ _ _} {c : code α β hβ} :
  ⟨γ, coe_lt_coe.2 hγ, {g}⟩ ≡ c ↔
    c = ⟨γ, coe_lt_coe.2 hγ, {g}⟩ ∨
      ∃ δ (hc : c.extension = some δ) (hδ : δ < β) (hγδ : γ ≠ δ),
        c = A_map_code hδ ⟨⟨γ, coe_lt_coe.2 hγ, {g}⟩, singleton_nonempty g⟩ :=
begin
  classical,
  refine ⟨λ h, _, λ h, _⟩,
  {
    sorry
    -- cases h,
    -- dsimp at h,
    -- rw dif_pos (singleton_nonempty g) at h,
    -- have : even (height ⟨⟨γ, coe_lt_coe.2 hγ, {g}⟩, singleton_nonempty g⟩),
    -- { convert even_zero,
    --   simp },
    -- rw dif_neg (nat.even_iff_not_odd.mp this) at h,
    -- cases c with δ hδ D,
    -- split_ifs at h,
    -- { left,
    --   dsimp at h_1,
    --   subst h_1,
    --   simp at h,
    --   rw h },
    -- { right,
    --   cases δ; dsimp at h,
    --   { cases h },
    --   { rw ← h,
    --     exact ⟨δ, by { simp, refl }, coe_lt_coe.1 hδ, h_1 ∘ coe_eq_coe.2, rfl⟩ } }
        },
  { obtain rfl | ⟨δ, hc, hδ, hγδ, rfl⟩ := h,
    { refl },
    { convert singleton_equiv hγ hδ hγδ g,
      simp } }
end

lemma extension_eq_of_singleton_equiv_singleton (hγ : γ < β) (hδ : δ < β) {a b : tangle α _ _}
  (h : (⟨γ, coe_lt_coe.2 hγ, {a}⟩ : code α β hβ) ≡ ⟨δ, coe_lt_coe.2 hδ, {b}⟩) :
  γ = δ :=
begin
  cases singleton_equiv_iff.1 h,
  { simp at h_1,
    exact coe_eq_coe.1 h_1.left.symm },
  { exfalso,
    obtain ⟨ε, hc, hε, hγε, hA⟩ := h_1,
    have := congr_arg code.extension hA,
    simp at this,
    rw coe_eq_coe at this,
    subst this,
    simp at hA,
    sorry,
    -- exact hA
    }
end

/- Yaël: Do we really need this lemma? looks like `extension_eq_of_singleton_equiv_singleton` is
just as practical -/
lemma eq_of_singleton_equiv_singleton (hβ : β ≤ α) (hγ : γ < β) (hδ : δ < β) (a b : tangle _ _ _)
  (h : (⟨γ, coe_lt_coe.2 hγ, {a}⟩ : code α β hβ) ≡ ⟨δ, coe_lt_coe.2 hδ, {b}⟩) :
  a = cast (by simp_rw extension_eq_of_singleton_equiv_singleton _ _ h) b :=
begin
  sorry,
  -- cases singleton_equiv_iff.mp h,
  -- { simp at h_1,
  --   have := coe_eq_coe.1 h_1.left,
  --   subst this,
  --   simp at h_1 ⊢,
  --   exact h_1.symm },
  -- { exfalso,
  --   obtain ⟨ε, hc, hε, hγε, hA⟩ := h_1,
  --   have := congr_arg code.extension hA,
  --   simp at this,
  --   rw coe_eq_coe at this,
  --   subst this,
  --   simp at hA,
  --   exact hA }
end

/-!
Note for whoever is formalising this: feel free to reorder these definitions if it turns out
to be useful to use some lemmas in the proofs of others.
-/

/-- A code is representative if it is empty and has preferred extension `⊥`, or it is nonempty and
has even height. -/
inductive is_representative : code α β hβ → Prop
| empty : is_representative ⟨⊥, bot_lt_coe _, ∅⟩
| nonempty (c : nonempty_code α β hβ) : even (height c) → is_representative c

lemma is_representative.unique (hc : c.is_representative) (hd : d.is_representative)
  (hequiv : c ≡ d) : c = d :=
begin
  classical,
  obtain hc | ⟨c, hc⟩ := hc; obtain hd | ⟨d, hd⟩ := hd,
  { refl },
  sorry,
  sorry,
  sorry,
  -- by_cases d.elts.nonempty,
  -- { have := hequiv.nonempty_iff_nonempty.2 h,
  --   unfold code.equiv at hequiv,
  --   rw dif_pos h at hd,
  --   rw dif_pos this at hc hequiv,
  --   rw dif_neg (nat.even_iff_not_odd.1 hc) at hequiv,
  --   split_ifs at hequiv,
  --   { ext1,
  --     exact h_1,
  --     exact heq_of_cast_eq _ hequiv },
  --   { cases d with γ hγ G,
  --     dsimp at h h_1 hequiv,
  --     cases γ; dsimp at hequiv,
  --     cases hequiv,
  --     suffices : ¬even (height ⟨c, this⟩), cases this hc,
  --     rw [← nat.even_succ, ← height_A_map_code],
  --     simp_rw ← hequiv at hd,
  --     exact hd } },
  -- { have := h, rw ← code.equiv_nonempty_iff_nonempty hβ c d hequiv at this,
  --   unfold code.is_representative at hd hc,
  --   unfold code.equiv at hequiv,
  --   rw dif_neg h at hd,
  --   rw dif_neg this at hc hequiv,
  --   ext1,
  --   rw [hd, hc],
  --   rw set.not_nonempty_iff_eq_empty at h this,
  --   rw ← hc at hd,
  --   cases d with γ hγ G,
  --   cases c with δ hδ D,
  --   dsimp at hd h this,
  --   subst hd,
  --   dsimp,
  --   rw [h, this] }
end

lemma is_representative.A_map (c d : nonempty_code α β hβ)
  (hc : c.val.is_representative) (hd : d.val.is_representative)
  {γ : Λ} (hγ : γ < β) (hγd : d.val.extension ≠ γ) : c ≠ A_map_code hγ d :=
begin
  intro h,
  have := code.is_representative.unique hc hd _, rwa subtype.val_inj at this, rw this at h,
  exact A_map_code_ne hγ d h,
  by_cases even (height d),
  { exfalso, have := code.equiv.A_map_left _ hγ _ hγd h, sorry },
  { have := height_even_of_A_map_code_not_even hγ d hγd h, sorry }
end

lemma representative_code_exists_unique (c : code α β hβ) : ∃! d ≡ c, d.is_representative := sorry

lemma equiv_code_exists_unique (γ : Λ) (c : code α β hβ) : ∃! d ≡ c, d.extension = γ := sorry

lemma equiv_bot_code_subsingleton (c : code α β hβ) :
  ∀ d ≡ c, ∀ e ≡ c, d.extension = ⊥ → e.extension = ⊥ → d = e := sorry

end code
end con_nf
