import code

/-!
# f-maps
Consider a code `(α, γ, G)`. We are interested in the alternative extensions of this object at
different proper type indices `δ : Λ`. We will define the function `A_δ` which will map the code
`(α, γ, G)` to a new code `(α, δ, D)`. The elements of `D` are produced by the so-called f-maps.
In particular, elements of `D` are of the form `to_tangle M` where `M` is a near-litter to some
litter `N`, which in turn is given by an f-map.
-/

open with_bot
open_locale cardinal

universe u

namespace con_nf
open params
variables [params.{u}] {α β γ : Λ} [phase_1a.{u} α]

instance (h : β < α) : linear_order (code α β h) := sorry

lemma well_founded_code (h : β < α) : @well_founded (code α β h) (<) := sorry

lemma well_founded_of_tangle (h : β < α) :
  well_founded (λ a b, of_tangle _ h a < of_tangle _ _ b) :=
well_founded.inv_image _ is_well_order.wf

/-!
We now define the f-maps. We will do so in two stages; first, we define it as a function `μ → μ`,
(named `f_map_core`) and then raise it to be litter-valued and defined on tangles. This allows some
nicer definitional properties, such as that the resulting litter is of the form `⟨⟨β, γ⟩, χ⟩` for
`χ : μ`.

The value of an f-map is defined as a litter that satisfies two conditions, the second and third
bullet points on the blueprint (the first is a type-level condition that the resulting litter is of
the form `⟨⟨β, γ⟩, χ⟩`). In order to show that the f-maps are well-defined, we show that this set of
candidate litters is non-empty. In particular, the set of all possible litters has size `μ`, and
each constraint only removes `< μ` elements from this candidate set.

The following two lemmas will prove that for each constraint, we remove less than `μ` litters from
our pool of potential litters.
-/

local attribute [semireducible] litter

/-- Principal segments (sets of the form `{y | y < x}`) have cardinality `< μ`. -/
lemma principal_seg_card_lt (x : μ) : #{y // y < x} < #μ := cardinal.card_typein_lt (<) x μ_ord.symm

/-- Initial segments (sets of the form `{y | y ≤ x}`) have cardinality `< μ`. -/
lemma initial_seg_card_lt (x : μ) : #{y // y ≤ x} < #μ :=
begin
  have : {y | y ≤ x} = {y | y < x} ∪ {x},
  { rw set.union_def, simp, simp_rw le_iff_lt_or_eq },
  rw ← set.coe_set_of, rw this,
  rw cardinal.mk_union_of_disjoint,
  rw set.coe_set_of,
  rw cardinal.mk_singleton,
  by_cases ℵ₀ ≤ #{y // y < x},
  { convert (principal_seg_card_lt x), exact cardinal.add_one_eq h },
  { transitivity ℵ₀,
    push_neg at h, exact cardinal.add_lt_aleph_0 h cardinal.one_lt_aleph_0,
    exact lt_of_le_of_lt κ_regular.aleph_0_le κ_lt_μ },
  { simp }
end

lemma mk_litters_inflationary_constraint' (β γ : Λ) (hβ : β < α) (hγ : γ < α) (x : μ) :
#{N : (Σ i, {s // is_near_litter ⟨⟨β, γ⟩, i⟩ s}) |
  of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, N.fst⟩, N.snd⟩) ≤ x} < #μ :=
begin
  refine lt_of_le_of_lt (cardinal.mk_le_of_injective _) (initial_seg_card_lt x),
  { rintro ⟨⟨i, N⟩, hN⟩, exact ⟨of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, i⟩, N⟩), hN⟩ },
  rintros ⟨⟨i, N⟩, hN⟩ ⟨⟨j, M⟩, hM⟩ h,
  simp at h, obtain ⟨hij, hNM⟩ := h, subst hij, simp at hNM, subst hNM
end

/-- One of the constraints in defining the f-maps is that for all near-litters to the result litter
`N`, they are positioned higher than `x` in `μ` (under `to_tangle`). We show that there are less
than `μ` litters that do *not* satisfy this constraint. -/
lemma mk_litters_inflationary_constraint (β γ : Λ) (hβ : β < α) (hγ : γ < α) (x : μ) :
#{i : μ | ∃ N : {s // is_near_litter ⟨⟨β, γ⟩, i⟩ s},
  of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, i⟩, N⟩) ≤ x} < #μ :=
begin
  suffices : #{i : μ | ∃ N : {s // is_near_litter ⟨⟨β, γ⟩, i⟩ s},
    of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, i⟩, N⟩) ≤ x}
    ≤ #{N : (Σ i, {s // is_near_litter ⟨⟨β, γ⟩, i⟩ s}) |
    of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, N.fst⟩, N.snd⟩) ≤ x},
  { exact lt_of_le_of_lt this (mk_litters_inflationary_constraint' _ _ hβ hγ _) },
  dsimp, refine ⟨⟨λ ⟨i, hi⟩, ⟨⟨i, hi.some⟩, hi.some_spec⟩, _⟩⟩,
  rintros ⟨i, N, hN⟩ ⟨j, M, hM⟩ hij, simp at hij ⊢, exact hij.left
end

/-- Only `< μ` elements of `μ` have been hit so far by f_map_core. -/
lemma mk_litters_inj_constraint (β γ : Λ) (hβ : β < α) (hγ : γ < α) (x : μ)
(f_map_core : Π (y < x), μ) : #{i : μ | ∃ y < x, f_map_core y ‹_› = i} < #μ :=
begin
  have : {i | ∃ y < x, f_map_core y ‹_› = i}
    = {i | ∃ (y : {y // y < x}), f_map_core y.val y.property = i} := by simp,
  rw this, exact lt_of_le_of_lt cardinal.mk_range_le (principal_seg_card_lt x),
end

/-!
To keep track of the hypotheses that went into creating the f-maps, we create a few structures to
store the result of the f-map as well as the conditions on their values.
-/

def f_map_generator {β γ : Λ} (hβ : β < α) (hγ : γ < α)
(x : μ) (R : Π y < x, μ) := {i |
  (∀ N : {s // is_near_litter ⟨⟨β, γ⟩, i⟩ s},
    x < of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, i⟩, N⟩))
  ∧ ∀ y (H : y < x), R y H ≠ i
}

def pre_f_map_result_is_viable (β γ : Λ) (hβ : β < α) (hγ : γ < α) (x : μ) (R : Π y < x, μ) :=
∀ y ≤ x, (f_map_generator hβ hγ y (λ z hz, R z (lt_of_lt_of_le hz H))).nonempty

def pre_f_map_result_is_allowed (β γ : Λ) (hβ : β < α) (hγ : γ < α)
(x : μ) (R : Π y ≤ x, μ) :=
Σ' hv : pre_f_map_result_is_viable β γ hβ hγ x (λ z hz, R z (le_of_lt hz)),
∀ y ≤ x, R y ‹_› = (hv y ‹_›).some

def f_map_result (β γ : Λ) (hβ : β < α) (hγ : γ < α) (x : μ) : Type u :=
{R : Π y ≤ x, μ // nonempty (pre_f_map_result_is_allowed β γ hβ hγ x R)}

def extend_result (β γ : Λ) (hβ : β < α) (hγ : γ < α) (x : μ)
(h_lt : Π y < x, f_map_result β γ hβ hγ y) : Π y < x, μ := λ y hy, (h_lt y hy).val y le_rfl

/-- By construction, all the f_map_results have matching output values, where they are defined. -/
lemma f_map_result_coherent (β γ : Λ) (hβ : β < α) (hγ : γ < α) (x y : μ)
(fx : f_map_result β γ hβ hγ x) (fy : f_map_result β γ hβ hγ y) :
Π (z : μ), z ≤ x → z ≤ y → fx.val z ‹_› = fy.val z ‹_›
| z hzx hzy := begin
  rw (fx.property.some).snd z hzx,
  rw (fy.property.some).snd z hzy,
  congr,
  ext w hw, dsimp,
  refine f_map_result_coherent w _ _
end
using_well_founded { dec_tac := `[exact psigma.lex.left _ _ ‹_›] }

/-- We can recursively construct the (unique) f_map_result for arbitrary `x`. -/
noncomputable def mk_f_map_result (β γ : Λ) (hβ : β < α) (hγ : γ < α) (x : μ)
(h_lt : Π y < x, f_map_result β γ hβ hγ y)
(hx : (f_map_generator hβ hγ x $ extend_result β γ hβ hγ x h_lt).nonempty)
: f_map_result β γ hβ hγ x :=
begin
  refine ⟨λ y hy, _, _⟩,
  { by_cases x = y,
    { exact hx.some },
    { refine (h_lt y _).val y le_rfl,
      rw le_iff_lt_or_eq at hy,
      cases hy,
      { exact hy },
      { exfalso, exact h hy.symm } } },
  refine ⟨⟨_, _⟩⟩,
  { intros y hy,
    by_cases x = y,
    { subst h, convert hx, unfold extend_result, ext z hz, split_ifs,
      { exfalso, exact ne_of_lt hz h.symm },
      { refl } },
    { convert (h_lt y (lt_of_le_of_ne hy (ne.symm h))).property.some.fst y le_rfl,
      ext z hz, dsimp, split_ifs with h₁,
      { exfalso, rw h₁ at hy, exact not_lt_of_ge hy hz },
      { exact f_map_result_coherent β γ hβ hγ z y (h_lt z _) (h_lt y _) z le_rfl _ } } },
  { intros y hy, dsimp,
    split_ifs,
    { subst h, congr,
      ext z hz, split_ifs,
      { exfalso, exact ne_of_lt hz h.symm, },
      { refl } },
    { convert ((h_lt y _).property.some).snd y le_rfl,
      ext z hz, split_ifs with h₁,
      { exfalso, rw h₁ at hy, exact not_lt_of_ge hy hz },
      { exact f_map_result_coherent β γ hβ hγ z y (h_lt z _) (h_lt y _) z le_rfl _ } } }
end

/-- The core of the definition for the f-maps. This is essentially the definition as in the
blueprint, except that it is defined as a function from `μ` to `f_map_result` instead of from
tangles to litters. This gives two benefits:
1. We preserve the hypotheses of the construction. This allows us to easily derive properties of the
  `f_map` function later.
2. Given the conversion functions in `phase_1a`, it is an easy translation into the true `f_map`
  as required. -/
@[irreducible] noncomputable def f_map_core (β γ : Λ) (hβ : β < α) (hγ : γ < α) :
Π (x : μ), f_map_result β γ hβ hγ x
| x := let f_map_core' := λ (y < x), (f_map_core y).val y le_rfl in begin
  refine mk_f_map_result β γ hβ hγ x (λ y hy, f_map_core y) _,
  by_contradiction, refine lt_irrefl (#μ) (lt_of_le_of_lt _ _),
  -- We need to explicitly specify which intermediate cardinal to use in the transitivity
  -- argument; the elaborator can't determine it at this point.
  exact #{i | (∃ (N : {s // is_near_litter ((β, γ), i) s}),
      of_tangle _ hγ (to_tangle _ _ ⟨((β, γ), i), N⟩) ≤ x)
    ∨ ∃ y (H : y < x), f_map_core' y H = i},

  { convert cardinal.mk_union_le
      {i |
        (∀ N : {s // is_near_litter ⟨⟨β, γ⟩, i⟩ s},
          x < of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, i⟩, N⟩))
        ∧ ∀ y (H : y < x), f_map_core' y H ≠ i }
      ({i | ∃ N : {s // is_near_litter ⟨⟨β, γ⟩, i⟩ s},
          of_tangle _ hγ (to_tangle _ _ ⟨⟨⟨β, γ⟩, i⟩, N⟩) ≤ x}
        ∪ {i | ∃ y (H : y < x), f_map_core' y H = i}) using 1,
    { rw ← cardinal.mk_univ, congr,
      -- This is just basic logic and linear arithmetic.
      -- However, we can't close the goal with just `tauto` or `linarith` since both styles of
      -- reasoning are used at once.
      refine (set.eq_univ_of_forall _).symm,
      intro i,
      by_cases h₁ : (∀ N, x < (of_tangle γ hγ) ((to_tangle γ hγ) ⟨((β, γ), i), N⟩))
        ∧ ∀ y (H : y < x), f_map_core' y H ≠ i,
      { left, exact h₁ },
      { right, dsimp,
        rw [not_and_distrib, not_forall] at h₁,
        cases h₁,
        { left, obtain ⟨N, hN⟩ := h₁, exact ⟨N, le_of_not_lt hN⟩ },
        { right, rw not_forall at h₁, obtain ⟨y, hy⟩ := h₁, simp at hy ⊢, exact ⟨y, hy⟩ } } },
    { rw set.not_nonempty_iff_eq_empty at h,
      rw ← cardinal.mk_emptyc_iff at h,
      suffices : f_map_generator hβ hγ x
        (extend_result β γ hβ hγ x (λ (y : μ) (hy : y < x), f_map_core y)) =
        {i : μ | (∀ (N : subtype (is_near_litter ((β, γ), i))),
          x < (of_tangle γ hγ) ((to_tangle γ hγ) ⟨((β, γ), i), N⟩))
          ∧ ∀ (y : μ) (H : y < x), f_map_core' y H ≠ i},
      { rw this at h, rw [h, zero_add, set.union_def], refl },
      unfold f_map_generator, congr } },

  { have inflationary := mk_litters_inflationary_constraint β γ hβ hγ x,
    have inj := mk_litters_inj_constraint β γ hβ hγ x f_map_core',
    refine lt_of_le_of_lt (cardinal.mk_union_le _ _) (cardinal.add_lt_of_lt _ inflationary inj),
    exact κ_regular.aleph_0_le.trans κ_le_μ }
end
using_well_founded { dec_tac := `[assumption] }

/-- The f-maps. -/
@[irreducible] noncomputable def f_map (β γ : Λ) (hβ : β < α) (hγ : γ < α)
(a : tangle α β (coe_lt_coe.2 hβ)) : litter :=
⟨⟨β, γ⟩, (f_map_core β γ hβ hγ (of_tangle _ _ a)).val (of_tangle _ _ a) le_rfl⟩

/-!
The f-maps have a number of useful properties.
This is `f-map-properties` in the blueprint.
TODO: Once these properties have all been proven, we can be (relatively) certain that the definition
of `f_map` is correct.
-/

local attribute [semireducible] f_map_core f_map

lemma f_map_core_injective (β γ : Λ) (hβ : β < α) (hγ : γ < α) :
function.injective $ λ x, (f_map_core β γ hβ hγ x).val x le_rfl :=
begin
  intros i j h,
  wlog : i ≤ j using i j,
  dsimp at h,
  by_contradiction i_ne_j,
  have i_lt_j := lt_of_le_of_ne case i_ne_j,
  have snd := (f_map_core β γ hβ hγ j).property.some.snd j le_rfl,
  simp_rw subtype.val_eq_coe at snd,
  rw snd at h,
  have := set.nonempty.some_mem ((f_map_core β γ hβ hγ j).property.some.fst j le_rfl),
  dsimp at this, rw ← h at this, unfold f_map_generator at this, simp at this,
  exact this.right i i_lt_j (f_map_result_coherent β γ hβ hγ _ _ _ _ _ _ _)
end

lemma f_map_injective (β γ : Λ) (hβ : β < α) (hγ : γ < α) : function.injective $ f_map β γ hβ hγ :=
begin
  intros i j h,
  unfold f_map at h, simp at h,
  exact (of_tangle β hβ).inj' (f_map_core_injective β γ hβ hγ h)
end

lemma f_map_range (β γ : Λ) (hβ : β < α) (hγ : γ < α) (x : tangle α β (coe_lt_coe.2 hβ)) :
(f_map β γ hβ hγ x).fst = ⟨β, γ⟩ := rfl

/-- The f-maps have disjoint ranges; that is, for each choice of pair `(β, γ)`, the range of `f_map`
is disjoint. -/
lemma f_map_disjoint : pairwise (@disjoint (set litter) _ _ on
  (λ ⟨β, γ⟩, set.range (f_map β.val γ.val β.property γ.property)
    : {β // β < α} × {γ // γ < α} → set litter)) :=
begin
  rintros ⟨β₁, γ₁⟩ ⟨β₂, γ₂⟩ hne N hN,
  simp at hN ⊢,
  refine hne _,
  obtain ⟨⟨x₁, hN₁⟩, ⟨x₂, hN₂⟩⟩ := hN,
  have h₁ : N.fst = ⟨β₁, γ₁⟩ := by { rw ← hN₁, exact f_map_range _ _ _ _ _ },
  have h₂ : N.fst = ⟨β₂, γ₂⟩ := by { rw ← hN₂, exact f_map_range _ _ _ _ _ },
  rw h₁ at h₂, simp at h₂, obtain ⟨β_eq, γ_eq⟩ := h₂,
  simp, refine ⟨_, _⟩; ext; assumption,
end

lemma f_map_position_raising (β γ : Λ) (hβ : β < α) (hγ : γ < α) (x : tangle α β (coe_lt_coe.2 hβ))
(N : set atom) (hN : is_near_litter (f_map β γ hβ hγ x) N) :
of_tangle β hβ x < of_tangle γ hγ (to_tangle γ hγ ⟨f_map β γ hβ hγ x, N, hN⟩) := sorry

end con_nf
