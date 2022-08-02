import phase1.basic

/-!
# f-maps

Consider a code `(α, γ, G)`. We are interested in the alternative extensions of this object at
different proper type indices `δ : Λ`. We will define the function `A_δ` which will map the code
`(α, γ, G)` to a new code `(α, δ, D)`. The elements of `D` are produced by the so-called f-maps.
In particular, elements of `D` are of the form `to_tangle M` where `M` is a near-litter to some
litter `N`, which in turn is given by an f-map.
-/

open cardinal function set with_bot
open_locale cardinal

universe u

namespace con_nf
variables [params.{u}] (α : type_index) (β : Λ) [core_tangle_data α] [positioned_tangle_data α]
variables [core_tangle_data β] [positioned_tangle_data β] [almost_tangle_data β] [tangle_data β]

/-!
We now define the f-maps. We will do so in two stages; first, we define it as a function `μ → μ`,
(named `f_map_core`) and then raise it to be litter-valued and defined on tangles. This allows some
nicer definitional properties, such as that the resulting litter is of the form `⟨⟨α, β⟩, χ⟩` for
`χ : μ`.

The value of an f-map is defined as a litter that satisfies two conditions, the second and third
bullet points on the blueprint (the first is a type-level condition that the resulting litter is of
the form `⟨⟨α, β⟩, χ⟩`). In order to show that the f-maps are well-defined, we show that this set of
candidate litters is non-empty. In particular, the set of all possible litters has size `μ`, and
each constraint only removes `< μ` elements from this candidate set.

The following two lemmas will prove that for each constraint, we remove less than `μ` litters from
our pool of potential litters.
-/

local attribute [semireducible] litter

lemma mk_litters_inflationary_constraint' (x : μ) :
  #{N : (Σ i, {s // is_near_litter ⟨⟨α, β⟩, i⟩ s}) |
    position (to_tangle ⟨⟨⟨α, β⟩, N.fst⟩, N.snd⟩ : tangle β) ≤ x} < #μ :=
begin
  refine (mk_le_of_injective _).trans_lt (card_Iic_lt x),
  { exact λ N, ⟨position (to_tangle ⟨⟨⟨α, β⟩, N.1.1⟩, N.1.2⟩), N.2⟩ },
  rintro ⟨⟨i, N⟩, hN⟩ ⟨⟨j, M⟩, hM⟩ h,
  simp only [subtype.mk_eq_mk, embedding_like.apply_eq_iff_eq, prod.mk.inj_iff, eq_self_iff_true,
    true_and] at h,
  obtain ⟨rfl, rfl⟩ := h,
  refl,
end

/-- One of the constraints in defining the f-maps is that for all near-litters to the result litter
`N`, they are positioned higher than `x` in `μ` (under `to_tangle`). We show that there are less
than `μ` litters that do *not* satisfy this constraint. -/
lemma mk_litters_inflationary_constraint (x : μ) :
  #{i : μ | ∃ N : {s // is_near_litter ⟨⟨α, β⟩, i⟩ s},
    position (to_tangle ⟨⟨⟨α, β⟩, i⟩, N⟩ : tangle β) ≤ x} < #μ :=
begin
  suffices : #{i : μ | ∃ N : {s // is_near_litter ⟨⟨α, β⟩, i⟩ s},
    position (to_tangle ⟨⟨⟨α, β⟩, i⟩, N⟩) ≤ x}
    ≤ #{N : (Σ i, {s // is_near_litter ⟨⟨α, β⟩, i⟩ s}) |
    position (to_tangle ⟨⟨⟨α, β⟩, N.fst⟩, N.snd⟩) ≤ x},
  { exact this.trans_lt (mk_litters_inflationary_constraint' _ _ _) },
  refine ⟨⟨λ i, ⟨⟨i, i.2.some⟩, i.2.some_spec⟩, _⟩⟩,
  rintro ⟨i, N, hN⟩ ⟨j, M, hM⟩ hij,
  simp_rw subtype.mk_eq_mk at hij ⊢,
  exact hij.1,
end

/-- Only `< μ` elements of `μ` have been hit so far by f_map_core. -/
lemma mk_litters_inj_constraint (x : μ) (f_map_core : Π (y < x), μ) :
  #{i : μ | ∃ y < x, f_map_core y ‹_› = i} < #μ :=
begin
  have : {i | ∃ y < x, f_map_core y ‹_› = i}
    = {i | ∃ (y : {y // y < x}), f_map_core y.val y.property = i} := by simp_rw subtype.exists,
  rw this,
  exact mk_range_le.trans_lt (card_Iio_lt x),
end

/-!
To keep track of the hypotheses that went into creating the f-maps, we create a few structures to
store the result of the f-map as well as the conditions on their values.
These definitions are private so that we just use the intended properties of the f-maps, instead of
their internal structure.
-/

private def f_map_generator (x : μ) (R : Π y < x, μ) : set μ :=
{i | (∀ N : {s // is_near_litter ⟨⟨α, β⟩, i⟩ s},
  x < position (to_tangle ⟨⟨⟨α, β⟩, i⟩, N⟩ : tangle β))
    ∧ ∀ y (H : y < x), R y H ≠ i}

private def pre_f_map_result_is_viable (x : μ) (R : Π y < x, μ) : Prop :=
∀ y ≤ x, (f_map_generator α β y $ λ z hz, R z $ hz.trans_le H).nonempty

private def pre_f_map_result_is_allowed (x : μ) (R : Π y ≤ x, μ) :=
Σ' hv : pre_f_map_result_is_viable α β x (λ z hz, R z hz.le), ∀ y ≤ x, R y ‹_› = (hv y ‹_›).some

private def f_map_result (x : μ) : Type u :=
{R : Π y ≤ x, μ // nonempty (pre_f_map_result_is_allowed α β x R)}

private def extend_result (x : μ) (h_lt : Π y < x, f_map_result α β y) : Π y < x, μ :=
λ y hy, (h_lt y hy).val y le_rfl

/-- By construction, all the `f_map_result`s have matching output values, where they are defined. -/
private lemma f_map_result_coherent (x y : μ) (fx : f_map_result α β x) (fy : f_map_result α β y) :
  Π (z : μ), z ≤ x → z ≤ y → fx.val z ‹_› = fy.val z ‹_›
| z hzx hzy := begin
  rw (fx.property.some).snd z hzx,
  rw (fy.property.some).snd z hzy,
  congr' with w hw,
  exact f_map_result_coherent w _ _,
end
using_well_founded { dec_tac := `[exact psigma.lex.left _ _ ‹_›] }

/-- We can recursively construct the (unique) `f_map_result` for arbitrary `x`. -/
private noncomputable def mk_f_map_result (x : μ) (h_lt : Π y < x, f_map_result α β y)
  (hx : (f_map_generator α β x $ extend_result α β x h_lt).nonempty) :
  f_map_result α β x :=
⟨λ y hy, dite (x = y) (λ h, hx.some) (λ h, (h_lt y $ hy.lt_of_ne' h).val y le_rfl),
⟨⟨λ y hy, begin
  by_cases x = y,
  { subst h,
    convert hx,
    unfold extend_result,
    ext z hz,
    rw dif_neg hz.ne' },
  { convert (h_lt y $ hy.lt_of_ne' h).prop.some.fst y le_rfl,
    ext z hz,
    dsimp,
    rw dif_neg (hz.trans_le hy).ne',
    exact f_map_result_coherent α β z y (h_lt z _) (h_lt y _) z le_rfl _ }
end, λ y hy, begin
  dsimp,
  split_ifs,
  { subst h,
    congr' with z hz,
    rw dif_neg hz.ne',
    refl },
  { convert ((h_lt y _).prop.some).snd y le_rfl,
    ext z hz, split_ifs with h₁,
    { exfalso, rw h₁ at hy, exact not_lt_of_ge hy hz },
    { exact f_map_result_coherent α β z y (h_lt z _) (h_lt y _) z le_rfl _ } }
end⟩⟩⟩

/-- The core of the definition for the f-maps. This is essentially the definition as in the
blueprint, except that it is defined as a function from `μ` to `f_map_result` instead of from
tangles to litters. This gives two benefits:
1. We preserve the hypotheses of the construction. This allows us to easily derive properties of the
  `f_map` function later.
2. Given the conversion functions in `tangle_data`, it is an easy translation into the true `f_map`
  as required. -/
noncomputable def f_map_core : Π (x : μ), f_map_result α β x
| x := let f_map_core' := λ (y < x), (f_map_core y).val y le_rfl in begin
  refine mk_f_map_result α β x (λ y hy, f_map_core y)
    (ne_empty_iff_nonempty.1 $ λ h, lt_irrefl (#μ) $ lt_of_eq_of_lt _ _),
  -- We need to explicitly specify which intermediate cardinal to use in the transitivity
  -- argument; the elaborator can't determine it at this point.
  exact #{i | (∃ N, position (to_tangle ⟨((α, β), i), N⟩ : tangle β) ≤ x)
    ∨ ∃ y H, f_map_core' y H = i},
  { rw ←mk_univ,
    congr,
    rw [eq_comm, ←compl_eq_empty],
    simp_rw [compl_set_of, not_or_distrib, not_exists, not_le],
    exact h },
  { exact (mk_union_le _ _).trans_lt (add_lt_of_lt (κ_regular.aleph_0_le.trans κ_le_μ)
      (mk_litters_inflationary_constraint α β x) $ mk_litters_inj_constraint x f_map_core') }
end
using_well_founded { dec_tac := `[assumption] }

private lemma f_map_core_injective : injective $ λ x, (f_map_core α β x).val x le_rfl :=
begin
  intros i j h,
  wlog : i ≤ j using i j,
  dsimp at h,
  by_contradiction i_ne_j,
  have i_lt_j := lt_of_le_of_ne case i_ne_j,
  have snd := (f_map_core α β j).prop.some.snd j le_rfl,
  simp_rw subtype.val_eq_coe at snd,
  rw snd at h,
  have := set.nonempty.some_mem ((f_map_core α β j).prop.some.fst j le_rfl),
  dsimp at this,
  rw ← h at this,
  unfold f_map_generator at this,
  simp at this,
  exact this.right i i_lt_j (f_map_result_coherent α β _ _ _ _ _ _ _),
end

private lemma f_map_core_position_raising (x : μ) (N : set atom)
  (hN : is_near_litter ⟨⟨α, β⟩, (f_map_core α β x).val x le_rfl⟩ N) :
  x < position (to_tangle ⟨⟨⟨α, β⟩, (f_map_core α β x).val x le_rfl⟩, N, hN⟩ : tangle β) :=
begin
  have snd := (f_map_core α β x).prop.some.snd x le_rfl,
  have := set.nonempty.some_mem ((f_map_core α β x).prop.some.fst x le_rfl),
  rw ← snd at this,
  exact this.left _,
end

variables {α}

/-- The f-maps. -/
noncomputable def f_map (a : tangle α) : litter :=
⟨⟨α, β⟩, (f_map_core α β (position a)).val (position a) le_rfl⟩

/-!
The f-maps have a number of useful properties.
This is `f-map-properties` in the blueprint.
Now that these properties have all been proven, we can be (relatively) certain that the definition
of `f_map` is correct.
-/

lemma f_map_injective : injective (f_map β : tangle α → litter) :=
λ i j h, position.inj' $ f_map_core_injective α β (prod.ext_iff.1 h).2

variable (α)
@[simp] lemma f_map_fst (x : tangle α) : (f_map β x).fst = (α, β) := rfl
variable {α}

lemma f_map_range_eq {α₁ α₂ : type_index} [core_tangle_data α₁] [positioned_tangle_data α₁]
  [core_tangle_data α₂] [positioned_tangle_data α₂] {x : tangle α₁} {y : tangle α₂}
  (h : f_map β x = f_map β y) : α₁ = α₂ :=
congr_arg (prod.fst ∘ prod.fst) h

lemma f_map_position_raising (x : tangle α) (N : set atom) (hN : is_near_litter (f_map β x) N) :
  position x < position (to_tangle ⟨f_map β x, N, hN⟩ : tangle β) :=
f_map_core_position_raising α β (position x) N hN

end con_nf
