import phase1.basic

/-!
# f-maps

Consider a code `(β, γ, G)`. We are interested in the alternative extensions of this object at
different proper type indices `δ : Λ`. We will define the function `A_δ` which will map the code
`(β, γ, G)` to a new code `(α, δ, D)`. The elements of `D` are produced by the so-called f-maps.
In particular, elements of `D` are of the form `typed_near_litter M` where `M` is a near-litter to
some litter `N`, which in turn is given by an f-map.
-/

open cardinal function set with_bot
open_locale cardinal

universe u

namespace con_nf

section choose_wf

/-!
We construct the f-maps by first defining the auxiliary function `choose_wf`.

Suppose we wish to construct a function `f : α → β` with the constraint that for each `α`,
there is a predefined set of "denied" `β` values that it cannot take. Under some restrictions
based on the cardinalities of the denied set, we can construct such a function.
We can in addition require that `f` be injective if `α` has a well-order, which we will assume here.

The f-maps that we will construct indeed satisfy these conditions.
-/

variables {α β : Type u} {r : α → α → Prop}

/-- Noncomputably chooses an element of `β \ s`, given `#s < #β`. -/
noncomputable def some_of_mk_lt (s : set β) (h : #s < #β) : β :=
(nonempty_compl_of_mk_lt_mk h).some

lemma some_of_mk_lt_spec {s : set β} {h : #s < #β} : some_of_mk_lt s h ∉ s :=
(nonempty_compl_of_mk_lt_mk h).some_spec

lemma mk_image₂_le {p : α → Prop} (f : Π x, p x → β) : #{y // ∃ z h, f z h = y} ≤ #{x // p x} :=
⟨⟨λ y, ⟨y.prop.some, y.prop.some_spec.some⟩, begin
  intros y₁ y₂ h,
  simp only at h,
  have := y₁.prop.some_spec.some_spec,
  simp_rw h at this,
  rw y₂.prop.some_spec.some_spec at this,
  simp only [subtype.coe_inj] at this,
  exact this.symm,
end⟩⟩

noncomputable def choose_wf_core (deny : α → set β)
  (h : ∀ x, #{y // r y x} + #(deny x) < #β) (x : α) (f : Π (y : α), r y x → β) : β :=
begin
  refine some_of_mk_lt ({z | ∃ y h, f y h = z} ∪ deny x) _,
  refine lt_of_le_of_lt (mk_union_le _ _) _,
  exact lt_of_le_of_lt (add_le_add_right (mk_image₂_le _) _) (h x),
end

lemma choose_wf_core_spec {deny : α → set β}
  {h : ∀ x, #{y // r y x} + #(deny x) < #β} (x : α) (f : Π (y : α), r y x → β) :
  choose_wf_core deny h x f ∉ {z | ∃ y h, f y h = z} ∪ deny x :=
some_of_mk_lt_spec

/-- Constructs an injective function `f` such that `f x ∉ deny x`. -/
noncomputable def choose_wf [hwf : is_well_order α r] (deny : α → set β)
  (h : ∀ x, #{y // r y x} + #(deny x) < #β) : α → β :=
hwf.to_is_well_founded.wf.fix (choose_wf_core deny h)

lemma choose_wf_spec [hwf : is_well_order α r] {deny : α → set β}
  {h : ∀ x, #{y // r y x} + #(deny x) < #β} (x : α) :
  choose_wf deny h x ∉ ({z | ∃ y (hy : r y x), choose_wf deny h y = z} ∪ deny x) :=
begin
  rw [choose_wf, well_founded.fix_eq],
  exact choose_wf_core_spec x _,
end

lemma choose_wf_not_mem_deny [is_well_order α r] {deny : α → set β}
  {h : ∀ x, #{y // r y x} + #(deny x) < #β} (x : α) : choose_wf deny h x ∉ deny x :=
λ h', choose_wf_spec x (mem_union_right _ h')

lemma choose_wf_ne_of_r [is_well_order α r] {deny : α → set β}
  {h : ∀ x, #{y // r y x} + #(deny x) < #β} (x₁ x₂ : α) (hx : r x₁ x₂) :
    choose_wf deny h x₁ ≠ choose_wf deny h x₂ :=
λ hx', not_mem_subset (subset_union_left _ _) (choose_wf_spec x₂) ⟨x₁, hx, hx'⟩

lemma choose_wf_injective [is_well_order α r] {deny : α → set β}
  {h : ∀ x, #{y // r y x} + #(deny x) < #β} : injective (choose_wf deny h) :=
begin
  intros x₁ x₂ h,
  obtain hx | hx | hx := (is_well_order.is_trichotomous r).trichotomous x₁ x₂,
  { cases choose_wf_ne_of_r x₁ x₂ hx h },
  { exact hx },
  { cases choose_wf_ne_of_r x₂ x₁ hx h.symm },
end

end choose_wf

/-!
We construct the f-maps by constructing a set of image values to deny, and then choosing
arbitrarily from the remaining set. This uses the `choose_wf` results.
The majority of this section is spent proving that the set of values to deny isn't "too large",
such that we could run out of available values for the function.
-/

variables [params.{u}] {β : type_index} {γ : Λ}
  [core_tangle_data β] [positioned_tangle_data β]
  [position_data.{}] [core_tangle_data γ]
  [positioned_tangle_data γ] [almost_tangle_data γ]
  (hβγ : β ≠ γ)

/-- The requirements to be satisfied by the f-maps.
If `f_map_condition` applied to a litter indexed by `i` is true,
then `i` is *not* a valid output to `f_map x`. -/
inductive f_map_condition (x : tangle β) (i : μ) : Prop
| any (N : set atom) (hN : is_near_litter ⟨i, β, γ, hβγ⟩ N) :
  position (typed_near_litter ⟨⟨i, β, γ, hβγ⟩, N, hN⟩ : tangle γ) ≤ position x →
  f_map_condition
| bot (a : atom) :
  β = ⊥ → -- this condition should only trigger for type `-1`
  a == x → -- using `heq` instead of induction on `β` or the instance deals with many annoyances
  position (typed_near_litter (litter.to_near_litter ⟨i, ⊥, γ, bot_ne_coe⟩) : tangle γ) ≤
    typed_atom_position a →
  f_map_condition

instance : is_well_order (tangle β) (inv_image (<) position) :=
begin
  refine { .. },
  { intros x y,
    have := lt_trichotomy (position x) (position y),
    rw embedding_like.apply_eq_iff_eq at this,
    exact this },
  { intros x y z,
    exact lt_trans },
  { exact inv_image.wf _ μwf.wf },
end

variable (γ)

lemma mk_inv_image_lt (x : tangle β) : #{y // inv_image (<) position y x} < #μ :=
begin
  refine lt_of_le_of_lt _ (show #{y // y < position x} < #μ, from card_Iio_lt _),
  refine ⟨⟨λ y, ⟨_, y.prop⟩, _⟩⟩,
  intros y₁ y₂ h,
  simp only [embedding_like.apply_eq_iff_eq, subtype.coe_inj] at h,
  exact h,
end

lemma mk_inv_image_le (x : tangle β) : #{y : tangle γ // position y ≤ position x} < #μ :=
begin
  refine lt_of_le_of_lt _ (show #{y // y ≤ position x} < #μ, from card_Iic_lt _),
  refine ⟨⟨λ y, ⟨_, y.prop⟩, _⟩⟩,
  intros y₁ y₂ h,
  simp only [embedding_like.apply_eq_iff_eq, subtype.coe_inj] at h,
  exact h,
end

variable {γ}

lemma mk_f_map_deny (hβγ : β ≠ γ) (x : tangle β) :
  #{y // inv_image (<) position y x} + #{i // f_map_condition hβγ x i} < #μ :=
begin
  have h₁ := mk_inv_image_lt x,
  have h₂ : #{i // f_map_condition hβγ x i} < #μ,
  { have : ∀ i, f_map_condition hβγ x i →
      (∃ (N : set atom) (hN : is_near_litter ⟨i, β, γ, hβγ⟩ N),
        position (typed_near_litter ⟨_, N, hN⟩ : tangle γ) ≤ position x) ∨
      β = ⊥ ∧ ∃ (a : atom), a == x ∧
        position (typed_near_litter (litter.to_near_litter ⟨i, β, γ, hβγ⟩) : tangle γ) ≤
          typed_atom_position a,
    { intros i hi,
      obtain ⟨N, hN₁, hN₂⟩ | ⟨a, h₁, h₂, h₃⟩ := hi,
      { left, exact ⟨N, hN₁, hN₂⟩ },
      { right, refine ⟨h₁, a, h₂, _⟩, simp_rw h₁, exact h₃ } },
    refine lt_of_le_of_lt (mk_subtype_mono this) _,
    refine lt_of_le_of_lt (mk_union_le _ _) _,
    refine add_lt_of_lt μ_strong_limit.is_limit.aleph_0_le _ _,
    { refine lt_of_le_of_lt _ (mk_inv_image_le γ x),
      refine ⟨⟨λ i, ⟨_, i.prop.some_spec.some_spec⟩, _⟩⟩,
      intros i j h,
      simp only [embedding_like.apply_eq_iff_eq] at h,
      exact subtype.coe_inj.mp h.1.1 },
    { by_cases β = ⊥ ∧ ∃ (a : atom), a == x,
      { obtain ⟨hβ, a, hax⟩ := h,
        refine lt_of_le_of_lt _ (card_Iic_lt (typed_atom_position a)),
        refine ⟨⟨λ i, ⟨position
          (typed_near_litter (litter.to_near_litter ⟨i, β, γ, hβγ⟩) : tangle γ), _⟩, _⟩⟩,
        { obtain ⟨i, _, b, hb, _⟩ := i,
          rw eq_of_heq (hax.trans hb.symm),
          assumption },
        { intros i j h,
          simp only [subtype.mk_eq_mk, embedding_like.apply_eq_iff_eq,
            litter.to_near_litter_injective.eq_iff] at h,
          exact subtype.coe_inj.mp h.1 } },
      { refine lt_of_eq_of_lt _ (lt_of_lt_of_le aleph_0_pos μ_strong_limit.is_limit.aleph_0_le),
        rw [mk_eq_zero_iff, is_empty_coe_sort, set.eq_empty_iff_forall_not_mem],
        rintros i ⟨hb, a, ha, _⟩,
        exact h ⟨hb, a, ha⟩ } } },
  exact add_lt_of_lt μ_strong_limit.is_limit.aleph_0_le h₁ h₂,
end

/-!
We're done with proving technical results, now we can define the f-maps.
-/

/-- The f-maps. -/
noncomputable def f_map (x : tangle β) : litter :=
⟨choose_wf (f_map_condition hβγ) (mk_f_map_deny hβγ) x, β, γ, hβγ⟩

@[simp] lemma f_map_β (x : tangle β) : (f_map hβγ x).β = β := rfl
@[simp] lemma f_map_γ (x : tangle β) : (f_map hβγ x).γ = γ := rfl

lemma f_map_injective : injective (f_map hβγ) :=
begin
  intros x y h,
  simp only [f_map, choose_wf_injective.eq_iff, eq_self_iff_true, and_true] at h,
  exact h,
end

lemma f_map_not_mem_deny (x : tangle β) : (f_map hβγ x).ν ∉ {i | f_map_condition hβγ x i} :=
choose_wf_not_mem_deny x

lemma f_map_position (x : tangle β) (N : set atom) (h : is_near_litter (f_map hβγ x) N) :
  position x < position (typed_near_litter ⟨_, N, h⟩ : tangle γ) :=
begin
  have := f_map_not_mem_deny hβγ x,
  contrapose! this,
  unfreezingI { induction β using with_bot.rec_bot_coe };
  exact f_map_condition.any _ h this,
end

lemma typed_atom_position_lt_f_map (x : tangle ⊥) :
  typed_atom_position x <
  position (typed_near_litter
    (f_map (bot_ne_coe : (⊥ : type_index) ≠ γ) x).to_near_litter : tangle γ) :=
begin
  have := f_map_not_mem_deny (bot_ne_coe : (⊥ : type_index) ≠ γ) x,
  contrapose! this,
  exact f_map_condition.bot x rfl heq.rfl this,
end

end con_nf
