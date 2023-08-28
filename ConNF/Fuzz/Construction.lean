import ConNF.Fuzz.Hypotheses

/-!
# Constructing the `fuzz` map

In tangled type theory, a given model element has extensions at each level below it.
We have a "preferred" extension, and must find a way to compute the other extensions from that
information. In order to do this, we need to be able to convert arbitrary model elements into
"junk" at other levels, which can then be clearly interpreted as a "non-preferred" extension.

The `fuzz` maps perform this task. They are parametrised by a pair of type indices, representing
the source type level and target type level. At each pair of levels, the `fuzz` map is an injection
from tangles to litters. An arbitrary litter can only be the image of a `fuzz` map defined at a
single pair of type levels.

Treating the output of a `fuzz` map as a typed near-litter, its position is always greater than
the position of the input to the function. This ensures a well-foundedness condition that we use
in many places later.

## Main declarations

* `ConNF.fuzz`: Converts a tangle into a "junk" litter.
-/

open Cardinal Function Set WithBot

open scoped Cardinal

universe u

namespace ConNF

section ChooseWf

/-!
We construct the `fuzz` map by first defining the auxiliary function `chooseWf`.

Suppose we wish to construct a function `f : α → β` with the constraint that for each `α`,
there is a predefined set of "denied" `β` values that it cannot take. Under some restrictions
based on the cardinalities of the denied set, we can construct such a function. We can in addition
require that `f` be injective if `α` has a well-order, which we will assume here.

The `fuzz` map that we will construct indeed satisfies these conditions.
-/

variable {α β : Type u} {r : α → α → Prop}

/-- Noncomputably chooses an element of `β \ s`, given `#s < #β`. -/
noncomputable def someOfMkLt (s : Set β) (h : #s < #β) : β :=
  (nonempty_compl_of_mk_lt_mk h).choose

theorem someOfMkLt_spec {s : Set β} {h : #s < #β} : someOfMkLt s h ∉ s :=
  (nonempty_compl_of_mk_lt_mk h).choose_spec

theorem mk_image₂_le {p : α → Prop} (f : ∀ x, p x → β) :
    #{ y // ∃ z h, f z h = y } ≤ #{ x // p x } :=
  ⟨⟨fun y => ⟨y.prop.choose, y.prop.choose_spec.choose⟩, by
    intro y₁ y₂ h
    simp only [Subtype.mk.injEq] at h
    have := y₂.prop.choose_spec.choose_spec
    simp_rw [← h] at this
    rw [y₁.prop.choose_spec.choose_spec] at this
    simp only [Subtype.coe_inj] at this
    exact this⟩⟩

noncomputable def chooseWfCore (deny : α → Set β) (h : ∀ x, #{ y // r y x } + #(deny x) < #β)
    (x : α) (f : ∀ y : α, r y x → β) : β :=
  someOfMkLt ({z | ∃ y h, f y h = z} ∪ deny x)
    (lt_of_le_of_lt (mk_union_le _ _) (lt_of_le_of_lt (add_le_add_right (mk_image₂_le _) _) (h x)))

theorem chooseWfCore_spec {deny : α → Set β} {h : ∀ x, #{ y // r y x } + #(deny x) < #β} (x : α)
    (f : ∀ y : α, r y x → β) :
    chooseWfCore deny h x f ∉ {z | ∃ y h, f y h = z} ∪ deny x :=
  someOfMkLt_spec

/-- Constructs an injective function `f` such that `f x ∉ deny x`. -/
noncomputable def chooseWf [hwf : IsWellOrder α r] (deny : α → Set β)
    (h : ∀ x, #{ y // r y x } + #(deny x) < #β) : α → β :=
  hwf.toIsWellFounded.wf.fix (chooseWfCore deny h)

theorem chooseWf_spec [hwf : IsWellOrder α r] {deny : α → Set β}
    {h : ∀ x, #{ y // r y x } + #(deny x) < #β} (x : α) :
    chooseWf deny h x ∉ {z | ∃ (y : _) (_ : r y x), chooseWf deny h y = z} ∪ deny x := by
  rw [chooseWf, WellFounded.fix_eq]
  exact chooseWfCore_spec x _

theorem chooseWf_not_mem_deny [IsWellOrder α r] {deny : α → Set β}
    {h : ∀ x, #{ y // r y x } + #(deny x) < #β} (x : α) : chooseWf deny h x ∉ deny x :=
  fun h' => chooseWf_spec x (mem_union_right _ h')

theorem chooseWf_ne_of_r [_inst : IsWellOrder α r] {deny : α → Set β}
    {h : ∀ x, #{ y // r y x } + #(deny x) < #β} (x₁ x₂ : α) (hx : r x₁ x₂) :
    chooseWf deny h x₁ ≠ chooseWf deny h x₂ := fun hx' =>
  not_mem_subset (subset_union_left _ _) (chooseWf_spec x₂) ⟨x₁, hx, hx'⟩

theorem chooseWf_injective [inst : IsWellOrder α r] {deny : α → Set β}
    {h : ∀ x, #{ y // r y x } + #(deny x) < #β} : Injective (chooseWf deny h) := by
  intro x₁ x₂ h
  obtain hx | hx | hx := @lt_trichotomy _ (IsWellOrder.linearOrder r) x₁ x₂
  · cases chooseWf_ne_of_r (_inst := inst) x₁ x₂ hx h
  · exact hx
  · cases chooseWf_ne_of_r (_inst := inst) x₂ x₁ hx h.symm

end ChooseWf

/-!
We construct the `fuzz` maps by constructing a set of image values to deny, and then choosing
arbitrarily from the remaining set. This uses the `chooseWf` results.

The majority of this section is spent proving that the set of values to deny isn't "too large",
such that we could run out of available values for the function.
-/

variable [Params.{u}] {β : TypeIndex} {γ : Λ} [TangleData β] [PositionFunction β]
  [BasePositions] [TangleData γ] [PositionFunction γ] [TypedObjects γ] (hβγ : β ≠ γ)

/-- The requirements to be satisfied by the f-maps.
If `FuzzCondition` applied to a litter indexed by `ν` is true,
then `ν` is *not* a valid output to `fuzz _ t`. -/
inductive FuzzCondition (x : Tangle β) (ν : μ) : Prop
  | any (N : Set Atom) (hN : IsNearLitter ⟨ν, β, γ, hβγ⟩ N) :
    position (typedNearLitter ⟨⟨ν, β, γ, hβγ⟩, N, hN⟩ : Tangle γ) ≤ position x → FuzzCondition x ν
  | bot (a : Atom) :
      β = ⊥ →   -- this condition should only trigger for type `⊥`
      HEq a x → -- using `HEq` instead of induction on `β` or the instance deals with some problems
      position (typedNearLitter (Litter.toNearLitter ⟨ν, ⊥, γ, bot_ne_coe⟩) : Tangle γ) ≤
        typedAtomPosition a →
      FuzzCondition x ν

instance : IsWellOrder (Tangle β) (InvImage (· < ·) position) := by
  refine' { .. }
  · intro t₁ t₂
    have := lt_trichotomy (position t₁) (position t₂)
    rw [EmbeddingLike.apply_eq_iff_eq] at this
    exact this
  · intro t₁ t₂ t₃
    exact lt_trans
  · exact InvImage.wf _ μwo.wf

variable (γ)

theorem mk_invImage_lt (t : Tangle β) : #{ y // InvImage (· < ·) position y t } < #μ := by
  refine lt_of_le_of_lt ?_ (show #{ ν // ν < position t } < #μ from card_Iio_lt _)
  refine ⟨⟨fun y => ⟨_, y.prop⟩, ?_⟩⟩
  intro y₁ y₂ h
  simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Subtype.coe_inj] at h
  exact h

theorem mk_invImage_le (t : Tangle β) : #{ t' : Tangle γ // position t' ≤ position t } < #μ := by
  refine lt_of_le_of_lt ?_ (show #{ ν // ν ≤ position t } < #μ from card_Iic_lt _)
  refine ⟨⟨fun t' => ⟨_, t'.prop⟩, ?_⟩⟩
  intro y₁ y₂ h
  simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Subtype.coe_inj] at h
  exact h

variable {γ}

theorem mk_fuzz_deny (hβγ : β ≠ γ) (t : Tangle β) :
    #{ t' // InvImage (· < ·) position t' t } + #{ ν // FuzzCondition hβγ t ν } < #μ := by
  have h₁ := mk_invImage_lt t
  suffices h₂ : #{ ν // FuzzCondition hβγ t ν } < #μ
  · exact add_lt_of_lt μ_isStrongLimit.isLimit.aleph0_le h₁ h₂
  have : ∀ ν, FuzzCondition hβγ t ν →
    (∃ (N : Set Atom) (hN : IsNearLitter ⟨ν, β, γ, hβγ⟩ N),
        position (typedNearLitter ⟨_, N, hN⟩ : Tangle γ) ≤ position t) ∨
    (β = ⊥ ∧ ∃ a : Atom, HEq a t ∧
    position (typedNearLitter (Litter.toNearLitter ⟨ν, β, γ, hβγ⟩) : Tangle γ) ≤
      typedAtomPosition a)
  · intro i hi
    obtain ⟨N, hN₁, hN₂⟩ | ⟨a, h₁, h₂, h₃⟩ := hi
    · left; exact ⟨N, hN₁, hN₂⟩
    · right; refine' ⟨h₁, a, h₂, _⟩; simp_rw [h₁]; exact h₃
  refine lt_of_le_of_lt (mk_subtype_mono this) ?_
  refine lt_of_le_of_lt (mk_union_le _ _) ?_
  refine add_lt_of_lt μ_isStrongLimit.isLimit.aleph0_le ?_ ?_
  · refine lt_of_le_of_lt ?_ (mk_invImage_le γ t)
    refine ⟨⟨fun i => ⟨_, i.prop.choose_spec.choose_spec⟩, ?_⟩⟩
    intro i j h
    simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    apply_fun Sigma.fst at h
    simp only [Litter.mk.injEq, Subtype.coe_inj, and_self, and_true] at h
    exact h
  · by_cases β = ⊥ ∧ ∃ a : Atom, HEq a t
    · obtain ⟨_, a, hax⟩ := h
      refine lt_of_le_of_lt ?_ (card_Iic_lt (typedAtomPosition a))
      refine ⟨⟨fun i => ⟨position (typedNearLitter
        (Litter.toNearLitter ⟨i, β, γ, hβγ⟩) : Tangle γ), ?_⟩, ?_⟩⟩
      · obtain ⟨ν, _, b, hb, _⟩ := i
        rw [eq_of_heq (hax.trans hb.symm)]
        assumption
      · intro i j h
        simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
          Litter.toNearLitter_injective.eq_iff,
          Litter.mk.injEq, Subtype.coe_inj, and_self, and_true] at h
        exact h
    · refine' lt_of_eq_of_lt _ (lt_of_lt_of_le aleph0_pos μ_isStrongLimit.isLimit.aleph0_le)
      rw [mk_eq_zero_iff, isEmpty_coe_sort, Set.eq_empty_iff_forall_not_mem]
      rintro i ⟨hb, a, ha, _⟩
      exact h ⟨hb, a, ha⟩

/-!
We're done with proving technical results, now we can define the `fuzz` maps.
-/

/--
The `fuzz` map for a particular pair of type indices.

In tangled type theory, a given model element has extensions at each level below it.
We have a "preferred" extension, and must find a way to compute the other extensions from that
information. In order to do this, we need to be able to convert arbitrary model elements into
"junk" at other levels, which can then be clearly interpreted as a "non-preferred" extension.

The `fuzz` maps perform this task. They are parametrised by a pair of type indices, representing
the source type level and target type level. At each pair of levels, the `fuzz` map is an injection
from tangles to litters. An arbitrary litter can only be the image of a `fuzz` map defined at a
single pair of type levels.

Treating the output of a `fuzz` map as a typed near-litter, its position is always greater than
the position of the input to the function. This ensures a well-foundedness condition that we use
in many places later.
-/
noncomputable def fuzz (t : Tangle β) : Litter :=
  ⟨chooseWf (FuzzCondition hβγ) (mk_fuzz_deny hβγ) t, β, γ, hβγ⟩

@[simp]
theorem fuzz_β (t : Tangle β) : (fuzz hβγ t).β = β :=
  rfl

@[simp]
theorem fuzz_γ (t : Tangle β) : (fuzz hβγ t).γ = γ :=
  rfl

theorem fuzz_injective : Injective (fuzz hβγ) := by
  intro t₁ t₂ h
  simp only [fuzz, Litter.mk.injEq, chooseWf_injective.eq_iff, and_self, and_true] at h
  exact h

theorem fuzz_not_mem_deny (t : Tangle β) : (fuzz hβγ t).ν ∉ {ν | FuzzCondition hβγ t ν} :=
  chooseWf_not_mem_deny t

theorem fuzz_position' (t : Tangle β) (N : Set Atom) (h : IsNearLitter (fuzz hβγ t) N) :
    position t < position (typedNearLitter ⟨fuzz hβγ t, N, h⟩ : Tangle γ) := by
  have h' := fuzz_not_mem_deny hβγ t
  contrapose! h'
  -- Generalise the instances.
  revert β
  intro β
  induction β using WithBot.recBotCoe <;>
  · intros _ _ hβγ t h h'
    exact FuzzCondition.any _ h h'

theorem fuzz_position (t : Tangle β) (N : NearLitter) (h : N.1 = fuzz hβγ t) :
    position t < position (typedNearLitter N : Tangle γ) := by
  have := fuzz_position' hβγ t N ((NearLitter.isNearLitter _ _).mpr h)
  exact lt_of_lt_of_eq this (congr_arg _ (congr_arg _ (NearLitter.ext rfl)))

theorem typedAtomPosition_lt_fuzz (t : Tangle ⊥) :
  typedAtomPosition t <
    position
      (typedNearLitter (fuzz (bot_ne_coe : (⊥ : TypeIndex) ≠ γ) t).toNearLitter : Tangle γ) := by
  have := fuzz_not_mem_deny (bot_ne_coe : (⊥ : TypeIndex) ≠ γ) t
  contrapose! this
  exact FuzzCondition.bot t rfl HEq.rfl this

end ConNF
