import ConNF.Fuzz.Hypotheses

/-!
# f-maps

Consider a code `(β, γ, G)`. We are interested in the alternative extensions of this object at
different proper type indices `δ : Λ`. We will define the function `A_δ` which will map the code
`(β, γ, G)` to a new code `(α, δ, D)`. The elements of `D` are produced by the so-called f-maps.
In particular, elements of `D` are of the form `typed_near_litter M` where `M` is a near-litter to
some litter `N`, which in turn is given by an f-map.
-/

open Cardinal Function Set WithBot

open scoped Cardinal

universe u

namespace ConNF

section ChooseWf

/-!
We construct the f-maps by first defining the auxiliary function `choose_wf`.

Suppose we wish to construct a function `f : α → β` with the constraint that for each `α`,
there is a predefined set of "denied" `β` values that it cannot take. Under some restrictions
based on the cardinalities of the denied set, we can construct such a function.
We can in addition require that `f` be injective if `α` has a well-order, which we will assume here.

The f-maps that we will construct indeed satisfy these conditions.
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
We construct the f-maps by constructing a set of image values to deny, and then choosing
arbitrarily from the remaining set. This uses the `choose_wf` results.
The majority of this section is spent proving that the set of values to deny isn't "too large",
such that we could run out of available values for the function.
-/


variable [Params.{u}] {β : TypeIndex} {γ : Λ} [TangleData β] [PositionFunction β]
  [BasePositions] [TangleData γ] [PositionFunction γ] [TypedObjects γ] (hβγ : β ≠ γ)

/-- The requirements to be satisfied by the f-maps.
If `fuzz_condition` applied to a litter indexed by `i` is true,
then `i` is *not* a valid output to `fuzz x`. -/
inductive FuzzCondition (x : Tangle β) (i : μ) : Prop
  | any (N : Set Atom) (hN : IsNearLitter ⟨i, β, γ, hβγ⟩ N) :
    position (typedNearLitter ⟨⟨i, β, γ, hβγ⟩, N, hN⟩ : Tangle γ) ≤ position x → FuzzCondition x i
  | bot (a : Atom) :
      β = ⊥ →   -- this condition should only trigger for type `-1`
      HEq a x → -- using `heq` instead of induction on `β` or the instance deals with many annoyances
      position (typedNearLitter (Litter.toNearLitter ⟨i, ⊥, γ, bot_ne_coe⟩) : Tangle γ) ≤
        typedAtomPosition a →
      FuzzCondition x i

instance : IsWellOrder (Tangle β) (InvImage (· < ·) position) := by
  refine' { .. }
  · intro x y
    have := lt_trichotomy (position x) (position y)
    rw [EmbeddingLike.apply_eq_iff_eq] at this
    exact this
  · intro x y z
    exact lt_trans
  · exact InvImage.wf _ μwo.wf

variable (γ)

theorem mk_invImage_lt (x : Tangle β) : #{ y // InvImage (· < ·) position y x } < #μ := by
  refine lt_of_le_of_lt ?_ (show #{ y // y < position x } < #μ from card_Iio_lt _)
  refine ⟨⟨fun y => ⟨_, y.prop⟩, ?_⟩⟩
  intro y₁ y₂ h
  simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Subtype.coe_inj] at h
  exact h

theorem mk_invImage_le (x : Tangle β) : #{ y : Tangle γ // position y ≤ position x } < #μ := by
  refine lt_of_le_of_lt ?_ (show #{ y // y ≤ position x } < #μ from card_Iic_lt _)
  refine ⟨⟨fun y => ⟨_, y.prop⟩, ?_⟩⟩
  intro y₁ y₂ h
  simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Subtype.coe_inj] at h
  exact h

variable {γ}

theorem mk_fuzz_deny (hβγ : β ≠ γ) (x : Tangle β) :
    #{ y // InvImage (· < ·) position y x } + #{ i // FuzzCondition hβγ x i } < #μ := by
  have h₁ := mk_invImage_lt x
  suffices h₂ : #{ i // FuzzCondition hβγ x i } < #μ
  · exact add_lt_of_lt μ_isStrongLimit.isLimit.aleph0_le h₁ h₂
  have : ∀ i, FuzzCondition hβγ x i →
    (∃ (N : Set Atom) (hN : IsNearLitter ⟨i, β, γ, hβγ⟩ N),
        position (typedNearLitter ⟨_, N, hN⟩ : Tangle γ) ≤ position x) ∨
      β = ⊥ ∧
        ∃ a : Atom,
          HEq a x ∧
            position (typedNearLitter (Litter.toNearLitter ⟨i, β, γ, hβγ⟩) : Tangle γ) ≤
              typedAtomPosition a
  · intro i hi
    obtain ⟨N, hN₁, hN₂⟩ | ⟨a, h₁, h₂, h₃⟩ := hi
    · left; exact ⟨N, hN₁, hN₂⟩
    · right; refine' ⟨h₁, a, h₂, _⟩; simp_rw [h₁]; exact h₃
  refine lt_of_le_of_lt (mk_subtype_mono this) ?_
  refine lt_of_le_of_lt (mk_union_le _ _) ?_
  refine add_lt_of_lt μ_isStrongLimit.isLimit.aleph0_le ?_ ?_
  · refine lt_of_le_of_lt ?_ (mk_invImage_le γ x)
    refine ⟨⟨fun i => ⟨_, i.prop.choose_spec.choose_spec⟩, ?_⟩⟩
    intro i j h
    simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    apply_fun Sigma.fst at h
    simp only [Litter.mk.injEq, Subtype.coe_inj, and_self, and_true] at h
    exact h
  · by_cases β = ⊥ ∧ ∃ a : Atom, HEq a x
    · obtain ⟨_, a, hax⟩ := h
      refine lt_of_le_of_lt ?_ (card_Iic_lt (typedAtomPosition a))
      refine ⟨⟨fun i => ⟨position (typedNearLitter
        (Litter.toNearLitter ⟨i, β, γ, hβγ⟩) : Tangle γ), ?_⟩, ?_⟩⟩
      · obtain ⟨i, _, b, hb, _⟩ := i
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
We're done with proving technical results, now we can define the f-maps.
-/

/-- The f-maps. -/
noncomputable def fuzz (x : Tangle β) : Litter :=
  ⟨chooseWf (FuzzCondition hβγ) (mk_fuzz_deny hβγ) x, β, γ, hβγ⟩

@[simp]
theorem fuzz_β (x : Tangle β) : (fuzz hβγ x).β = β :=
  rfl

@[simp]
theorem fuzz_γ (x : Tangle β) : (fuzz hβγ x).γ = γ :=
  rfl

theorem fuzz_injective : Injective (fuzz hβγ) := by
  intro x y h
  simp only [fuzz, Litter.mk.injEq, chooseWf_injective.eq_iff, and_self, and_true] at h
  exact h

theorem fuzz_not_mem_deny (x : Tangle β) : (fuzz hβγ x).ν ∉ {i | FuzzCondition hβγ x i} :=
  chooseWf_not_mem_deny x

theorem fuzz_position' (x : Tangle β) (N : Set Atom) (h : IsNearLitter (fuzz hβγ x) N) :
    position x < position (typedNearLitter ⟨fuzz hβγ x, N, h⟩ : Tangle γ) := by
  have h' := fuzz_not_mem_deny hβγ x
  contrapose! h'
  -- Generalise the instances.
  revert β
  intro β
  induction β using WithBot.recBotCoe <;>
  · intros _ _ hβγ x h h'
    exact FuzzCondition.any _ h h'

theorem fuzz_position (x : Tangle β) (N : NearLitter) (h : N.1 = fuzz hβγ x) :
    position x < position (typedNearLitter N : Tangle γ) := by
  have := fuzz_position' hβγ x N ((NearLitter.isNearLitter _ _).mpr h)
  exact lt_of_lt_of_eq this (congr_arg _ (congr_arg _ (NearLitter.ext rfl)))

theorem typedAtomPosition_lt_fuzz (x : Tangle ⊥) :
  typedAtomPosition x <
    position
      (typedNearLitter (fuzz (bot_ne_coe : (⊥ : TypeIndex) ≠ γ) x).toNearLitter : Tangle γ) := by
  have := fuzz_not_mem_deny (bot_ne_coe : (⊥ : TypeIndex) ≠ γ) x
  contrapose! this
  exact FuzzCondition.bot x rfl HEq.rfl this

end ConNF
