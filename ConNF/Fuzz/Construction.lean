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

Treating the output of a `fuzz` map as a typed near-litter, its pos is always greater than
the pos of the input to the function. This ensures a well-foundedness condition that we use
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

variable [Params.{u}] [BasePositions] {β : TypeIndex} [ModelData β] [PositionedTangles β]

/-- The set of elements of `ν` that `fuzz _ t` cannot be. -/
def fuzzDeny (t : Tangle β) : Set μ :=
  { ν : μ | ∃ (N : NearLitter), pos N ≤ pos t ∧ ν = N.1.1 } ∪
  { ν : μ | ∃ (a : Atom), pos a ≤ pos t ∧ ν = a.1.1 }

theorem mk_invImage_lt (t : Tangle β) : #{ t' // t' < t } < #μ := by
  refine lt_of_le_of_lt ?_ (show #{ ν // ν < pos t } < #μ from card_Iio_lt _)
  refine ⟨⟨fun t' => ⟨_, t'.prop⟩, ?_⟩⟩
  intro y₁ y₂ h
  simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Subtype.coe_inj] at h
  exact h

variable {γ}

theorem mk_fuzzDeny (t : Tangle β) :
    #{ t' // t' < t } + #(fuzzDeny t) < #μ := by
  refine add_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le (mk_invImage_lt t) ?_
  refine lt_of_le_of_lt (mk_union_le _ _) ?_
  refine add_lt_of_lt Params.μ_isStrongLimit.isLimit.aleph0_le ?_ ?_
  · have : #{ N : NearLitter | pos N ≤ pos t } < #μ
    · refine lt_of_le_of_lt ?_ (card_Iic_lt (pos t))
      refine ⟨⟨fun a => ⟨pos a.1, a.2⟩, ?_⟩⟩
      intro a b h
      exact Subtype.coe_inj.mp (pos_injective (Subtype.coe_inj.mpr h))
    refine lt_of_le_of_lt ?_ this
    refine mk_le_of_surjective (f := fun a => ⟨_, a.1, a.2, rfl⟩) ?_
    rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  · have : #{ a : Atom | pos a ≤ pos t } < #μ
    · refine lt_of_le_of_lt ?_ (card_Iic_lt (pos t))
      refine ⟨⟨fun a => ⟨pos a.1, a.2⟩, ?_⟩⟩
      intro a b h
      exact Subtype.coe_inj.mp (pos_injective (Subtype.coe_inj.mpr h))
    refine lt_of_le_of_lt ?_ this
    refine mk_le_of_surjective (f := fun a => ⟨_, a.1, a.2, rfl⟩) ?_
    rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

/-!
We're done with proving technical results, now we can define the `fuzz` maps.
-/

variable {γ : Λ} (hβγ : β ≠ γ)

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

Treating the output of a `fuzz` map as a typed near-litter, its pos is always greater than
the pos of the input to the function. This ensures a well-foundedness condition that we use
in many places later.
-/
noncomputable def fuzz (t : Tangle β) : Litter :=
  ⟨chooseWf fuzzDeny mk_fuzzDeny t, β, γ, hβγ⟩

@[simp]
theorem fuzz_β (t : Tangle β) : (fuzz hβγ t).β = β :=
  rfl

@[simp]
theorem fuzz_γ (t : Tangle β) : (fuzz hβγ t).γ = γ :=
  rfl

section congr

variable {β' : TypeIndex} {γ' : Λ} [ModelData β'] [PositionedTangles β']
  [ModelData γ'] [PositionedTangles γ'] [TypedObjects γ']

theorem fuzz_congr_β {hβγ : (β : TypeIndex) ≠ γ} {hβγ' : (β' : TypeIndex) ≠ γ'}
  {t : Tangle β} {t' : Tangle β'} (h : fuzz hβγ t = fuzz hβγ' t') :
  β = β' := by
  have h₁ := fuzz_β hβγ t
  have h₂ := fuzz_β hβγ' t'
  rw [← h, h₁] at h₂
  exact h₂

theorem fuzz_congr_γ {hβγ : (β : TypeIndex) ≠ γ} {hβγ' : (β' : TypeIndex) ≠ γ'}
  {t : Tangle β} {t' : Tangle β'} (h : fuzz hβγ t = fuzz hβγ' t') :
  γ = γ' := by
  have h₁ := fuzz_γ hβγ t
  have h₂ := fuzz_γ hβγ' t'
  rw [← h, h₁] at h₂
  exact h₂

end congr

theorem fuzz_injective : Injective (fuzz hβγ) := by
  intro t₁ t₂ h
  simp only [fuzz, Litter.mk.injEq, chooseWf_injective.eq_iff, and_self, and_true] at h
  exact h

theorem fuzz_not_mem_deny (t : Tangle β) : (fuzz hβγ t).ν ∉ fuzzDeny t :=
  chooseWf_not_mem_deny t

theorem pos_lt_pos_fuzz_nearLitter (t : Tangle β) (N : NearLitter) (h : N.1 = fuzz hβγ t) :
    pos t < pos N := by
  have h' := fuzz_not_mem_deny hβγ t
  contrapose! h'
  refine Or.inl ⟨N, h', ?_⟩
  rw [h]

theorem pos_lt_pos_fuzz_atom (t : Tangle β) (a : Atom) (ha : a.1 = fuzz hβγ t) :
    pos t < pos a := by
  have h' := fuzz_not_mem_deny hβγ t
  contrapose! h'
  refine Or.inr ⟨a, h', ?_⟩
  rw [ha]

end ConNF
