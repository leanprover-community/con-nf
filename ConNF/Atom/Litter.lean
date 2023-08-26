import ConNF.Atom.Params

/-!
# Litters, near-litters

In this file, we define litters and near-litters.

Litters are the parts of an indexed partition of `con_nf.atom`. Their precise definition can be
considered opaque, as we only care about the fact that their cardinality is `κ`.

## Main declarations

* `con_nf.litter`: The `i`-th litter.
* `con_nf.is_near_litter`: A set is a `i`-near-litter if it is near the `i`-th litter.
-/

open Cardinal Set

open scoped Classical

universe u

namespace ConNF

variable [Params.{u}] {α β : Type u}

/-- The litters. This is the type indexing the partition of `atom`. -/
structure Litter where
  ν : μ
  β : TypeIndex
  γ : Λ
  β_ne_γ : β ≠ γ

noncomputable instance : Inhabited Litter :=
  ⟨⟨default, ⊥, default, WithBot.bot_ne_coe⟩⟩

/-- Litters are equivalent to a subtype of a product type. -/
def litterEquiv : Litter ≃ { a : μ ×ₗ TypeIndex ×ₗ Λ // a.2.1 ≠ a.2.2 }
    where
  toFun L := ⟨⟨L.ν, L.β, L.γ⟩, L.β_ne_γ⟩
  invFun L := ⟨L.val.1, L.val.2.1, L.val.2.2, L.prop⟩
  left_inv := by rintro ⟨ν, β, γ, h⟩; rfl
  right_inv := by rintro ⟨⟨ν, β, γ⟩, h⟩; rfl

@[simp]
theorem mk_litter : #Litter = #μ := by
  refine
    litterEquiv.cardinal_eq.trans
      (le_antisymm ((Cardinal.mk_subtype_le _).trans_eq ?_)
        ⟨⟨fun ν => ⟨⟨ν, ⊥, default⟩, WithBot.bot_ne_coe⟩, fun ν₁ ν₂ =>
            congr_arg <| Prod.fst ∘ Subtype.val⟩⟩)
  have :=
    mul_eq_left (κ_regular.aleph0_le.trans κ_le_μ) (Λ_lt_κ.le.trans κ_lt_μ.le) Λ_limit.ne_zero
  simp only [Lex, mk_prod, lift_id, mk_typeIndex, mul_eq_self Λ_limit.aleph0_le, this]

/-- Principal segments (sets of the form `{y | y < x}`) have cardinality `< μ`. -/
theorem card_Iio_lt (x : μ) : #(Iio x) < #μ :=
  card_typein_lt (· < ·) x μ_ord.symm

/-- Initial segments (sets of the form `{y | y ≤ x}`) have cardinality `< μ`. -/
theorem card_Iic_lt (x : μ) : #(Iic x) < #μ := by
  rw [← Iio_union_right, mk_union_of_disjoint, mk_singleton]
  · exact (add_one_le_succ _).trans_lt (μ_strong_limit.isLimit.succ_lt (card_Iio_lt x))
  · simp

end ConNF
