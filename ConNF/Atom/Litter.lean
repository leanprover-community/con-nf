import ConNF.Atom.Params

/-!
# Litters

In this file, we define litters, which are the parts of an indexed partition of the base type of our
model. Each litter is indexed by an element of `μ`, as well as some parameters `β` and `γ` used for
defining the `fuzz` map later.
-/

open Cardinal Set

open scoped Classical

universe u

namespace ConNF

variable [Params.{u}] {α β : Type u}

/-- The type indexing the partition of `Atom`. Each atom belongs to a unique litter.
The field `ν : μ` is an index that enforces that there are `μ` litters.
The fields `β` and `γ` are used in the definition of the `fuzz` map, which is an injection
into the type of litters. -/
structure Litter where
  ν : μ
  β : TypeIndex
  γ : Λ
  β_ne_γ : β ≠ γ

noncomputable instance : Inhabited Litter :=
  ⟨⟨default, ⊥, default, WithBot.bot_ne_coe⟩⟩

/-- Strips away the name of the type of litters, converting it into a combination of types
well-known to mathlib. -/
def litterEquiv : Litter ≃ { a : μ × TypeIndex × Λ // a.2.1 ≠ a.2.2 }
    where
  toFun L := ⟨⟨L.ν, L.β, L.γ⟩, L.β_ne_γ⟩
  invFun L := ⟨L.val.1, L.val.2.1, L.val.2.2, L.prop⟩
  left_inv := by rintro ⟨ν, β, γ, h⟩; rfl
  right_inv := by rintro ⟨⟨ν, β, γ⟩, h⟩; rfl

/-- There are precisely `μ` litters. -/
@[simp]
theorem mk_litter : #Litter = #μ := by
  refine
    litterEquiv.cardinal_eq.trans
      (le_antisymm ((Cardinal.mk_subtype_le _).trans_eq ?_)
        ⟨⟨fun ν => ⟨⟨ν, ⊥, default⟩, WithBot.bot_ne_coe⟩, fun ν₁ ν₂ =>
            congr_arg <| Prod.fst ∘ Subtype.val⟩⟩)
  have :=
    mul_eq_left (κ_isRegular.aleph0_le.trans κ_le_μ) (Λ_lt_κ.le.trans κ_lt_μ.le) Λ_isLimit.ne_zero
  simp only [mk_prod, lift_id, mk_typeIndex, mul_eq_self Λ_isLimit.aleph0_le, this]

end ConNF
