import ConNF.Setup.TypeIndex

/-!
# Litters

In this file, we define litters, which are the parts of an indexed partition of the base type of our
model. Each litter is indexed by an element of `μ`, as well as some parameters `β` and `γ` used for
defining the `fuzz` map later.

## Main declarations

* `ConNF.Litter`: The type of litters.
-/

universe u

open Cardinal WithBot

namespace ConNF

variable [Params.{u}]

/-- The type indexing the partition of `ConNF.Atom`. Each atom belongs to a unique litter.
The field `ν : μ` is an index that enforces that there are `μ` litters.
The fields `β` and `γ` are used in the definition of the `fuzz` map, which is an injection
into the type of litters. -/
structure Litter where
  ν : μ
  β : TypeIndex
  γ : Λ
  β_ne_γ : β ≠ γ

instance : Nonempty Litter :=
  ⟨⟨Classical.arbitrary μ, ⊥, Classical.arbitrary Λ, bot_ne_coe⟩⟩

/-- Strips away the name of the type of litters, converting it into a combination of types
well-known to mathlib. -/
def litterEquiv : Litter ≃ { a : μ × TypeIndex × Λ // a.2.1 ≠ a.2.2 }
    where
  toFun L := ⟨⟨L.ν, L.β, L.γ⟩, L.β_ne_γ⟩
  invFun L := ⟨L.val.1, L.val.2.1, L.val.2.2, L.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- There are precisely `μ` litters. -/
@[simp]
theorem card_litter : #Litter = #μ := by
  apply le_antisymm
  · apply litterEquiv.cardinal_eq.trans_le
    apply (mk_subtype_le _).trans_eq
    simp only [mk_prod, Cardinal.lift_id, TypeIndex.card, mul_mk_eq_max, max_self,
      max_eq_left_iff, Λ_le_μ]
  · apply mk_le_of_injective (f := λ ν ↦ ⟨ν, ⊥, Classical.arbitrary Λ, bot_ne_coe⟩)
    intro ν₁ ν₂ h
    cases h
    rfl

/-- Typeclass for the `ᴸ` notation. -/
class SuperL (X : Type _) (Y : outParam <| Type _) where
  superL : X → Y

/-- Typeclass for the `ᴬ` notation. -/
class SuperA (X : Type _) (Y : outParam <| Type _) where
  superA : X → Y

/-- Typeclass for the `ᴺ` notation. -/
class SuperN (X : Type _) (Y : outParam <| Type _) where
  superN : X → Y

postfix:max "ᴸ" => SuperL.superL
postfix:max "ᴬ" => SuperA.superA
postfix:max "ᴺ" => SuperN.superN

end ConNF
