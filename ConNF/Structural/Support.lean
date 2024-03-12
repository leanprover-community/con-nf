import Mathlib.GroupTheory.GroupAction.Sum
import Mathlib.GroupTheory.GroupAction.Support
import ConNF.Structural.StructPerm
import ConNF.Structural.Enumeration

/-!
# Supports

In this file, we define addresses and supports.

## Main declarations

* `ConNF.Address`: The type of addresses.
* `ConNF.Support`: The type of small supports made of addresses.
-/

open Cardinal Equiv Sum

open scoped Cardinal Pointwise symmDiff

universe u

namespace ConNF

variable [Params.{u}] {α : TypeIndex}

/-- A *address* is an extended type index together with an atom or a near-litter.
This represents an object in the base type (the atom or near-litter) together with the path
detailing how we descend from type `α` to type `⊥` by looking at elements of elements and so on
in the model. -/
@[ext]
structure Address (α : TypeIndex) : Type u
    where
  path : ExtendedIndex α
  value : Atom ⊕ NearLitter

def Address_equiv : Address α ≃ ExtendedIndex α × (Atom ⊕ NearLitter)
    where
  toFun c := ⟨c.path, c.value⟩
  invFun c := ⟨c.1, c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- There are `μ` addresses. -/
@[simp]
theorem mk_address (α : TypeIndex) : #(Address α) = #μ := by
  rw [mk_congr Address_equiv]
  simp only [Address, mk_prod, mk_sum, mk_atom, lift_id, mk_nearLitter]
  rw [add_eq_left (Params.κ_isRegular.aleph0_le.trans Params.κ_lt_μ.le) le_rfl]
  exact mul_eq_right
    (Params.κ_isRegular.aleph0_le.trans Params.κ_lt_μ.le)
    (le_trans (mk_extendedIndex α) <| le_of_lt <| lt_trans Params.Λ_lt_κ Params.κ_lt_μ)
    (mk_ne_zero _)

namespace StructPerm

variable {π π' : StructPerm α} {c : Address α}

/-- Structural permutations act on addresses by following the derivative given in the
condition. -/
instance : MulAction (StructPerm α) (Address α)
    where
  smul π c := ⟨c.path, π c.path • c.value⟩
  one_smul := by rintro ⟨A, a | N⟩ <;> rfl
  mul_smul _ _ := by rintro ⟨A, a | N⟩ <;> rfl

/-!
We have a form of the next three lemmas for `StructPerm`, `NearLitterPerm`,
`Allowable`, and `NewAllowable`.
-/

theorem smul_address :
    π • c = ⟨c.path, π c.path • c.value⟩ :=
  rfl

@[simp]
theorem smul_address_eq_iff :
    π • c = c ↔ π c.path • c.value = c.value := by
  obtain ⟨A, x⟩ := c
  simp only [smul_address, Address.mk.injEq, true_and]

@[simp]
theorem smul_address_eq_smul_iff :
    π • c = π' • c ↔ π c.path • c.value = π' c.path • c.value := by
  obtain ⟨A, x⟩ := c
  simp only [smul_address, Address.mk.injEq, true_and]

end StructPerm

namespace NearLitterPerm

variable {π π' : NearLitterPerm} {c : Address ⊥}

instance : MulAction NearLitterPerm (Address ⊥)
    where
  smul π c := ⟨c.path, π • c.value⟩
  one_smul := by rintro ⟨A, a | N⟩ <;> rfl
  mul_smul _ _ := by rintro ⟨A, a | N⟩ <;> rfl

theorem smul_address :
    π • c = ⟨c.path, π • c.value⟩ :=
  rfl

@[simp]
theorem smul_address_eq_iff :
    π • c = c ↔ π • c.value = c.value := by
  obtain ⟨A, x⟩ := c
  simp only [smul_address, Address.mk.injEq, true_and]

@[simp]
theorem smul_address_eq_smul_iff :
    π • c = π' • c ↔ π • c.value = π' • c.value := by
  obtain ⟨A, x⟩ := c
  simp only [smul_address, Address.mk.injEq, true_and]

end NearLitterPerm

/-- A *support* is a function from an initial segment of κ to the type of addresses. -/
abbrev Support (α : TypeIndex) := Enumeration (Address α)

/-- There are exactly `μ` supports. -/
@[simp]
theorem mk_support : #(Support α) = #μ :=
  mk_enumeration (mk_address α)

end ConNF
