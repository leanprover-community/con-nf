import ConNF.Setup.Litter

/-!
# Atoms

In this file, we define atoms: the elements of the base type of our model. They are not atoms in the
ZFU sense (for example), they are simply the elements of the model which are in type `⊥`.

This base type does not appear in the final construction, it is just used as the foundation on which
the subsequent layers can be built.

## Main declarations

* `ConNF.Atom`: The type of atoms.
-/

universe u

open Cardinal Set

namespace ConNF

variable [Params.{u}]

/--
The base type of the construction, denoted by `τ₋₁` in various papers. Instead of declaring it as an
arbitrary type of cardinality `μ` and partitioning it into suitable sets of litters afterwards, we
define it as `Litter × κ`, which has the correct cardinality and comes with a natural partition.

These are not 'atoms' in the ZFU, TTTU or NFU sense; they are simply the elements of the model which
are in type `τ₋₁`.
-/
structure Atom : Type u where
  litter : Litter
  index : κ

instance : ToLitter Atom where
  toLitter := Atom.litter

/-- The set of atoms corresponding to litter `L`. -/
def litterSet (L : Litter) : Set Atom :=
  {a | a° = L}

@[inherit_doc] postfix:75 "ᴬ" => litterSet

@[simp]
theorem mem_litterSet_iff (a : Atom) (L : Litter) :
    a ∈ Lᴬ ↔ a° = L :=
  Iff.rfl

@[ext]
theorem Atom.ext {a₁ a₂ : Atom} (h : a₁° = a₂°) (h' : a₁.index = a₂.index) : a₁ = a₂ := by
  obtain ⟨L₁, i₁⟩ := a₁
  obtain ⟨L₂, i₂⟩ := a₂
  subst h
  subst h'
  rfl

/-- Strips away the name of the type of atoms, converting it into a combination of types
well-known to mathlib. -/
def atomEquiv : Atom ≃ Litter × κ
    where
  toFun a := (a°, a.index)
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The cardinality of `Atom` is the cardinality of `μ`.
We will prove that all types constructed in our model have cardinality equal to `μ`. -/
@[simp]
theorem card_atom : #Atom = #μ := by
  rw [atomEquiv.cardinal_eq, mk_prod, lift_id, lift_id, card_litter]
  exact mul_eq_left aleph0_lt_μ.le κ_le_μ (mk_ne_zero κ)

/-- Each litter set is equivalent as a type to `κ`. -/
def litterSetEquiv (L : Litter) : Lᴬ ≃ κ where
  toFun a := a.val.index
  invFun i := ⟨⟨L, i⟩, rfl⟩
  left_inv x := Subtype.ext <| Atom.ext x.prop.symm rfl
  right_inv _ := rfl

/-- Each litter set has cardinality `κ`. -/
@[simp]
theorem mk_litterSet (L : Litter) : #(Lᴬ) = #κ :=
  Cardinal.eq.mpr ⟨litterSetEquiv L⟩

instance (L : Litter) : Nonempty (Lᴬ) :=
  ⟨⟨L, Classical.arbitrary κ⟩, rfl⟩

end ConNF
