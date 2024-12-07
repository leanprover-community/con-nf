import ConNF.Base.Litter
import ConNF.Base.Small

/-!
# Atoms

In this file, we define atoms: the elements of the base type of our model. They are not atoms in the
ZFU sense (for example), they are simply the elements of the model which are in type `⊥`.

This base type does not appear in the final construction, it is just used as the foundation on which
the subsequent layers can be built.
-/

universe u

open Cardinal Set

namespace ConNF

variable [Params.{u}]

/--
The base type of the construction, denoted by `τ₋₁` in various papers.
An atom consists of a litter together with an index in `κ`.
This gives a partition of atoms into litters: we say that two atoms are in the same litter
if their first projections are equal. These equivalence classes will be called *litter sets*.

These are not 'atoms' in the ZFU, TTTU or NFU sense; they are simply the elements of the model which
are in type `τ₋₁`.
-/
structure Atom : Type u where
  litter : Litter
  index : κ

/-- If `a` is an atom, `aᴸ` is its first projection; that is, the litter associated to it. -/
instance : SuperL Atom Litter where
  superL := Atom.litter

/-- If `L` is a litter, `Lᴬ` is the set of atoms associated to that litter.
This is sometimes called the *litter set* of `L`. -/
instance : SuperA Litter (Set Atom) where
  superA L := {a | aᴸ = L}

/-- The definition of membership in a litter set. -/
@[simp]
theorem mem_litter_atoms_iff (a : Atom) (L : Litter) :
    a ∈ Lᴬ ↔ aᴸ = L :=
  Iff.rfl

theorem Atom.ext {a₁ a₂ : Atom} (h : a₁ᴸ = a₂ᴸ) (h' : a₁.index = a₂.index) : a₁ = a₂ := by
  obtain ⟨L₁, i₁⟩ := a₁
  obtain ⟨L₂, i₂⟩ := a₂
  subst h
  subst h'
  rfl

/-- Strips away the name of the type of atoms, converting it into a combination of types
well-known to mathlib. -/
def atomEquiv : Atom ≃ Litter × κ
    where
  toFun a := (aᴸ, a.index)
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The cardinality of `Atom` is the cardinality of `μ`.
We will prove that all types constructed in our model have cardinality equal to that of `μ`. -/
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
theorem Litter.card_atoms (L : Litter) : #Lᴬ = #κ :=
  Cardinal.eq.mpr ⟨litterSetEquiv L⟩

/-- Litter sets are not small. -/
theorem Litter.atoms_not_small (L : Litter) : ¬Small Lᴬ :=
  L.card_atoms.not_lt

/-- Litter sets are nonempty. -/
instance (L : Litter) : Nonempty Lᴬ :=
  ⟨⟨L, Classical.arbitrary κ⟩, rfl⟩

/-- Litter sets are pairwise disjoint. -/
theorem litter_pairwise_disjoint {L₁ L₂ : Litter} (h : L₁ ≠ L₂) : Disjoint L₁ᴬ L₂ᴬ := by
  rw [Set.disjoint_iff]
  intro x hx
  exact h <| hx.1.symm.trans hx.2

/-- If two litters are near each other, then they are equal. -/
theorem litter_eq_of_near {L₁ L₂ : Litter} (h : L₁ᴬ ~ L₂ᴬ) : L₁ = L₂ := by
  obtain ⟨a, ha₁, ha₂⟩ := inter_nonempty_of_near h L₁.atoms_not_small
  exact ha₁.symm.trans ha₂

end ConNF
