import ConNF.BaseType.Litter

/-!
# Atoms

In this file, we define atoms: the elements of the base type of our model. They are not atoms in the
ZFU sense (for example), they are simply the elements of the model which are in type `τ₋₁`.

This base type does not appear in the final construction, it is just used as the foundation on which
the subsequent layers can be built.

## Main declarations

* `ConNF.Atom`: The type of atoms.
-/

open Cardinal Set

open scoped Classical

universe u

namespace ConNF

variable [Params.{u}] {α β : Type u}

/--
The base type of the construction, denoted by `τ₋₁` in various papers. Instead of declaring it as an
arbitrary type of cardinality `μ` and partitioning it into suitable sets of litters afterwards, we
define it as `Litter × κ`, which has the correct cardinality and comes with a natural partition.

These are not 'atoms' in the ZFU, TTTU or NFU sense; they are simply the elements of the model which
are in type `τ₋₁`.
-/
def Atom : Type _ :=
  Litter × κ

noncomputable instance : Inhabited Atom :=
  ⟨⟨default, default⟩⟩

/-- The cardinality of `Atom` is the cardinality of `μ`.
We will prove that all types constructed in our model have cardinality equal to `μ`. -/
@[simp]
theorem mk_atom : #Atom = #μ := by
  simp_rw [Atom, mk_prod, lift_id, mk_litter,
    mul_eq_left (κ_isRegular.aleph0_le.trans κ_le_μ) κ_le_μ κ_isRegular.pos.ne']

/-- The set corresponding to litter `L`. We define a litter set as the set of atoms with first
projection `L`. -/
def litterSet (L : Litter) : Set Atom :=
  {a | a.1 = L}

@[simp]
theorem mem_litterSet {a : Atom} {L : Litter} : a ∈ litterSet L ↔ a.1 = L :=
  Iff.rfl

/-- Each litter set is equivalent as a type to `κ`. -/
def litterSetEquiv (L : Litter) : litterSet L ≃ κ := ⟨
    fun x => x.1.2,
    fun k => ⟨(L, k), rfl⟩,
    fun x => Subtype.ext <| Prod.ext x.2.symm rfl,
    fun _ => rfl
  ⟩

/-- Each litter set has cardinality `κ`. -/
@[simp]
theorem mk_litterSet (L : Litter) : #(litterSet L) = #κ :=
  Cardinal.eq.2 ⟨litterSetEquiv L⟩

/-- Two litters with different indices have disjoint litter sets. -/
theorem pairwise_disjoint_litterSet : Pairwise (Disjoint on litterSet) :=
  fun _ _ h => disjoint_left.2 fun _ h₁ h₂ => h <| h₁.symm.trans h₂

theorem eq_of_mem_litterSet_of_mem_litterSet {a : Atom} {L₁ L₂ : Litter}
    (hi : a ∈ litterSet L₁) (hj : a ∈ litterSet L₂) : L₁ = L₂ :=
  pairwise_disjoint_litterSet.eq <| not_disjoint_iff.2 ⟨_, hi, hj⟩

theorem litterSet_symmDiff_litterSet {L₁ L₂ : Litter} (h : L₁ ≠ L₂) :
    litterSet L₁ ∆ litterSet L₂ = litterSet L₁ ∪ litterSet L₂ :=
  (pairwise_disjoint_litterSet h).symmDiff_eq_sup

end ConNF
