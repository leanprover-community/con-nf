import ConNF.Atom.Litter

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

/-- The base type of the construction, `τ₋₁` in the document. Instead of declaring it as an
arbitrary type of cardinality `μ` and partitioning it into suitable sets of litters afterwards, we
define it as `litter × κ`, which has the correct cardinality and comes with a natural
partition.

These are not 'atoms' in the ZFU, TTTU or NFU sense; they are simply the elements of the model which
are in type `τ₋₁`. -/
def Atom : Type _ :=
  Litter × κ

noncomputable instance : Inhabited Atom :=
  ⟨⟨default, default⟩⟩

/-- The cardinality of `τ₋₁` is the cardinality of `μ`.
We will prove that all types constructed in our model have cardinality equal to `μ`. -/
@[simp]
theorem mk_atom : #Atom = #μ := by
  simp_rw [Atom, mk_prod, lift_id, mk_litter,
    mul_eq_left (κ_regular.aleph0_le.trans κ_le_μ) κ_le_μ κ_regular.pos.ne']

variable {i j : Litter} {s t : Set Atom}

/-- The set corresponding to the `i`-th litter.

We define a litter as the set of elements of the base type `τ₋₁` where the first element of the pair
is `i`. However, as noted above, the definition can be viewed as opaque, since its cardinality is
the only interesting feature. -/
def litterSet (i : Litter) : Set Atom :=
  {p | p.1 = i}

@[simp]
theorem mem_litterSet {a : Atom} {i : Litter} : a ∈ litterSet i ↔ a.1 = i :=
  Iff.rfl

def litterSetEquiv (L : Litter) : litterSet L ≃ κ := ⟨
    fun x => x.1.2,
    fun k => ⟨(L, k), rfl⟩,
    fun x => Subtype.ext <| Prod.ext x.2.symm rfl,
    fun _ => rfl
  ⟩

/-- Each litter has cardinality `κ`. -/
@[simp]
theorem mk_litterSet (i : Litter) : #(litterSet i) = #κ :=
  Cardinal.eq.2 ⟨litterSetEquiv i⟩

/-- Two litters with different indices are disjoint. -/
theorem pairwise_disjoint_litterSet : Pairwise (Disjoint on litterSet) :=
  fun _ _ h => disjoint_left.2 fun _ hi hj => h <| hi.symm.trans hj

theorem eq_of_mem_litterSet_of_mem_litterSet {a : Atom}
    (hi : a ∈ litterSet i) (hj : a ∈ litterSet j) : i = j :=
  pairwise_disjoint_litterSet.eq <| not_disjoint_iff.2 ⟨_, hi, hj⟩

theorem litterSet_symmDiff_litterSet (h : i ≠ j) :
    litterSet i ∆ litterSet j = litterSet i ∪ litterSet j :=
  (pairwise_disjoint_litterSet h).symmDiff_eq_sup

end ConNF
