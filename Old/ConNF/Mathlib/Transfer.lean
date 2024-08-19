import Mathlib.Order.Hom.Basic
import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Transfer order structures across `equiv`s

In this file we prove theorems of the following form: if `β` has a
group structure and `α ≃ β` then `α` has a group structure, and
similarly for monoids, semigroups, rings, integral domains, fields and
so on.

Note that most of these constructions can also be obtained using the `transport` tactic.

## Tags

equiv
-/


namespace Equiv

variable {α β : Type _} (e : α ≃ β)

/-- Transfer `has_le` across an `equiv` -/
protected def hasLe [LE β] : LE α :=
  ⟨fun x y => e x ≤ e y⟩

/-- Transfer `has_lt` across an `equiv` -/
protected def hasLt [LT β] : LT α :=
  ⟨fun x y => e x < e y⟩

/-- Transfer `has_top` across an `equiv` -/
protected def hasTop [Top β] : Top α :=
  ⟨e.symm ⊤⟩

/-- Transfer `has_bot` across an `equiv` -/
protected def hasBot [Bot β] : Bot α :=
  ⟨e.symm ⊥⟩

/-- Transfer `has_sup` across an `equiv` -/
protected def hasSup [Sup β] : Sup α :=
  ⟨fun x y => e.symm (e x ⊔ e y)⟩

/-- Transfer `has_inf` across an `equiv` -/
protected def hasInf [Inf β] : Inf α :=
  ⟨fun x y => e.symm (e x ⊓ e y)⟩

/-- Transfer `has_Sup` across an `equiv` -/
protected def hasSupSet [SupSet β] : SupSet α :=
  ⟨fun s => e.symm (⨆ x ∈ s, e x)⟩

/-- Transfer `has_Inf` across an `equiv` -/
protected def hasInfSet [InfSet β] : InfSet α :=
  ⟨fun s => e.symm (⨅ x ∈ s, e x)⟩

theorem le_def [LE β] {x y : α} : e.hasLe.le x y ↔ e x ≤ e y :=
  Iff.rfl

theorem lt_def [LT β] {x y : α} : e.hasLt.lt x y ↔ e x < e y :=
  Iff.rfl

theorem top_def [Top β] : e.hasTop.top = e.symm ⊤ :=
  rfl

theorem bot_def [Bot β] : e.hasBot.bot = e.symm ⊥ :=
  rfl

theorem sup_def [Sup β] (x y : α) : e.hasSup.sup x y = e.symm (e x ⊔ e y) :=
  rfl

theorem inf_def [Inf β] (x y : α) : e.hasInf.inf x y = e.symm (e x ⊓ e y) :=
  rfl

theorem sSup_def [SupSet β] (s : Set α) : e.hasSupSet.sSup s = e.symm (⨆ x ∈ s, e x) :=
  rfl

theorem sInf_def [InfSet β] (s : Set α) : e.hasInfSet.sInf s = e.symm (⨅ x ∈ s, e x) :=
  rfl

/-- An equivalence `e : α ≃ β` gives a suptiplicative equivalence `α ≃⊔ β` where the suptiplicative
structure on `α` is the top obtained by transporting a suptiplicative structure on `β` back along
`e`. -/
def orderIso (e : α ≃ β) [LE β] :
    letI := e.hasLe
    α ≃o β :=
  by intros; exact { e with map_rel_iff' := fun {a b} => Iff.rfl }

@[simp]
theorem orderIso_apply [LE β] (a : α) : orderIso e a = e a :=
  rfl

theorem orderIso_symm_apply (e : α ≃ β) [LE β] (b : β) :
    letI := e.hasLe
    (orderIso e).symm b = e.symm b :=
  by intros; rfl

/-- Transfer `preorder` across an `equiv` -/
protected def preorder [Preorder β] : Preorder α :=
  Preorder.lift e

/-- Transfer `partial_order` across an `equiv` -/
protected def partialOrder [PartialOrder β] : PartialOrder α :=
  PartialOrder.lift e e.injective

/-- Transfer `linear_order` across an `equiv` -/
protected def linearOrder [LinearOrder β] : LinearOrder α :=
  LinearOrder.lift' e e.injective

/-- Transfer `semilattice_sup` across an `equiv` -/
protected def semilatticeSup [SemilatticeSup β] : SemilatticeSup α := by
  let sup := e.hasSup
  apply e.injective.semilatticeSup
  intros
  exact e.apply_symm_apply _

/-- Transfer `semilattice_inf` across an `equiv` -/
protected def semilatticeInf [SemilatticeInf β] : SemilatticeInf α := by
  let inf := e.hasInf
  apply e.injective.semilatticeInf
  intros
  exact e.apply_symm_apply _

/-- Transfer `lattice` across an `equiv` -/
protected def lattice [Lattice β] : Lattice α := by
  let sup := e.hasSup
  let inf := e.hasInf
  apply e.injective.lattice <;>
  · intros
    exact e.apply_symm_apply _

/-- Transfer `complete_lattice` across an `equiv` -/
protected def completeLattice [CompleteLattice β] : CompleteLattice α := by
  let top := e.hasTop
  let bot := e.hasBot
  let sup := e.hasSup
  let inf := e.hasInf
  let Sup := e.hasSupSet
  let Inf := e.hasInfSet
  apply e.injective.completeLattice <;>
  · intros
    exact e.apply_symm_apply _

/-- Transfer `complete_distrib_lattice` across an `equiv` -/
protected def completeDistribLattice [CompleteDistribLattice β] : CompleteDistribLattice α := by
  let completeLattice := e.completeLattice
  apply e.injective.completeDistribLattice <;>
  · intros
    exact e.apply_symm_apply _

end Equiv
