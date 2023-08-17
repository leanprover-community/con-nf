import Mathlib.Order.Hom.Basic
import Mathlib.Order.CompleteBooleanAlgebra

#align_import mathlib.transfer

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

/- warning: equiv.has_Sup clashes with equiv.has_sup -> Equiv.hasSup
Case conversion may be inaccurate. Consider using '#align equiv.has_Sup Equiv.hasSupₓ'. -/
#print Equiv.hasSup /-
/-- Transfer `has_Sup` across an `equiv` -/
protected def hasSup [SupSet β] : SupSet α :=
  ⟨fun s => e.symm (⨆ x ∈ s, e x)⟩
-/

/- warning: equiv.has_Inf clashes with equiv.has_inf -> Equiv.hasInf
Case conversion may be inaccurate. Consider using '#align equiv.has_Inf Equiv.hasInfₓ'. -/
#print Equiv.hasInf /-
/-- Transfer `has_Inf` across an `equiv` -/
protected def hasInf [InfSet β] : InfSet α :=
  ⟨fun s => e.symm (⨅ x ∈ s, e x)⟩
-/

theorem le_def [LE β] {x y : α} : @LE.le _ e.LE x y ↔ e x ≤ e y :=
  Iff.rfl

theorem lt_def [LT β] {x y : α} : @LT.lt _ e.LT x y ↔ e x < e y :=
  Iff.rfl

theorem top_def [Top β] : @Top.top _ e.Top = e.symm ⊤ :=
  rfl

theorem bot_def [Bot β] : @Bot.bot _ e.Bot = e.symm ⊥ :=
  rfl

theorem sup_def [Sup β] (x y : α) : @Sup.sup _ e.Sup x y = e.symm (e x ⊔ e y) :=
  rfl

theorem inf_def [Inf β] (x y : α) : @Inf.inf _ e.Inf x y = e.symm (e x ⊓ e y) :=
  rfl

theorem sSup_def [SupSet β] (s : Set α) : @SupSet.sSup _ e.SupSet s = e.symm (⨆ x ∈ s, e x) :=
  rfl

theorem sInf_def [InfSet β] (s : Set α) : @InfSet.sInf _ e.InfSet s = e.symm (⨅ x ∈ s, e x) :=
  rfl

/-- An equivalence `e : α ≃ β` gives a suptiplicative equivalence `α ≃⊔ β` where the suptiplicative
structure on `α` is the top obtained by transporting a suptiplicative structure on `β` back along
`e`. -/
def orderIso (e : α ≃ β) [LE β] :
    letI := e.has_le
    α ≃o β :=
  by intros; exact { e with map_rel_iff' := fun x y => Iff.rfl }

@[simp]
theorem orderIso_apply [LE β] (a : α) : orderIso e a = e a :=
  rfl

theorem orderIso_symm_apply (e : α ≃ β) [LE β] (b : β) :
    letI := e.has_le
    (OrderIso e).symm b = e.symm b :=
  by intros; rfl

/-- Transfer `preorder` across an `equiv` -/
protected def preorder [Preorder β] : Preorder α :=
  Preorder.lift e

/-- Transfer `partial_order` across an `equiv` -/
protected def partialOrder [PartialOrder β] : PartialOrder α :=
  PartialOrder.lift e e.Injective

/-- Transfer `linear_order` across an `equiv` -/
protected def linearOrder [LinearOrder β] : LinearOrder α :=
  LinearOrder.lift' e e.Injective

/-- Transfer `semilattice_sup` across an `equiv` -/
protected def semilatticeSup [SemilatticeSup β] : SemilatticeSup α :=
  by
  let preorder := e.Preorder
  let sup := e.Sup
  skip <;> apply e.injective.semilattice_sup _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `semilattice_inf` across an `equiv` -/
protected def semilatticeInf [SemilatticeInf β] : SemilatticeInf α :=
  by
  let preorder := e.Preorder
  let inf := e.Inf
  skip <;> apply e.injective.semilattice_inf _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `lattice` across an `equiv` -/
protected def lattice [Lattice β] : Lattice α :=
  by
  let preorder := e.Preorder
  let sup := e.Sup
  let inf := e.Inf
  skip <;> apply e.injective.lattice _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `complete_lattice` across an `equiv` -/
protected def completeLattice [CompleteLattice β] : CompleteLattice α :=
  by
  let top := e.Top
  let bot := e.Bot
  let sup := e.Sup
  let inf := e.Inf
  let Sup := e.SupSet
  let Inf := e.InfSet
  skip <;> apply e.injective.complete_lattice _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `complete_distrib_lattice` across an `equiv` -/
protected def completeDistribLattice [CompleteDistribLattice β] : CompleteDistribLattice α :=
  by
  let complete_lattice := e.CompleteLattice
  skip <;> apply e.injective.complete_distrib_lattice _ <;> intros <;> exact e.apply_symm_apply _

end Equiv
