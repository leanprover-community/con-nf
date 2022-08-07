import order.hom.basic
import order.complete_boolean_algebra

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

namespace equiv
variables {α β : Type*} (e : α ≃ β)

/-- Transfer `has_le` across an `equiv` -/
protected def has_le [has_le β] : has_le α := ⟨λ x y, e x ≤ e y⟩

/-- Transfer `has_lt` across an `equiv` -/
protected def has_lt [has_lt β] : has_lt α := ⟨λ x y, e x < e y⟩

/-- Transfer `has_top` across an `equiv` -/
protected def has_top [has_top β] : has_top α := ⟨e.symm ⊤⟩

/-- Transfer `has_bot` across an `equiv` -/
protected def has_bot [has_bot β] : has_bot α := ⟨e.symm ⊥⟩

/-- Transfer `has_sup` across an `equiv` -/
protected def has_sup [has_sup β] : has_sup α := ⟨λ x y, e.symm (e x ⊔ e y)⟩

/-- Transfer `has_inf` across an `equiv` -/
protected def has_inf [has_inf β] : has_inf α := ⟨λ x y, e.symm (e x ⊓ e y)⟩

/-- Transfer `has_Sup` across an `equiv` -/
protected def has_Sup [has_Sup β] : has_Sup α := ⟨λ s, e.symm (⨆ x ∈ s, e x)⟩

/-- Transfer `has_Inf` across an `equiv` -/
protected def has_Inf [has_Inf β] : has_Inf α := ⟨λ s, e.symm (⨅ x ∈ s, e x)⟩

lemma le_def [has_le β] {x y : α} : @has_le.le _ e.has_le x y ↔ e x ≤ e y := iff.rfl
lemma lt_def [has_lt β] {x y : α} : @has_lt.lt _ e.has_lt x y ↔ e x < e y := iff.rfl
lemma top_def [has_top β] : @has_top.top _ e.has_top = e.symm ⊤ := rfl
lemma bot_def [has_bot β] : @has_bot.bot _ e.has_bot = e.symm ⊥ := rfl
lemma sup_def [has_sup β] (x y : α) : @has_sup.sup _ e.has_sup x y = e.symm (e x ⊔ e y) := rfl
lemma inf_def [has_inf β] (x y : α) : @has_inf.inf _ e.has_inf x y = e.symm (e x ⊓ e y) := rfl
lemma Sup_def [has_Sup β] (s : set α) : @has_Sup.Sup _ e.has_Sup s = e.symm (⨆ x ∈ s, e x) := rfl
lemma Inf_def [has_Inf β] (s : set α) : @has_Inf.Inf _ e.has_Inf s = e.symm (⨅ x ∈ s, e x) := rfl

/-- An equivalence `e : α ≃ β` gives a suptiplicative equivalence `α ≃⊔ β` where the suptiplicative
structure on `α` is the top obtained by transporting a suptiplicative structure on `β` back along
`e`. -/
def order_iso (e : α ≃ β) [has_le β] : by { letI := e.has_le, exact α ≃o β } :=
by { introsI, exact { map_rel_iff' := λ x y, iff.rfl, ..e } }

@[simp] lemma order_iso_apply [has_le β] (a : α) : order_iso e a = e a := rfl

lemma order_iso_symm_apply (e : α ≃ β) [has_le β] (b : β) :
  by { letI := e.has_le, exact (order_iso e).symm b = e.symm b } :=
by { intros, refl }

/-- Transfer `preorder` across an `equiv` -/
protected def preorder [preorder β] : preorder α := preorder.lift e

/-- Transfer `partial_order` across an `equiv` -/
protected def partial_order [partial_order β] : partial_order α := partial_order.lift e e.injective

/-- Transfer `linear_order` across an `equiv` -/
protected def linear_order [linear_order β] : linear_order α := linear_order.lift' e e.injective

/-- Transfer `semilattice_sup` across an `equiv` -/
protected def semilattice_sup [semilattice_sup β] : semilattice_sup α :=
let preorder := e.preorder, sup := e.has_sup in
by resetI; apply e.injective.semilattice_sup _; intros; exact e.apply_symm_apply _

/-- Transfer `semilattice_inf` across an `equiv` -/
protected def semilattice_inf [semilattice_inf β] : semilattice_inf α :=
let preorder := e.preorder, inf := e.has_inf in
by resetI; apply e.injective.semilattice_inf _; intros; exact e.apply_symm_apply _

/-- Transfer `lattice` across an `equiv` -/
protected def lattice [lattice β] : lattice α :=
let preorder := e.preorder, sup := e.has_sup, inf := e.has_inf in
by resetI; apply e.injective.lattice _; intros; exact e.apply_symm_apply _

/-- Transfer `complete_lattice` across an `equiv` -/
protected def complete_lattice [complete_lattice β] : complete_lattice α :=
let top := e.has_top, bot := e.has_bot, sup := e.has_sup, inf := e.has_inf, Sup := e.has_Sup,
  Inf := e.has_Inf in
by resetI; apply e.injective.complete_lattice _; intros; exact e.apply_symm_apply _

/-- Transfer `complete_distrib_lattice` across an `equiv` -/
protected def complete_distrib_lattice [complete_distrib_lattice β] : complete_distrib_lattice α :=
let complete_lattice := e.complete_lattice in
by resetI; apply e.injective.complete_distrib_lattice _; intros; exact e.apply_symm_apply _

end equiv
