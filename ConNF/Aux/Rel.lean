import Mathlib.Data.Rel

namespace Rel

variable {α β : Type _}

-- Note the backward composition style of Rel.comp!
@[inherit_doc]
scoped infixr:80 " • " => Rel.comp

structure Injective (r : Rel α β) : Prop where
  injective : ∀ ⦃x₁ x₂ y⦄, r x₁ y → r x₂ y → x₁ = x₂

structure Coinjective (r : Rel α β) : Prop where
  coinjective : ∀ ⦃x y₁ y₂⦄, r x y₁ → r x y₂ → y₁ = y₂

structure Surjective (r : Rel α β) : Prop where
  surjective : ∀ y, ∃ x, r x y

structure Cosurjective (r : Rel α β) : Prop where
  cosurjective : ∀ x, ∃ y, r x y

structure Functional (r : Rel α β) extends r.Coinjective, r.Cosurjective : Prop

structure Cofunctional (r : Rel α β) extends r.Injective, r.Surjective : Prop

structure OneOne (r : Rel α β) extends r.Injective, r.Coinjective : Prop

structure Bijective (r : Rel α β) extends r.Functional, r.Cofunctional : Prop

structure DomEqCodom (r : Rel α α) : Prop where
  dom_eq_codom : r.dom = r.codom

structure Permutative (r : Rel α α) extends r.OneOne, r.DomEqCodom : Prop

/-- An alternative spelling of `Rel.graph` that is useful for proving inequalities of cardinals. -/
def graph' (r : Rel α β) : Set (α × β) :=
  r.uncurry

theorem le_of_graph'_subset {r s : Rel α β} (h : r.graph' ⊆ s.graph') :
    r ≤ s :=
  λ x y h' ↦ Set.mem_of_subset_of_mem (a := (x, y)) h h'

theorem graph'_subset_of_le {r s : Rel α β} (h : r ≤ s) :
    r.graph' ⊆ s.graph' :=
  λ z ↦ h z.1 z.2

theorem graph'_subset_iff {r s : Rel α β} :
    r.graph' ⊆ s.graph' ↔ r ≤ s :=
  ⟨le_of_graph'_subset, graph'_subset_of_le⟩

theorem graph'_injective :
    Function.Injective (Rel.graph' : Rel α β → Set (α × β)) :=
  λ _ _ h ↦ le_antisymm (le_of_graph'_subset h.le) (le_of_graph'_subset h.symm.le)

-- Compare Mathlib.Data.Rel and Mathlib.Logic.Relator.

end Rel
