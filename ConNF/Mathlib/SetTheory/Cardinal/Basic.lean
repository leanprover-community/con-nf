import Mathlib.Data.Rel
import Mathlib.SetTheory.Cardinal.Defs

open Cardinal

namespace Function

@[simp] lemma cardinalMk_graph {α β : Type _} (f : α → β) : #f.graph = #α := by
  rw [Cardinal.eq]
  exact ⟨⟨fun x ↦ x.val.1, fun x ↦ ⟨⟨x, f x⟩, rfl⟩, by rintro ⟨⟨x, _⟩, rfl⟩; rfl, fun x ↦ rfl⟩⟩

end Function
