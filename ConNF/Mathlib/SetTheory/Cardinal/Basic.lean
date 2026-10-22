module

public import Mathlib.Basic.Rel
public import Mathlib.SetTheory.Cardinal.Defs

public section

open Cardinal

namespace Function

universe u v

@[simp] lemma cardinalMk_graph {α : Type u} {β : Type v} (f : α → β) :
    #f.graph = Cardinal.lift.{v} #α := by
  rw [← Cardinal.mk_uLift]
  exact Cardinal.mk_congr
    ⟨fun x ↦ ⟨x.val.1⟩, fun x ↦ ⟨⟨x.down, f x.down⟩, rfl⟩, by rintro ⟨⟨x, _⟩, rfl⟩; rfl,
      fun x ↦ rfl⟩

end Function
