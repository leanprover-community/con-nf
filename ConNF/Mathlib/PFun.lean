import Mathlib.Data.PFun

namespace PFun

variable {α β : Type _}

noncomputable def ofGraph (g : α → β → Prop)
    (_hg : ∀ a b b', g a b → g a b' → b = b') : α →. β :=
  fun a => ⟨∃ b, g a b, fun h => h.choose⟩

variable {g : α → β → Prop} {hg : ∀ a b b', g a b → g a b' → b = b'}

theorem get_eq (a : α) (b : β) (h : g a b) :
    (ofGraph g hg a).get ⟨b, h⟩ = b := by
  have : ∃ b, g a b := ⟨b, h⟩
  refine hg a _ _ this.choose_spec h

@[simp]
theorem ofGraph_dom : (ofGraph g hg).Dom = {a | ∃ b, g a b} := rfl

end PFun
