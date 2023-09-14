import ConNF.Counting.CodingFunction
import ConNF.Counting.OrdSupportEquiv

/-!
# Equivalences of coding functions
-/

open MulAction Set Sum

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}

namespace CodingFunction

-- TODO: Is this file even needed?

/-- A reordering `r` is an equivalence of coding functions if it is an equivalence of some ordered
supports in the domains of the coding functions in question. -/
def Equiv (χ₁ χ₂ : CodingFunction β) : Prop :=
  ∃ S₁ ∈ χ₁, ∃ S₂ ∈ χ₂, S₁ ≈ S₂

/-- If two coding functions are equivalent, every ordered support in the domain of the first one
is equivalent to some ordered support in the domain of the second. -/
def exists_mem_equiv {χ₁ χ₂ : CodingFunction β} (h : Equiv χ₁ χ₂)
    (S₁ : OrdSupport β) (hS₁ : S₁ ∈ χ₁) :
    ∃ S₂ ∈ χ₂, S₁ ≈ S₂ := by
  obtain ⟨T₁, hT₁, T₂, hT₂, h⟩ := h
  obtain ⟨ρ, rfl⟩ := (χ₁.dom_iff T₁ S₁ hT₁).mp hS₁
  refine ⟨ρ • T₂, ?_, ?_⟩
  · exact χ₂.smul_mem ρ hT₂
  · exact OrdSupport.smul_equiv_smul h ρ

end CodingFunction

end ConNF
