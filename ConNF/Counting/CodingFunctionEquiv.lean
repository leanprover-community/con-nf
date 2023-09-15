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

/-- Coding functions are equivalent if they contain two equivalent supports that decode to the same
tangle. -/
def Equiv (χ₁ χ₂ : CodingFunction β) : Prop :=
  ∃ S₁ : OrdSupport β, ∃ h₁ : S₁ ∈ χ₁,
  ∃ S₂ : OrdSupport β, ∃ h₂ : S₂ ∈ χ₂,
  S₁ ≈ S₂ ∧ (χ₁.decode S₁).get h₁ = (χ₂.decode S₂).get h₂

/-- If two coding functions are equivalent, every ordered support in the domain of the first one
is equivalent to some ordered support in the domain of the second. -/
def exists_mem_equiv' {χ₁ χ₂ : CodingFunction β} (h : Equiv χ₁ χ₂)
    (S₁ : OrdSupport β) (h₁ : S₁ ∈ χ₁) :
    ∃ S₂ : OrdSupport β, ∃ h₂ : S₂ ∈ χ₂,
    S₁ ≈ S₂ ∧ (χ₁.decode S₁).get h₁ = (χ₂.decode S₂).get h₂ := by
  obtain ⟨T₁, hT₁, T₂, hT₂, h⟩ := h
  obtain ⟨ρ, rfl⟩ := (χ₁.dom_iff T₁ S₁ hT₁).mp h₁
  refine ⟨ρ • T₂, ?_, ?_, ?_⟩
  · exact χ₂.smul_mem ρ hT₂
  · exact OrdSupport.smul_equiv_smul h.1 ρ
  · rw [decode_smul, decode_smul, h.2]

namespace Equiv

def refl (χ : CodingFunction β) : Equiv χ χ := by
  obtain ⟨S, hS⟩ := χ.dom_nonempty
  exact ⟨S, hS, S, hS, OrdSupport.Equiv.refl _, rfl⟩

def symm {χ₁ χ₂ : CodingFunction β} (h : Equiv χ₁ χ₂) : Equiv χ₂ χ₁ := by
  obtain ⟨S₁, h₁, S₂, h₂, h₁₂, h₁₂'⟩ := h
  exact ⟨S₂, h₂, S₁, h₁, h₁₂.symm, h₁₂'.symm⟩

def trans {χ₁ χ₂ χ₃ : CodingFunction β} (h : Equiv χ₁ χ₂) (h' : Equiv χ₂ χ₃) : Equiv χ₁ χ₃ := by
  obtain ⟨S₁, h₁, S₂, h₂, h₁₂, h₁₂'⟩ := h
  obtain ⟨S₃, h₃, h₂₃, h₂₃'⟩ := exists_mem_equiv' h' S₂ h₂
  exact ⟨S₁, h₁, S₃, h₃, h₁₂.trans h₂₃, h₁₂'.trans h₂₃'⟩

end Equiv

instance setoid (β : Iic α) : Setoid (CodingFunction β) where
  r := Equiv
  iseqv := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

/-- If two coding functions are equivalent, every ordered support in the domain of the first one
is equivalent to some ordered support in the domain of the second. -/
def exists_mem_equiv {χ₁ χ₂ : CodingFunction β} (h : χ₁ ≈ χ₂)
    (S₁ : OrdSupport β) (h₁ : S₁ ∈ χ₁) :
    ∃ S₂ : OrdSupport β, ∃ h₂ : S₂ ∈ χ₂,
    S₁ ≈ S₂ ∧ (χ₁.decode S₁).get h₁ = (χ₂.decode S₂).get h₂ :=
  exists_mem_equiv' h S₁ h₁

/-- A reordering `r` is an equivalence of coding functions if it is an equivalence of some ordered
supports in the domains of the coding functions in question. -/
def IsEquiv (r : Tree Reorder β) (χ₁ χ₂ : CodingFunction β) : Prop :=
  ∃ S₁ ∈ χ₁, ∃ S₂ ∈ χ₂, OrdSupport.IsEquiv r S₁ S₂

/-- If two coding functions are equivalent, every ordered support in the domain of the first one
is equivalent to some ordered support in the domain of the second. -/
def exists_mem_isEquiv {r : Tree Reorder β} {χ₁ χ₂ : CodingFunction β} (h : IsEquiv r χ₁ χ₂)
    (S₁ : OrdSupport β) (hS₁ : S₁ ∈ χ₁) :
    ∃ S₂ ∈ χ₂, OrdSupport.IsEquiv r S₁ S₂ := by
  obtain ⟨T₁, hT₁, T₂, hT₂, h⟩ := h
  obtain ⟨ρ, rfl⟩ := (χ₁.dom_iff T₁ S₁ hT₁).mp hS₁
  refine ⟨ρ • T₂, ?_, ?_⟩
  · exact χ₂.smul_mem ρ hT₂
  · exact OrdSupport.isEquiv_smul h ρ

def ReorderSupports (χ : CodingFunction β) (r : Tree Reorder β) : Prop :=
  ∀ S ∈ χ, S.ReorderSupports r

theorem reorderSupports (χ : CodingFunction β) (r : Tree Reorder β) (S : OrdSupport β)
    (hSχ : S ∈ χ) (hSr : S.ReorderSupports r) :
    χ.ReorderSupports r := by
  intro T hTχ
  rw [mem_iff_of_mem hSχ] at hTχ
  obtain ⟨ρ, rfl⟩ := hTχ
  exact hSr.smul ρ

noncomputable def reorder (χ : CodingFunction β) (r : Tree Reorder β) (h : χ.ReorderSupports r) :
    CodingFunction β :=
  code
    (χ.dom_nonempty.choose.reorder r (h _ χ.dom_nonempty.choose_spec))
    ((χ.decode χ.dom_nonempty.choose).get χ.dom_nonempty.choose_spec)
    (fun _ hρ => χ.supports_decode _ _ _ (fun _ hc => hρ hc))

end CodingFunction

end ConNF
