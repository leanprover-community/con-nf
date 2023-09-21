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

theorem decode_eq_decode_of_equiv {S₁ S₂ : OrdSupport β} {χ₁ χ₂ : CodingFunction β}
    (h₁ : S₁ ∈ χ₁) (h₂ : S₂ ∈ χ₂) (hS : S₁ ≈ S₂) (hχ : χ₁ ≈ χ₂) :
    (χ₁.decode S₁).get h₁ = (χ₂.decode S₂).get h₂ := by
  obtain ⟨T₁, hT₁, T₂, hT₂, hT, h⟩ := hχ
  rw [χ₁.mem_iff_of_mem h₁] at hT₁
  rw [χ₂.mem_iff_of_mem h₂] at hT₂
  obtain ⟨ρ₁, rfl⟩ := hT₁
  obtain ⟨ρ₂, rfl⟩ := hT₂
  have := (OrdSupport.smul_equiv_smul hS ρ₁).symm.trans hT
  have := OrdSupport.smul_equiv_smul this ρ₂⁻¹
  rw [inv_smul_smul, smul_smul] at this
  have := OrdSupport.smul_eq_of_smul_equiv _ this
  rw [mul_smul, inv_smul_eq_iff] at this
  simp_rw [← this] at h
  rw [decode_smul, decode_smul, smul_left_cancel_iff] at h
  exact h

/-- A reordering `r` is an equivalence of coding functions if it is an equivalence of some ordered
supports in the domains of the coding functions in question. -/
def IsEquiv (r : Tree Reorder β) (χ₁ χ₂ : CodingFunction β) : Prop :=
  ∃ S₁, ∃ h₁ : S₁ ∈ χ₁, ∃ S₂, ∃ h₂ : S₂ ∈ χ₂,
    OrdSupport.IsEquiv r S₁ S₂ ∧ (χ₁.decode S₁).get h₁ = (χ₂.decode S₂).get h₂

theorem IsEquiv.symm {r : Tree Reorder β} {χ₁ χ₂ : CodingFunction β} (h : IsEquiv r χ₁ χ₂) :
    IsEquiv (reorderSymm r) χ₂ χ₁ := by
  obtain ⟨S₁, hS₁, S₂, hS₂, h₁, h₂⟩ := h
  exact ⟨S₂, hS₂, S₁, hS₁, h₁.symm, h₂.symm⟩

/-- If two coding functions are equivalent, every ordered support in the domain of the first one
is equivalent to some ordered support in the domain of the second. -/
def exists_mem_isEquiv {r : Tree Reorder β} {χ₁ χ₂ : CodingFunction β} (h : IsEquiv r χ₁ χ₂)
    (S₁ : OrdSupport β) (hS₁ : S₁ ∈ χ₁) :
    ∃ S₂, ∃ hS₂: S₂ ∈ χ₂,
      OrdSupport.IsEquiv r S₁ S₂ ∧ (χ₁.decode S₁).get hS₁ = (χ₂.decode S₂).get hS₂ := by
  obtain ⟨T₁, hT₁, T₂, hT₂, h₁, h₂⟩ := h
  obtain ⟨ρ, rfl⟩ := (χ₁.dom_iff T₁ S₁ hT₁).mp hS₁
  refine ⟨ρ • T₂, ?_, ?_, ?_⟩
  · exact χ₂.smul_mem ρ hT₂
  · exact OrdSupport.isEquiv_smul h₁ ρ
  · rw [decode_smul, decode_smul, h₂]

def mem_of_mem_of_isEquiv {S₁ S₂ : OrdSupport β} {χ₁ χ₂ : CodingFunction β} {r : Tree Reorder β}
    (hS : OrdSupport.IsEquiv r S₁ S₂) (hχ : CodingFunction.IsEquiv r χ₁ χ₂) (hS₁ : S₁ ∈ χ₁) :
    S₂ ∈ χ₂ := by
  obtain ⟨S₂', h₁, h₂, h₃⟩ := CodingFunction.exists_mem_isEquiv hχ S₁ hS₁
  cases OrdSupport.isEquiv_isEquiv_right hS h₂
  exact h₁

def decode_eq_of_mem_of_isEquiv {S₁ S₂ : OrdSupport β} {χ₁ χ₂ : CodingFunction β}
    {r : Tree Reorder β}
    (hS : OrdSupport.IsEquiv r S₁ S₂) (hχ : CodingFunction.IsEquiv r χ₁ χ₂) (hS₁ : S₁ ∈ χ₁) :
    (χ₂.decode S₂).get (mem_of_mem_of_isEquiv hS hχ hS₁) = (χ₁.decode S₁).get hS₁ := by
  obtain ⟨S₂', h₁, h₂, h₃⟩ := CodingFunction.exists_mem_isEquiv hχ S₁ hS₁
  cases OrdSupport.isEquiv_isEquiv_right hS h₂
  exact h₃.symm

def mem_iff_mem_of_isEquiv {S₁ S₂ : OrdSupport β} {χ₁ χ₂ : CodingFunction β} {r : Tree Reorder β}
    (hS : OrdSupport.IsEquiv r S₁ S₂) (hχ : CodingFunction.IsEquiv r χ₁ χ₂) :
    S₁ ∈ χ₁ ↔ S₂ ∈ χ₂ :=
  ⟨mem_of_mem_of_isEquiv hS hχ, mem_of_mem_of_isEquiv hS.symm hχ.symm⟩

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

def CodingClass (β : Iic α) : Type u :=
  Quotient (CodingFunction.setoid β)

namespace CodingClass

def mk (χ : CodingFunction β) : CodingClass β := ⟦χ⟧

instance : Membership (OrdSupportClass β) (CodingClass β) where
  mem o c := ∃ S, OrdSupportClass.mk S = o ∧ ∃ χ, mk χ = c ∧ S ∈ χ

noncomputable def ordSupportOfMem {c : CodingClass β} {o : OrdSupportClass β} (h : o ∈ c) :
    OrdSupport β :=
  h.choose

@[simp]
theorem mk_ordSupportOfMem {c : CodingClass β} {o : OrdSupportClass β} (h : o ∈ c) :
    OrdSupportClass.mk (ordSupportOfMem h) = o :=
  h.choose_spec.1

theorem equiv_ordSupportOfMem {c : CodingClass β} {S : OrdSupport β}
    (h : OrdSupportClass.mk S ∈ c) :
    S ≈ ordSupportOfMem h :=
  Quotient.eq.mp ((mk_ordSupportOfMem h).symm)

noncomputable def codingFunctionOfMem {c : CodingClass β} {o : OrdSupportClass β} (h : o ∈ c) :
    CodingFunction β :=
  h.choose_spec.2.choose

@[simp]
theorem mk_codingFunctionOfMem {c : CodingClass β} {o : OrdSupportClass β} (h : o ∈ c) :
    mk (codingFunctionOfMem h) = c :=
  h.choose_spec.2.choose_spec.1

theorem equiv_codingFunctionOfMem {χ : CodingFunction β} {o : OrdSupportClass β} (h : o ∈ mk χ) :
    χ ≈ codingFunctionOfMem h :=
  Quotient.eq.mp ((mk_codingFunctionOfMem h).symm)

theorem ordSupportOfMem_mem_codingFunctionOfMem
    {c : CodingClass β} {o : OrdSupportClass β} (h : o ∈ c) :
    ordSupportOfMem h ∈ codingFunctionOfMem h :=
  h.choose_spec.2.choose_spec.2

noncomputable def decode (c : CodingClass β) (o : OrdSupportClass β) (h : o ∈ c) : Tangle β :=
  ((codingFunctionOfMem h).decode (ordSupportOfMem h)).get
    (ordSupportOfMem_mem_codingFunctionOfMem h)

theorem mk_mem_mk_of_mem {S : OrdSupport β} {χ : CodingFunction β} (h : S ∈ χ) :
    OrdSupportClass.mk S ∈ mk χ :=
  ⟨S, rfl, χ, rfl, h⟩

@[simp]
theorem decode_mk_eq_decode {S : OrdSupport β} {χ : CodingFunction β} (h : S ∈ χ) :
    (mk χ).decode (OrdSupportClass.mk S) (mk_mem_mk_of_mem h) = (χ.decode S).get h := by
  have h' := mk_mem_mk_of_mem h
  exact (CodingFunction.decode_eq_decode_of_equiv h
    (ordSupportOfMem_mem_codingFunctionOfMem h')
    (equiv_ordSupportOfMem h') (equiv_codingFunctionOfMem h')).symm

end CodingClass

end ConNF
