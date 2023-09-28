import Mathlib.GroupTheory.GroupAction.Basic
import ConNF.Counting.OrdSupport

/-!
# Orbits of ordered supports
-/

open Set MulAction

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}

def OrdSupportOrbit (β : Iic α) : Type u :=
  orbitRel.Quotient (Allowable β) (OrdSupport β)

namespace OrdSupportOrbit

/-- The orbit of a given ordered support. -/
def mk (S : OrdSupport β) : OrdSupportOrbit β :=
  ⟦S⟧

protected theorem eq {S T : OrdSupport β} : mk S = mk T ↔ S ∈ orbit (Allowable β) T :=
  Quotient.eq (r := _)

instance : SetLike (OrdSupportOrbit β) (OrdSupport β) where
  coe o := {S | mk S = o}
  coe_injective' := by
    intro o₁ o₂
    refine Quotient.inductionOn₂ o₁ o₂ ?_
    intro S₁ S₂ h
    simp only [ext_iff, mem_setOf_eq] at h
    exact (h S₁).mp rfl

theorem mem_mk (S : OrdSupport β) : S ∈ mk S :=
  rfl

theorem mem_def (S : OrdSupport β) (o : OrdSupportOrbit β) : S ∈ o ↔ mk S = o := Iff.rfl

@[simp]
theorem mem_mk_iff (S T : OrdSupport β) : S ∈ mk T ↔ S ∈ orbit (Allowable β) T := by
  rw [mem_def, mk, mk, ← orbitRel_apply, Quotient.eq (r := _)]
  rfl

theorem smul_mem_of_mem {S : OrdSupport β} {o : OrdSupportOrbit β} (ρ : Allowable β) (h : S ∈ o) :
    ρ • S ∈ o := by
  refine Quotient.inductionOn o ?_ h
  intro T hST
  change _ ∈ mk _ at hST ⊢
  rw [mem_mk_iff] at hST ⊢
  obtain ⟨ρ', rfl⟩ := hST
  rw [smul_smul]
  exact ⟨ρ * ρ', rfl⟩

theorem smul_mem_iff_mem {S : OrdSupport β} {o : OrdSupportOrbit β} (ρ : Allowable β) :
    ρ • S ∈ o ↔ S ∈ o := by
  refine ⟨?_, smul_mem_of_mem ρ⟩
  intro h
  have := smul_mem_of_mem ρ⁻¹ h
  rw [inv_smul_smul] at this
  exact this

noncomputable def out (o : OrdSupportOrbit β) : OrdSupport β :=
  Quotient.out (s := _) o

theorem out_mem (o : OrdSupportOrbit β) : o.out ∈ o :=
  Quotient.out_eq (s := _) o

theorem nonempty (o : OrdSupportOrbit β) : (o : Set (OrdSupport β)).Nonempty :=
  ⟨o.out, o.out_mem⟩

theorem eq_mk_of_mem {S : OrdSupport β} {o : OrdSupportOrbit β} (h : S ∈ o) : o = mk S :=
  h.symm

/-- An orbit of ordered supports is *strong* if it contains a strong support. -/
def Strong (o : OrdSupportOrbit β) : Prop :=
  ∃ S : OrdSupport β, o = mk S ∧ S.Strong

end OrdSupportOrbit

end ConNF
