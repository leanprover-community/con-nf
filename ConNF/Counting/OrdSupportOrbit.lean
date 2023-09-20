import Mathlib.GroupTheory.GroupAction.Basic
import ConNF.Counting.SpecSame

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

theorem mem_mk_def (S T : OrdSupport β) : S ∈ mk T ↔ mk S = mk T := Iff.rfl

@[simp]
theorem mem_mk_iff (S T : OrdSupport β) : S ∈ mk T ↔ S ∈ orbit (Allowable β) T := by
  rw [mem_mk_def, mk, mk, ← orbitRel_apply, Quotient.eq (r := _)]
  rfl

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
