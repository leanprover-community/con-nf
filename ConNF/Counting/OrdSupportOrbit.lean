import Mathlib.GroupTheory.GroupAction.Basic
import ConNF.Counting.OrdSupportEquiv

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

def OrdSupportClassOrbit (β : Iic α) : Type u :=
  orbitRel.Quotient (Allowable β) (OrdSupportClass β)

namespace OrdSupportClassOrbit

/-- The orbit of a given ordered support class. -/
def mk (S : OrdSupportClass β) : OrdSupportClassOrbit β :=
  ⟦S⟧

protected theorem eq {S T : OrdSupportClass β} : mk S = mk T ↔ S ∈ orbit (Allowable β) T :=
  Quotient.eq (r := _)

instance : SetLike (OrdSupportClassOrbit β) (OrdSupportClass β) where
  coe o := {S | mk S = o}
  coe_injective' := by
    intro o₁ o₂
    refine Quotient.inductionOn₂ o₁ o₂ ?_
    intro S₁ S₂ h
    simp only [ext_iff, mem_setOf_eq] at h
    exact (h S₁).mp rfl

theorem mem_mk (S : OrdSupportClass β) : S ∈ mk S :=
  rfl

theorem mem_mk_def (S T : OrdSupportClass β) : S ∈ mk T ↔ mk S = mk T := Iff.rfl

@[simp]
theorem mem_mk_iff (S T : OrdSupportClass β) : S ∈ mk T ↔ S ∈ orbit (Allowable β) T := by
  rw [mem_mk_def, mk, mk, ← orbitRel_apply, Quotient.eq (r := _)]
  rfl

@[simp]
theorem mk_smul (S : OrdSupportClass β) (ρ : Allowable β) : mk (ρ • S) = mk S := by
  rw [OrdSupportClassOrbit.eq]
  exact ⟨ρ, rfl⟩

/-- This theorem shows that it doesn't matter whether we take the quotient by equivalence before or
after the quotient by orbits. -/
theorem mk_eq_mk_of_mem_orbit (S T : OrdSupport β) (h : S ∈ orbit (Allowable β) T) :
    mk (OrdSupportClass.mk S) = mk (OrdSupportClass.mk T) := by
  obtain ⟨ρ, rfl⟩ := h
  simp only [OrdSupportClass.smul_mk, mk_smul]

def ofOrbit : OrdSupportOrbit β → OrdSupportClassOrbit β :=
  Quotient.lift (fun S => mk (OrdSupportClass.mk S)) mk_eq_mk_of_mem_orbit

@[simp]
theorem ofOrbit_mk (S : OrdSupport β) :
    ofOrbit (OrdSupportOrbit.mk S) = mk (OrdSupportClass.mk S) :=
  rfl

/-- An ordered support class in this class orbit. -/
noncomputable def chooseClass (o : OrdSupportClassOrbit β) : OrdSupportClass β :=
  (o.out (s := _))

@[simp]
theorem mk_chooseClass (o : OrdSupportClassOrbit β) :
    mk o.chooseClass = o :=
  Quotient.out_eq (s := _) _

theorem chooseClass_mem (o : OrdSupportClassOrbit β) :
    o.chooseClass ∈ o :=
  o.mk_chooseClass

/-- An ordered support orbit in this class orbit. -/
noncomputable def chooseOrbit (o : OrdSupportClassOrbit β) : OrdSupportOrbit β :=
  OrdSupportOrbit.mk (o.chooseClass.out)

@[simp]
theorem ofOrbit_chooseOrbit (o : OrdSupportClassOrbit β) :
    ofOrbit o.chooseOrbit = o := by
  rw [chooseOrbit, ofOrbit_mk, OrdSupportClass.mk, Quotient.out_eq, mk_chooseClass]

theorem mk_mem_of_mem_orbit {S : OrdSupport β} {o : OrdSupportOrbit β} {co : OrdSupportClassOrbit β}
    (hS : S ∈ o) (ho : ofOrbit o = co) : OrdSupportClass.mk S ∈ co := by
  subst ho
  obtain ⟨ρ, rfl⟩ := hS
  simp only [ofOrbit_mk, mem_mk_iff, mem_orbit_self]

end OrdSupportClassOrbit

end ConNF
