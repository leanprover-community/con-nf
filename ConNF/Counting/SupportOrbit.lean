import Mathlib.GroupTheory.GroupAction.Basic
import ConNF.Counting.StrongSupport

open Quiver Set Sum WithBot

open scoped symmDiff

universe u

namespace ConNF

variable [Params.{u}]

def SupportOrbit (β : Λ) [ModelData β] : Type u :=
  MulAction.orbitRel.Quotient (Allowable β) (Support β)

namespace SupportOrbit

variable {β : Λ} [ModelData β]

/-- The orbit of a given ordered support. -/
def mk (S : Support β) : SupportOrbit β :=
  ⟦S⟧

protected theorem eq {S T : Support β} : mk S = mk T ↔ S ∈ MulAction.orbit (Allowable β) T :=
  Quotient.eq (r := _)

instance : SetLike (SupportOrbit β) (Support β) where
  coe o := {S | mk S = o}
  coe_injective' := by
    intro o₁ o₂
    refine Quotient.inductionOn₂ o₁ o₂ ?_
    intro S₁ S₂ h
    simp only [ext_iff, mem_setOf_eq] at h
    exact (h S₁).mp rfl

theorem mem_mk (S : Support β) : S ∈ mk S :=
  rfl

theorem mem_def (S : Support β) (o : SupportOrbit β) : S ∈ o ↔ mk S = o := Iff.rfl

@[simp]
theorem mem_mk_iff (S T : Support β) : S ∈ mk T ↔ S ∈ MulAction.orbit (Allowable β) T := by
  rw [mem_def, mk, mk, ← MulAction.orbitRel_apply, Quotient.eq (r := _)]
  rfl

theorem smul_mem_of_mem {S : Support β} {o : SupportOrbit β} (ρ : Allowable β) (h : S ∈ o) :
    ρ • S ∈ o := by
  refine Quotient.inductionOn o ?_ h
  intro T hST
  change _ ∈ mk _ at hST ⊢
  rw [mem_mk_iff] at hST ⊢
  obtain ⟨ρ', rfl⟩ := hST
  rw [smul_smul]
  exact ⟨ρ * ρ', rfl⟩

theorem smul_mem_iff_mem {S : Support β} {o : SupportOrbit β} (ρ : Allowable β) :
    ρ • S ∈ o ↔ S ∈ o := by
  refine ⟨?_, smul_mem_of_mem ρ⟩
  intro h
  have := smul_mem_of_mem ρ⁻¹ h
  rw [inv_smul_smul] at this
  exact this

theorem eq_of_mem_orbit {o₁ o₂ : SupportOrbit β} {S₁ S₂ : Support β}
    (h₁ : S₁ ∈ o₁) (h₂ : S₂ ∈ o₂) (h : S₁ ∈ MulAction.orbit (Allowable β) S₂) : o₁ = o₂ := by
  rw [mem_def] at h₁ h₂
  rw [← h₁, ← h₂, SupportOrbit.eq]
  exact h

theorem inductionOn {motive : SupportOrbit β → Prop} (o : SupportOrbit β) (h : ∀ S, motive (mk S)) :
    motive o :=
  Quotient.inductionOn o h

theorem nonempty (o : SupportOrbit β) : Set.Nonempty {S | S ∈ o} := by
  refine inductionOn (motive := fun o => Set.Nonempty {S | S ∈ o}) o ?_
  intro S
  exact ⟨S, mem_mk _⟩

noncomputable def out (o : SupportOrbit β) : Support β :=
  Quotient.out (s := _) o

theorem out_mem (o : SupportOrbit β) : o.out ∈ o :=
  Quotient.out_eq (s := _) o

theorem eq_mk_of_mem {S : Support β} {o : SupportOrbit β} (h : S ∈ o) : o = mk S :=
  h.symm

/-- An orbit of ordered supports is *strong* if it contains a strong support. -/
def Strong [BasePositions] [Level] [FOAAssumptions] {β : Λ} [LeLevel β]
    (o : SupportOrbit β) : Prop :=
  ∀ S ∈ o, S.Strong

end SupportOrbit

end ConNF
