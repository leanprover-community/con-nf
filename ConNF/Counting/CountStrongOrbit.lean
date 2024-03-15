import ConNF.Counting.ExistsSpec
import ConNF.Counting.SpecSMul
import ConNF.Counting.SpecSame
import ConNF.Counting.SupportOrbit

open Quiver Set Sum WithBot

open scoped symmDiff

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ} [LeLevel β]

theorem SupportOrbit.hasSpec (o : SupportOrbit β) (ho : o.Strong) :
    ∃ σ : Spec β, ∀ S (hS : S ∈ o), σ.Specifies S (ho S hS) := by
  revert ho
  refine inductionOn
    (motive := fun o => ∀ (ho : o.Strong),
      ∃ σ : Spec β, ∀ S (hS : S ∈ o), σ.Specifies S (ho S hS)) o ?_
  intro S ho
  refine ⟨S.spec (ho S (mem_mk S)), ?_⟩
  intro T hT
  rw [mem_mk_iff] at hT
  obtain ⟨ρ, rfl⟩ := hT
  exact (S.spec_specifies (ho S (mem_mk S))).smul ρ

noncomputable def SupportOrbit.spec (o : SupportOrbit β) (ho : o.Strong) : Spec β :=
  (o.hasSpec ho).choose

theorem SupportOrbit.spec_specifies (o : SupportOrbit β) (ho : o.Strong)
    (S : Support β) (hS : S ∈ o) : (o.spec ho).Specifies S (ho S hS) :=
  (o.hasSpec ho).choose_spec S hS

theorem SupportOrbit.spec_injective (o₁ o₂ : SupportOrbit β)
    (ho₁ : o₁.Strong) (ho₂ : o₂.Strong) (h : o₁.spec ho₁ = o₂.spec ho₂) :
    o₁ = o₂ := by
  revert ho₁ ho₂ h
  refine inductionOn (motive := fun o =>
    ∀ (ho₁ : o.Strong) (ho₂ : o₂.Strong), o.spec ho₁ = o₂.spec ho₂ → o = o₂) o₁ ?_
  intro S₁
  refine inductionOn (motive := fun o =>
    ∀ (ho₁ : (mk S₁).Strong) (ho₂ : o.Strong),
      (mk S₁).spec ho₁ = o.spec ho₂ → (mk S₁) = o) o₂ ?_
  intro S₂
  intro hS₁ hS₂ h
  have h₁ := spec_specifies (mk S₁) hS₁ S₁ (mem_mk S₁)
  have h₂ := spec_specifies (mk S₂) hS₂ S₂ (mem_mk S₂)
  rw [h] at h₁
  have := convertAllowable_smul h₂ h₁
  rw [← mem_def, mem_mk_iff]
  exact ⟨_, this⟩

end ConNF
