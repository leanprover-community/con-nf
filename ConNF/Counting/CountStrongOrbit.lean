import ConNF.Counting.ExistsSpec
import ConNF.Counting.SpecSMul
import ConNF.Counting.SpecSame
import ConNF.Counting.SupportOrbit

open Quiver Set Sum WithBot

open scoped Cardinal symmDiff

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ} [LeLevel β]

/-- A morphism of supports `S → T`. -/
structure SupportHom (S T : Support β) : Type u where
  f : κ → κ
  hf (i : κ) (hi : i < S.max) : f i < T.max
  f_eq (i : κ) (hi : i < S.max) : S.f i hi = T.f (f i) (hf i hi)

theorem Support.exists_hom_strongSupport (S : Support β) :
    Nonempty (SupportHom S (strongSupport S.small)) := by
  have := subset_strongSupport S.small
  choose I hI₁ hI₂ using this
  refine ⟨⟨fun i => if h : i < S.max then I ⟨i, h, rfl⟩ else 0, ?_, ?_⟩⟩
  · intro i hi
    simp only [dif_pos hi]
    exact hI₁ _
  · intro i hi
    simp only [dif_pos hi]
    exact hI₂ _

@[ext]
theorem SupportHom.ext {S T : Support β} {F G : SupportHom S T} (h : F.f = G.f) :
    F = G := by
  obtain ⟨f, _, _⟩ := F
  obtain ⟨g, _, _⟩ := G
  cases h
  rfl

def SupportHom.smul {S T : Support β} (F : SupportHom S T) (ρ : Allowable β) :
    SupportHom (ρ • S) (ρ • T) where
  f := F.f
  hf := F.hf
  f_eq i hi := by rw [Enumeration.smul_f, Enumeration.smul_f, F.f_eq]

@[simp]
theorem SupportHom.smul_f {S T : Support β} (F : SupportHom S T) (ρ : Allowable β) :
    (F.smul ρ).f = F.f :=
  rfl

theorem SupportHom.smul_eq {S₁ S₂ T₁ T₂ : Support β} {ρ : Allowable β}
    {F₁ : SupportHom S₁ T₁} {F₂ : SupportHom S₂ T₂} (hF : F₁.f = F₂.f)
    (h : ρ • T₁ = T₂) (h' : S₁.max = S₂.max) :
    ρ • S₁ = S₂ := by
  refine Enumeration.ext' h' ?_
  intro i hi₁ hi₂
  rw [Enumeration.smul_f, F₁.f_eq, F₂.f_eq, ← Enumeration.smul_f]
  simp_rw [h, hF]

/-- A specification for a not-necessarily-strong support. -/
structure WeakSpec (β : Λ) : Type u where
  max : κ
  f : κ → κ
  σ : Spec β

def WeakSpec.Specifies (W : WeakSpec β) (S : Support β) : Prop :=
  ∃ (T : Support β) (hT : T.Strong) (F : SupportHom S T),
    W.max = S.max ∧ W.f = F.f ∧ W.σ.Specifies T hT

theorem Support.hasWeakSpec (S : Support β) : ∃ W : WeakSpec β, W.Specifies S := by
  obtain ⟨F⟩ := S.exists_hom_strongSupport
  refine ⟨⟨S.max, F.f, (strongSupport S.small).spec (strongSupport_strong S.small)⟩, ?_⟩
  exact ⟨strongSupport S.small, strongSupport_strong S.small, F, rfl, rfl,
    (strongSupport S.small).spec_specifies (strongSupport_strong S.small)⟩

theorem WeakSpec.Specifies.smul {W : WeakSpec β} {S : Support β}
    (h : W.Specifies S) (ρ : Allowable β) :
    W.Specifies (ρ • S) := by
  obtain ⟨T, hT, F, hWm, hWf, hWσ⟩ := h
  exact ⟨ρ • T, hT.smul ρ, F.smul ρ, hWm, hWf, hWσ.smul ρ⟩

theorem SupportOrbit.hasWeakSpec (o : SupportOrbit β) :
    ∃ W : WeakSpec β, ∀ S ∈ o, W.Specifies S := by
  refine inductionOn (motive := fun o => ∃ W : WeakSpec β, ∀ S ∈ o, W.Specifies S) o ?_
  intro S
  obtain ⟨W, hW⟩ := S.hasWeakSpec
  refine ⟨W, ?_⟩
  intro T hT
  rw [mem_mk_iff] at hT
  obtain ⟨ρ, rfl⟩ := hT
  exact hW.smul ρ

noncomputable def SupportOrbit.weakSpec (o : SupportOrbit β) : WeakSpec β :=
  o.hasWeakSpec.choose

theorem SupportOrbit.weakSpec_specifies (o : SupportOrbit β)
    (S : Support β) (hS : S ∈ o) : o.weakSpec.Specifies S :=
  o.hasWeakSpec.choose_spec S hS

theorem SupportOrbit.spec_injective (o₁ o₂ : SupportOrbit β) (h : o₁.weakSpec = o₂.weakSpec) :
    o₁ = o₂ := by
  revert h
  refine inductionOn (motive := fun o => o.weakSpec = o₂.weakSpec → o = o₂) o₁ ?_
  intro S₁
  refine inductionOn (motive := fun o => (mk S₁).weakSpec = o.weakSpec → (mk S₁) = o) o₂ ?_
  intro S₂
  intro h
  obtain ⟨T₁, hT₁, F₁, hWm₁, hWf₁, hWT₁⟩ := weakSpec_specifies (mk S₁) S₁ (mem_mk S₁)
  obtain ⟨T₂, hT₂, F₂, hWm₂, hWf₂, hWT₂⟩ := weakSpec_specifies (mk S₂) S₂ (mem_mk S₂)
  rw [h] at hWf₁ hWT₁
  have := convertAllowable_smul hWT₂ hWT₁
  rw [← mem_def, mem_mk_iff]
  refine ⟨convertAllowable hWT₂ hWT₁, ?_⟩
  refine SupportHom.smul_eq (hWf₂.symm.trans hWf₁) this ?_
  rw [← hWm₁, ← hWm₂, h]

theorem mk_supportOrbit_le_mk_weakSpec (β : Λ) [LeLevel β] :
    #(SupportOrbit β) ≤ #(WeakSpec β) :=
  ⟨⟨SupportOrbit.weakSpec, SupportOrbit.spec_injective⟩⟩

end ConNF
