import ConNF.ModelData.CoherentData
import ConNF.FOA.Inflexible

/-!
# New file

In this file...

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}] {β : TypeIndex}

class BaseActionClass (X : Type _) where
  atoms : X → Rel Atom Atom
  atoms_oneOne : ∀ ξ, (atoms ξ).OneOne
  nearLitters : X → Rel NearLitter NearLitter
  nearLitters_oneOne : ∀ ξ, (nearLitters ξ).OneOne

instance {X : Type _} [BaseActionClass X] : SuperA X (Rel Atom Atom) where
  superA := BaseActionClass.atoms

instance {X : Type _} [BaseActionClass X] : SuperN X (Rel NearLitter NearLitter) where
  superN := BaseActionClass.nearLitters

instance {X : Type _} [BaseActionClass X] : SMul X BaseSupport where
  smul ξ S := ⟨Sᴬ.comp ξᴬ (BaseActionClass.atoms_oneOne ξ).toCoinjective,
    Sᴺ.comp ξᴺ (BaseActionClass.nearLitters_oneOne ξ).toCoinjective⟩

instance {X : Type _} [BaseActionClass X] {β : TypeIndex} :
    SMul (Tree X β) (Support β) where
  smul ξ S := ⟨Sᴬ.comp (Enumeration.relWithPath λ A ↦ (ξ A)ᴬ)
      (Enumeration.relWithPath_coinjective
        λ A ↦ (BaseActionClass.atoms_oneOne (ξ A)).toCoinjective),
    Sᴺ.comp (Enumeration.relWithPath λ A ↦ (ξ A)ᴺ)
      (Enumeration.relWithPath_coinjective
        λ A ↦ (BaseActionClass.nearLitters_oneOne (ξ A)).toCoinjective)⟩

theorem smul_atoms {X : Type _} [BaseActionClass X] (ξ : X) (S : BaseSupport) :
    (ξ • S)ᴬ = Sᴬ.comp ξᴬ (BaseActionClass.atoms_oneOne ξ).toCoinjective :=
  rfl

theorem smul_nearLitters {X : Type _} [BaseActionClass X] (ξ : X) (S : BaseSupport) :
    (ξ • S)ᴺ = Sᴺ.comp ξᴺ (BaseActionClass.nearLitters_oneOne ξ).toCoinjective :=
  rfl

theorem smul_baseSupport_eq_smul_iff {X : Type _} [BaseActionClass X]
    (ξ : X) (S : BaseSupport) (π : BasePerm) :
    ξ • S = π • S ↔ (∀ a ∈ Sᴬ, ξᴬ a (π • a)) ∧ (∀ N ∈ Sᴺ, ξᴺ N (π • N)) := by
  constructor
  · intro h
    constructor
    · rintro a ⟨i, ha⟩
      have : (π • S)ᴬ.rel i (π • a) := by
        rwa [BaseSupport.smul_atoms, Enumeration.smul_rel, inv_smul_smul]
      rw [← h] at this
      obtain ⟨b, hb, hξ⟩ := this
      cases Sᴬ.rel_coinjective.coinjective ha hb
      exact hξ
    · rintro a ⟨i, ha⟩
      have : (π • S)ᴺ.rel i (π • a) := by
        rwa [BaseSupport.smul_nearLitters, Enumeration.smul_rel, inv_smul_smul]
      rw [← h] at this
      obtain ⟨b, hb, hξ⟩ := this
      cases Sᴺ.rel_coinjective.coinjective ha hb
      exact hξ
  · intro h
    ext : 2; rfl; swap; rfl
    · ext i a : 3
      rw [smul_atoms, BaseSupport.smul_atoms, Enumeration.smul_rel]
      constructor
      · rintro ⟨b, hb, hξ⟩
        cases (BaseActionClass.atoms_oneOne ξ).coinjective hξ (h.1 b ⟨i, hb⟩)
        rwa [inv_smul_smul]
      · intro ha
        refine ⟨π⁻¹ • a, ha, ?_⟩
        have := h.1 (π⁻¹ • a) ⟨i, ha⟩
        rwa [smul_inv_smul] at this
    · ext i a : 3
      rw [smul_nearLitters, BaseSupport.smul_nearLitters, Enumeration.smul_rel]
      constructor
      · rintro ⟨b, hb, hξ⟩
        cases (BaseActionClass.nearLitters_oneOne ξ).coinjective hξ (h.2 b ⟨i, hb⟩)
        rwa [inv_smul_smul]
      · intro ha
        refine ⟨π⁻¹ • a, ha, ?_⟩
        have := h.2 (π⁻¹ • a) ⟨i, ha⟩
        rwa [smul_inv_smul] at this

@[simp]
theorem smul_support_derivBot {X : Type _} [BaseActionClass X]
    (ξ : Tree X β) (S : Support β) (A : β ↝ ⊥) :
    (ξ • S) ⇘. A = ξ A • (S ⇘. A) := by
  ext : 2; rfl; swap; rfl
  all_goals
  · ext i a
    constructor
    · rintro ⟨⟨B, b⟩, h₁, h₂⟩
      cases h₂.1
      exact ⟨b, h₁, h₂.2⟩
    · rintro ⟨b, h₁, h₂⟩
      exact ⟨⟨A, b⟩, h₁, rfl, h₂⟩

theorem smul_support_eq_smul_iff {X : Type _} [BaseActionClass X]
    (ξ : Tree X β) (S : Support β) (π : StrPerm β) :
    ξ • S = π • S ↔ ∀ A,
      (∀ a ∈ (S ⇘. A)ᴬ, (ξ A)ᴬ a (π A • a)) ∧ (∀ N ∈ (S ⇘. A)ᴺ, (ξ A)ᴺ N (π A • N)) := by
  simp only [Support.ext_iff, smul_support_derivBot, Support.smul_derivBot,
    smul_baseSupport_eq_smul_iff]

theorem smul_support_smul_eq_iff {X : Type _} [BaseActionClass X]
    (ξ : Tree X β) (S : Support β) (π : StrPerm β) :
    ξ • π • S = S ↔ ∀ A,
      (∀ a ∈ ((π • S) ⇘. A)ᴬ, (ξ A)ᴬ a (π⁻¹ A • a)) ∧
      (∀ N ∈ ((π • S) ⇘. A)ᴺ, (ξ A)ᴺ N (π⁻¹ A • N)) := by
  have := smul_support_eq_smul_iff ξ (π • S) π⁻¹
  rw [inv_smul_smul] at this
  rw [this]

variable [Level] [CoherentData]

/-- `ξ` is defined coherently at `(A, L₁, L₂)` (or could be defined coherently at this triple). -/
structure CoherentAt [LeLevel β] {X : Type _} [BaseActionClass X]
    (ξ : Tree X β) (A : β ↝ ⊥) (L₁ L₂ : Litter) : Prop where
  inflexible (P : InflexiblePath β) (t : Tangle P.δ)
    (hA : A = P.A ↘ P.hε ↘.) (ht : L₁ = fuzz P.hδε t) :
    ∃ ρ : AllPerm P.δ, ξ ⇘ P.A ↘ P.hδ • t.support = ρᵁ • t.support ∧ L₂ = fuzz P.hδε (ρ • t)
  flexible (h : ¬Inflexible A L₁) : ¬Inflexible A L₂

theorem coherentAt_inflexible [LeLevel β] {X : Type _} [BaseActionClass X]
    {ξ : Tree X β} {A : β ↝ ⊥} {L₁ L₂ : Litter}
    {P : InflexiblePath β} {t : Tangle P.δ} (hA : A = P.A ↘ P.hε ↘.) (ht : L₁ = fuzz P.hδε t) :
    CoherentAt ξ A L₁ L₂ ↔ ∃ ρ : AllPerm P.δ,
      ξ ⇘ P.A ↘ P.hδ • t.support = ρᵁ • t.support ∧ L₂ = fuzz P.hδε (ρ • t) := by
  constructor
  · intro h
    exact h.inflexible P t hA ht
  · intro h
    constructor
    · intro P' t' hA' ht'
      cases inflexiblePath_subsingleton hA hA' ht ht'
      cases fuzz_injective (ht.symm.trans ht')
      exact h
    · intro h'
      cases h' ⟨P, t, hA, ht⟩

theorem smul_eq_of_coherentAt_inflexible [LeLevel β] {X : Type _} [BaseActionClass X]
    {ξ : Tree X β} {A : β ↝ ⊥} {L₁ L₂ : Litter}
    {P : InflexiblePath β} {t : Tangle P.δ} (hA : A = P.A ↘ P.hε ↘.) (ht : L₁ = fuzz P.hδε t)
    (h : CoherentAt ξ A L₁ L₂) :
    ∀ ρ : AllPerm P.δ, ξ ⇘ P.A ↘ P.hδ • t.support = ρᵁ • t.support → L₂ = fuzz P.hδε (ρ • t) := by
  intro ρ₁ hρ₁
  rw [coherentAt_inflexible hA ht] at h
  obtain ⟨ρ₂, hρ₂, rfl⟩ := h
  congr 1
  apply t.smul_eq_smul
  rw [← hρ₁, ← hρ₂]

theorem coherentAt_flexible [LeLevel β] {X : Type _} [BaseActionClass X]
    {ξ : Tree X β} {A : β ↝ ⊥} {L₁ L₂ : Litter}
    (hL : ¬Inflexible A L₁) :
    CoherentAt ξ A L₁ L₂ ↔ ¬Inflexible A L₂ := by
  constructor
  · intro h
    exact h.flexible hL
  · intro h
    constructor
    · intro P t hA ht
      cases hL ⟨P, t, hA, ht⟩
    · intro
      exact h

theorem coherentAt_inflexible' [LeLevel β] {X : Type _} [BaseActionClass X]
    {ξ : Tree X β} {A : β ↝ ⊥} {L₁ L₂ : Litter}
    {P : InflexiblePath β} {t : Tangle P.δ} (hA : A = P.A ↘ P.hε ↘.) (ht : L₂ = fuzz P.hδε t) :
    CoherentAt ξ A L₁ L₂ ↔ ∃ ρ : AllPerm P.δ,
      ξ ⇘ P.A ↘ P.hδ • ρᵁ • t.support = t.support ∧ L₁ = fuzz P.hδε (ρ • t) := by
  constructor
  · intro h
    obtain (⟨P', t', hA', ht'⟩ | hL) := inflexible_cases A L₁
    · obtain ⟨ρ, h₁, h₂⟩ := h.inflexible P' t' hA' ht'
      cases inflexiblePath_subsingleton hA hA' ht h₂
      cases fuzz_injective <| ht.symm.trans h₂
      use ρ⁻¹
      rw [inv_smul_smul, Tangle.smul_support, ht', allPermForget_inv, inv_smul_smul, h₁]
      exact ⟨rfl, rfl⟩
    · rw [coherentAt_flexible hL] at h
      cases h ⟨P, t, hA, ht⟩
  · intro h
    obtain ⟨ρ, h₁, h₂⟩ := h
    constructor
    · intro P' t' hA' ht'
      cases inflexiblePath_subsingleton hA hA' h₂ ht'
      cases fuzz_injective <| h₂.symm.trans ht'
      refine ⟨ρ⁻¹, ?_, ?_⟩
      · rwa [Tangle.smul_support, allPermForget_inv, inv_smul_smul]
      · rwa [inv_smul_smul]
    · intro h
      cases h ⟨P, ρ • t, hA, h₂⟩

theorem smul_eq_of_coherentAt_inflexible' [LeLevel β] {X : Type _} [BaseActionClass X]
    {ξ : Tree X β} {A : β ↝ ⊥} {L₁ L₂ : Litter}
    {P : InflexiblePath β} {t : Tangle P.δ} (hA : A = P.A ↘ P.hε ↘.) (ht : L₂ = fuzz P.hδε t)
    (h : CoherentAt ξ A L₁ L₂) :
    ∀ ρ : AllPerm P.δ, ξ ⇘ P.A ↘ P.hδ • ρᵁ • t.support = t.support → L₁ = fuzz P.hδε (ρ • t) := by
  intro ρ₁ hρ₁
  rw [coherentAt_inflexible' hA ht] at h
  obtain ⟨ρ₂, hρ₂, rfl⟩ := h
  congr 1
  apply t.smul_eq_smul
  rw [smul_support_smul_eq_iff] at hρ₁ hρ₂
  ext B : 1
  rw [Support.smul_derivBot, Support.smul_derivBot, BaseSupport.smul_eq_smul_iff]
  constructor
  · rintro a ha
    have h₁ := (hρ₁ B).1 (ρ₁ᵁ B • a) ?_
    have h₂ := (hρ₂ B).1 (ρ₂ᵁ B • a) ?_
    · rw [Tree.inv_apply, inv_smul_smul] at h₁ h₂
      exact (BaseActionClass.atoms_oneOne _).injective h₂ h₁
    · rwa [Support.smul_derivBot, BaseSupport.smul_atoms, Enumeration.mem_smul_iff, inv_smul_smul]
    · rwa [Support.smul_derivBot, BaseSupport.smul_atoms, Enumeration.mem_smul_iff, inv_smul_smul]
  · rintro N hN
    have h₁ := (hρ₁ B).2 (ρ₁ᵁ B • N) ?_
    have h₂ := (hρ₂ B).2 (ρ₂ᵁ B • N) ?_
    · rw [Tree.inv_apply, inv_smul_smul] at h₁ h₂
      exact (BaseActionClass.nearLitters_oneOne _).injective h₂ h₁
    · rwa [Support.smul_derivBot, BaseSupport.smul_nearLitters,
        Enumeration.mem_smul_iff, inv_smul_smul]
    · rwa [Support.smul_derivBot, BaseSupport.smul_nearLitters,
        Enumeration.mem_smul_iff, inv_smul_smul]

theorem CoherentAt.deriv [LeLevel β] {γ : TypeIndex} [LeLevel γ] {X : Type _} [BaseActionClass X]
    {ξ : Tree X β} {L₁ L₂ : Litter} (A : β ↝ γ) (B : γ ↝ ⊥) (h : CoherentAt ξ (A ⇘ B) L₁ L₂) :
    CoherentAt (ξ ⇘ A) B L₁ L₂ := by
  constructor
  · intro P t hA ht
    have := h.inflexible (P ⇗ A) t ?_ ht
    · obtain ⟨ρ, hρ₁, hρ₂⟩ := this
      refine ⟨ρ, ?_, hρ₂⟩
      rwa [InflexiblePath.coderiv_A, ← Tree.deriv_deriv] at hρ₁
    · rw [hA]
      rfl
  · intro hL₁ hL₂
    obtain (hL₁' | hL₁') := inflexible_cases (A ⇘ B) L₁
    · obtain ⟨P, t, rfl, ht⟩ := hL₂
      obtain ⟨P', t', hA', ht'⟩ := hL₁'
      suffices P' = P ⇗ A by
        cases this
        cases hL₁ ⟨P, t', rfl, ht'⟩
      rw [coherentAt_inflexible hA' ht'] at h
      obtain ⟨ρ, hρ₁, hρ₂⟩ := h
      rw [Path.deriv_sderivBot, Path.deriv_sderiv] at hA'
      exact inflexiblePath_subsingleton hA' rfl hρ₂ ht
    · cases h.flexible hL₁' (inflexible_deriv hL₂ A)

end ConNF
