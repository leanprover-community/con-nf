import ConNF.Setup.CoherentData
import ConNF.Construction.Code

/-!
# New file

In this file...

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal WithBot

namespace ConNF

variable [Params.{u}]

structure Motive (α : Λ) where
  data : ModelData α
  pos : Position (Tangle α)
  typed : TypedNearLitters α

theorem card_tangle_bot_le [ModelData ⊥] : #(Tangle ⊥) ≤ #μ := by
  apply card_tangle_le_of_card_tSet
  apply (mk_le_of_injective (ModelData.tSetForget_injective' (α := ⊥))).trans
  apply (mk_le_of_injective StrSet.botEquiv.injective).trans
  rw [card_atom]

def botPosition [ModelData ⊥] : Position (Tangle ⊥) where
  pos := ⟨funOfDeny card_tangle_bot_le (λ t ↦ pos '' (t.supportᴬ.image Prod.snd : Set Atom))
      (λ _ ↦ sorry),
    funOfDeny_injective _ _ _⟩

theorem pos_tangle_bot {D : ModelData ⊥} (t : Tangle ⊥) (a : Atom) (A : ⊥ ↝ ⊥)
    (ha : a ∈ (t.support ⇘. A)ᴬ) :
    letI := botPosition
    pos a < pos t := by
  refine funOfDeny_gt_deny _ _ _ _ _ ⟨_, ?_, rfl⟩
  obtain ⟨i, hi⟩ := ha
  exact ⟨i, ⟨A, a⟩, hi, rfl⟩

structure Hypothesis {α : Λ} (M : Motive α) (N : (β : Λ) → (β : TypeIndex) < α → Motive β) where
  allPermSderiv {β : Λ} (h : (β : TypeIndex) < α) : M.data.AllPerm → (N β h).data.AllPerm
  allPermBotSderiv : M.data.AllPerm → botModelData.AllPerm
  singleton {β : Λ} (h : (β : TypeIndex) < α) : (N β h).data.TSet → M.data.TSet
  allPermSderiv_forget {β : Λ} (h : (β : TypeIndex) < α) (ρ : M.data.AllPerm) :
    (N β h).data.allPermForget (allPermSderiv h ρ) = M.data.allPermForget ρ ↘ h
  allPermBotSderiv_forget (ρ : M.data.AllPerm) :
    botModelData.allPermForget (allPermBotSderiv ρ) = M.data.allPermForget ρ ↘ bot_lt_coe _
  pos_atom_lt_pos :
    letI := M.data; letI := M.pos
    ∀ (t : Tangle α) (A : α ↝ ⊥) (a : Atom), a ∈ (t.support ⇘. A)ᴬ → pos a < pos t
  pos_nearLitter_lt_pos :
    letI := M.data; letI := M.pos
    ∀ (t : Tangle α) (A : α ↝ ⊥) (N : NearLitter), N ∈ (t.support ⇘. A)ᴺ → pos N < pos t
  smul_fuzz {β γ : Λ} (hβ : (β : TypeIndex) < α)
      (hγ : (γ : TypeIndex) < α) (hβγ : (β : TypeIndex) ≠ γ) :
    letI := (N β hβ).data; letI := (N β hβ).pos
    ∀ (ρ : M.data.AllPerm) (t : Tangle β),
    M.data.allPermForget ρ ↘ hγ ↘. • fuzz hβγ t = fuzz hβγ (allPermSderiv hβ ρ • t)
  smul_fuzz_bot {γ : Λ} (hγ : (γ : TypeIndex) < α) :
    letI := botModelData; letI := botPosition
    ∀ (ρ : M.data.AllPerm) (t : Tangle ⊥),
    M.data.allPermForget ρ ↘ hγ ↘. • fuzz (bot_ne_coe (a := γ)) t =
      fuzz (bot_ne_coe (a := γ)) (allPermBotSderiv ρ • t)
  allPerm_of_smul_fuzz :
    ∀ (ρs : {β : Λ} → (hβ : (β : TypeIndex) < α) → (N β hβ).data.AllPerm)
    (π : letI := botModelData; AllPerm ⊥),
    (∀ {β γ : Λ} (hβ : (β : TypeIndex) < α) (hγ : (γ : TypeIndex) < α),
      letI := (N β hβ).data; letI := (N β hβ).pos
      ∀ (hδε : (β : TypeIndex) ≠ γ) (t : Tangle β),
      (ρs hγ)ᵁ ↘. • fuzz hδε t = fuzz hδε (ρs hβ • t)) →
    (∀ {γ : Λ} (hγ : (γ : TypeIndex) < α) (t : letI := botModelData; Tangle ⊥),
      letI := botModelData; letI := botPosition
      (ρs hγ)ᵁ ↘. • fuzz (bot_ne_coe (a := γ)) t = fuzz (bot_ne_coe (a := γ)) (π • t)) →
    ∃ ρ : M.data.AllPerm,
      (∀ (β : Λ) (hβ : (β : TypeIndex) < α), allPermSderiv hβ ρ = ρs hβ) ∧
      allPermBotSderiv ρ = π
  tSet_ext (β : Λ) (hβ : (β : TypeIndex) < α) (x y : M.data.TSet) :
    (∀ z : (N β hβ).data.TSet, z ∈[hβ] x ↔ z ∈[hβ] y) → x = y
  typedMem_singleton_iff {β : Λ} (hβ : (β : TypeIndex) < α) (x y : (N β hβ).data.TSet) :
    y ∈[hβ] singleton hβ x ↔ y = x

def castTSet {α β : TypeIndex} {D₁ : ModelData α} {D₂ : ModelData β}
    (h₁ : α = β) (h₂ : HEq D₁ D₂) :
    D₁.TSet ≃ D₂.TSet := by cases h₁; rw [eq_of_heq h₂]

def castAllPerm {α β : TypeIndex} {D₁ : ModelData α} {D₂ : ModelData β}
    (h₁ : α = β) (h₂ : HEq D₁ D₂) :
    D₁.AllPerm ≃ D₂.AllPerm := by cases h₁; rw [eq_of_heq h₂]

def castTangle {α β : TypeIndex} {D₁ : ModelData α} {D₂ : ModelData β}
    (h₁ : α = β) (h₂ : HEq D₁ D₂) :
    (letI := D₁; Tangle α) ≃ (letI := D₂; Tangle β) := by cases h₁; rw [eq_of_heq h₂]

theorem castTSet_forget {α : TypeIndex} {D₁ D₂ : ModelData α} (h₂ : HEq D₁ D₂) (ρ : D₁.TSet) :
    D₂.tSetForget (castTSet rfl h₂ ρ) = D₁.tSetForget ρ := by cases h₂; rfl

theorem castAllPerm_forget {α : TypeIndex} {D₁ D₂ : ModelData α} (h₂ : HEq D₁ D₂) (ρ : D₁.AllPerm) :
    D₂.allPermForget (castAllPerm rfl h₂ ρ) = D₁.allPermForget ρ := by cases h₂; rfl

theorem castTangle_support {α : TypeIndex} {D₁ D₂ : ModelData α} (h₂ : HEq D₁ D₂)
    (t : letI := D₁; Tangle α) :
    (castTangle rfl h₂ t).support = letI := D₁; t.support := by cases h₂; rfl

theorem castAllPerm_smul {α : TypeIndex} {D₁ D₂ : ModelData α} (h₂ : HEq D₁ D₂)
    (ρ : D₂.AllPerm) (t : letI := D₁; Tangle α) :
    ρ • (castTangle rfl h₂ t) = letI := D₁; castTangle rfl h₂ ((castAllPerm rfl h₂).symm ρ • t) :=
  by cases h₂; rfl

theorem castTangle_pos {α β : TypeIndex} {D₁ : ModelData α} {D₂ : ModelData β}
    {E₁ : Position (Tangle α)} {E₂ : Position (Tangle β)}
    (h₁ : α = β) (h₂ : HEq D₁ D₂) (h₃ : HEq E₁ E₂) (t : Tangle α) :
    pos (castTangle h₁ h₂ t) = pos t := by cases h₁; cases h₂; cases h₃; rfl

theorem castTangle_fuzz {α : TypeIndex} {D₁ D₂ : ModelData α}
    {E₁ : letI := D₁; Position (Tangle α)} {E₂ : letI := D₂; Position (Tangle α)}
    (h₂ : HEq D₁ D₂) (h₃ : HEq E₁ E₂) (t : letI := D₁; Tangle α) {β : Λ} (hαβ : α ≠ β) :
    (letI := D₂; fuzz hαβ (castTangle rfl h₂ t)) = (letI := D₁; fuzz hαβ t) :=
  by cases h₂; cases h₃; rfl

end ConNF
