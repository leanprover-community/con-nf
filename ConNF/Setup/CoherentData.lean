import ConNF.Setup.Fuzz
import ConNF.Setup.Level
import ConNF.Setup.ModelData

/-!
# Coherent data

In this file, we define the type of coherent data below a particular proper type index.

## Main declarations

* `ConNF.CoherentData`: Coherent data below a given level `α`.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

/-!
TODO: We're going to try allowing model data at level `⊥` to vary. That is, we use
`(β : TypeIndex) → [LeLevel β] → ModelData β` instead of `(β : Λ) → [LeLevel β] → ModelData β`.
-/

variable [Params.{u}] [Level]

/-- A convenience typeclass to hold data below the current level. -/
class LtData where
  [data : (β : TypeIndex) → [LeLevel β] → ModelData β]
  [positions : (β : TypeIndex) → [LtLevel β] → Position (Tangle β)]

instance [LtData] : (β : TypeIndex) → [LeLevel β] → ModelData β :=
  LtData.data

instance [LtData] : (β : TypeIndex) → [LtLevel β] → Position (Tangle β) :=
  LtData.positions

class PreCoherentData extends LtData where
  allPermSderiv {β γ : TypeIndex} [LeLevel β] [LeLevel γ] (h : γ < β) : AllPerm β → AllPerm γ
  singleton {β γ : TypeIndex} [LeLevel β] [LeLevel γ] (h : γ < β) : TSet γ → TSet β

export PreCoherentData (singleton)

instance [PreCoherentData] {β γ : TypeIndex} [LeLevel β] [LeLevel γ] :
    Derivative (AllPerm β) (AllPerm γ) β γ where
  deriv ρ A := A.recSderiv
    (motive := λ (δ : TypeIndex) (A : β ↝ δ) ↦
      letI : LeLevel δ := ⟨A.le.trans LeLevel.elim⟩; AllPerm δ)
    ρ (λ δ ε A h ρ ↦
      letI : LeLevel δ := ⟨A.le.trans LeLevel.elim⟩
      letI : LeLevel ε := ⟨h.le.trans LeLevel.elim⟩
      PreCoherentData.allPermSderiv h ρ)

@[simp]
theorem allPerm_deriv_nil [PreCoherentData] {β : TypeIndex} [LeLevel β]
    (ρ : AllPerm β) :
    ρ ⇘ (.nil : β ↝ β) = ρ :=
  rfl

@[simp]
theorem allPerm_deriv_sderiv [PreCoherentData] {β γ δ : TypeIndex}
    [LeLevel β] [LeLevel γ] [LeLevel δ]
    (ρ : AllPerm β) (A : β ↝ γ) (h : δ < γ) :
    ρ ⇘ (A ↘ h) = ρ ⇘ A ↘ h :=
  rfl

class CoherentData extends PreCoherentData where
  allPermSderiv_forget {β γ : TypeIndex} [LeLevel β] [LeLevel γ] (h : γ < β) (ρ : AllPerm β) :
    (ρ ↘ h)ᵁ = ρᵁ ↘ h
  pos_atom_lt_pos {β : TypeIndex} [LtLevel β] (t : Tangle β) (A : β ↝ ⊥) (a : Atom) :
    a ∈ (t.support ⇘. A)ᴬ → pos a < pos t
  pos_nearLitter_lt_pos {β : TypeIndex} [LtLevel β] (t : Tangle β) (A : β ↝ ⊥) (N : NearLitter) :
    N ∈ (t.support ⇘. A)ᴺ → pos N < pos t
  smul_fuzz {γ δ : TypeIndex} {ε : Λ} [LeLevel γ] [LtLevel δ] [LtLevel ε]
    (hδ : δ < γ) (hε : ε < γ) (hδε : δ ≠ ε) (ρ : AllPerm γ) (t : Tangle δ) :
    ρᵁ ↘ hε ↘. • fuzz hδε t = fuzz hδε (ρ ↘ hδ • t)
  allPerm_of_basePerm (π : BasePerm) : ∃ ρ : AllPerm ⊥, ρᵁ Path.nil = π
  allPerm_of_smulFuzz {γ : Λ} [LeLevel γ]
    (ρs : {δ : TypeIndex} → [LtLevel δ] → δ < γ → AllPerm δ)
    (h : ∀ {δ : TypeIndex} {ε : Λ} [LeLevel γ] [LtLevel δ] [LtLevel ε]
      (hδ : δ < γ) (hε : (ε : TypeIndex) < γ) (hδε : δ ≠ ε) (t : Tangle δ),
      (ρs hε)ᵁ ↘. • fuzz hδε t = fuzz hδε (ρs hδ • t)) :
    ∃ ρ : AllPerm γ, ∀ δ : TypeIndex, [LtLevel δ] → ∀ hδ : δ < γ, ρ ↘ hδ = ρs hδ
  tSet_ext {β γ : Λ} [LeLevel β] [LeLevel γ] (hγ : (γ : TypeIndex) < β) (x y : TSet β)
      (h : ∀ z : TSet γ, z ∈[hγ] x ↔ z ∈[hγ] y) : x = y
  typedMem_tSetForget {β : Λ} {γ : TypeIndex} [LeLevel β] [LeLevel γ]
    (hγ : γ < β) (x : TSet β) (y : StrSet γ) :
    y ∈[hγ] xᵁ → ∃ z : TSet γ, y = zᵁ
  typedMem_singleton_iff {β γ : TypeIndex} [LeLevel β] [LeLevel γ] (hγ : γ < β) (x y : TSet γ) :
    y ∈[hγ] singleton hγ x ↔ y = x

export CoherentData (allPermSderiv_forget pos_atom_lt_pos pos_nearLitter_lt_pos smul_fuzz
  allPerm_of_basePerm allPerm_of_smulFuzz tSet_ext typedMem_tSetForget typedMem_singleton_iff)

attribute [simp] allPermSderiv_forget typedMem_singleton_iff

@[simp]
theorem allPermDeriv_forget [CoherentData] {β γ : TypeIndex} [LeLevel β] [iγ : LeLevel γ]
    (A : β ↝ γ) (ρ : AllPerm β) :
    (ρ ⇘ A)ᵁ = ρᵁ ⇘ A := by
  revert iγ
  induction A with
  | nil =>
    intro
    rw [allPerm_deriv_nil, Tree.deriv_nil]
  | sderiv δ ε A h ih =>
    intro
    have : LeLevel δ := ⟨A.le.trans LeLevel.elim⟩
    rw [allPerm_deriv_sderiv, allPermSderiv_forget, ih, Tree.deriv_sderiv]

theorem allPerm_inv_sderiv [CoherentData] {β γ : TypeIndex} [LeLevel β] [iγ : LeLevel γ]
    (h : γ < β) (ρ : AllPerm β) :
    ρ⁻¹ ↘ h = (ρ ↘ h)⁻¹ := by
  apply allPermForget_injective
  rw [allPermSderiv_forget, allPermForget_inv, Tree.inv_sderiv, allPermForget_inv,
    allPermSderiv_forget]

theorem TSet.mem_smul_iff [CoherentData] {β γ : TypeIndex} [LeLevel β] [iγ : LeLevel γ]
    {x : TSet γ} {y : TSet β} (h : γ < β) (ρ : AllPerm β) :
    x ∈[h] ρ • y ↔ ρ⁻¹ ↘ h • x ∈[h] y := by
  simp only [← forget_mem_forget, smul_forget, StrSet.mem_smul_iff, allPermSderiv_forget,
    allPermForget_inv, Tree.inv_sderiv]

end ConNF
