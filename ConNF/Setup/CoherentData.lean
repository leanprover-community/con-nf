import ConNF.Setup.Fuzz
import ConNF.Setup.Level
import ConNF.Setup.ModelData

/-!
# Coherent data

In this file, we define the type of coherent data below a particular proper type index.

## Main declarations

* `ConNF.InflexiblePath`: A pair of paths starting at `β` that describe a particular way to use
    a `fuzz` map.
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

instance [PreCoherentData] {β γ : TypeIndex} [LeLevel β] [LeLevel γ] :
    Derivative (AllPerm β) (AllPerm γ) β γ where
  deriv ρ A := A.recSderiv
    (motive := λ (δ : TypeIndex) (A : β ↝ δ) ↦
      letI : LeLevel δ := ⟨A.le.trans LeLevel.elim⟩; AllPerm δ)
    ρ (λ δ ε A h ρ ↦
      letI : LeLevel δ := ⟨A.le.trans LeLevel.elim⟩
      letI : LeLevel ε := ⟨h.le.trans LeLevel.elim⟩
      PreCoherentData.allPermSderiv h ρ)

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
  exists_of_smulFuzz {γ : TypeIndex} [LeLevel γ]
    (ρs : {δ : TypeIndex} → [LtLevel δ] → δ < γ → AllPerm δ)
    (h : ∀ {δ : TypeIndex} {ε : Λ} [LeLevel γ] [LtLevel δ] [LtLevel ε]
      (hδ : δ < γ) (hε : ε < γ) (hδε : δ ≠ ε) (t : Tangle δ),
      (ρs hε)ᵁ ↘. • fuzz hδε t = fuzz hδε (ρs hδ • t)) :
    ∃ ρ : AllPerm γ, ∀ δ : TypeIndex, [LtLevel δ] → ∀ hδ : δ < γ, ρ ↘ hδ = ρs hδ
  typedMem_tSetForget {β : Λ} {γ : TypeIndex} [LeLevel β] [LeLevel γ]
    (hγ : γ < β) (x : TSet β) (y : StrSet γ) :
    y ∈[hγ] xᵁ → ∃ z : TSet γ, y = zᵁ
  typedMem_singleton_iff {β γ : TypeIndex} [LeLevel β] [LeLevel γ] (hγ : γ < β) (x y : TSet γ) :
    y ∈[hγ] singleton hγ x ↔ y = x

export CoherentData (allPermSderiv_forget pos_atom_lt_pos pos_nearLitter_lt_pos smul_fuzz
  exists_of_smulFuzz typedMem_tSetForget typedMem_singleton_iff)

attribute [simp] allPermSderiv_forget typedMem_singleton_iff

end ConNF
