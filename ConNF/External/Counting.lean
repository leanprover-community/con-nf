import ConNF.External.Basic

/-!
# New file

In this file...

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal ConNF.TSet

namespace ConNF

variable [Params.{u}] {α β γ δ ε ζ : Λ} (hβ : (β : TypeIndex) < α) (hγ : (γ : TypeIndex) < β)
  (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < δ) (hζ : (ζ : TypeIndex) < ε)

/-- The set `{z ∪ {a} | z ∈ x}`. -/
def insert (x : TSet α) : TSet α :=
  sorry

def cardinalNat (n : ℕ) : TSet α :=
  (TSet.exists_cardinalOne hβ hγ).choose

@[simp]
theorem mem_cardinalNat_iff (n : ℕ) :
    ∀ a : TSet β, a ∈' cardinalNat hβ hγ n ↔
    ∃ s : Finset (TSet γ), s.card = n ∧ ∀ b : TSet γ, b ∈' a ↔ b ∈ s :=
  sorry

end ConNF
