import ConNF.Counting.Spec

/-!
# Supports in the same orbit
-/

open Quiver Set Sum WithBot

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ} [i : LeLevel β] {σ : Spec β} {S : Support β}
    {lS : ∀ {γ : Λ}, (hγ : (γ : TypeIndex) < β) → (A : Path (β : TypeIndex) γ) → Support γ}

end ConNF
