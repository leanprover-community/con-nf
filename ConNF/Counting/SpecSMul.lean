import ConNF.Counting.Spec

/-!
# Supports in the same orbit
-/

open Quiver Set Sum WithBot

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ} [i : LeLevel β] {σ : Spec β} {S : Support β}

end ConNF
