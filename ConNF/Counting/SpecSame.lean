import ConNF.FOA
import ConNF.Counting.StrongSupport

/-!
# Supports with the same specification
-/

open Quiver Set Sum WithBot

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ} [LeLevel β]
  {S T : Support β} {σ : Spec β} (hS : σ.Specifies S) (hT : σ.Specifies T)

end ConNF
