import ConNF.FOA
import ConNF.Counting.Spec

/-!
# Supports with the same specification
-/

open Quiver Set Sum WithBot

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ} [LeLevel β] (S T : Support β)

end ConNF
