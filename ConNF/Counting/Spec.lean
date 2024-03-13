import ConNF.Mathlib.Support
import ConNF.FOA.Basic.Flexible
import ConNF.Counting.CodingFunction

/-!
# Specifications
-/

open Quiver Set Sum WithBot

open scoped Classical Cardinal symmDiff

universe u

namespace ConNF

variable [Params.{u}] [Level] [FOAAssumptions] {β : Λ}

inductive SpecCondition (β : Λ)
  | atom (A : ExtendedIndex β) (i : κ)
  | flexible (A : ExtendedIndex β)
  | inflexibleCoe (A : ExtendedIndex β) (h : InflexibleCoePath A)
      (χ : CodingFunction h.δ) (hχ : χ.Strong)
  | inflexibleBot (A : ExtendedIndex β) (h : InflexibleBotPath A) (i : κ)

end ConNF
