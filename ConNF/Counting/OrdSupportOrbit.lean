import Mathlib.GroupTheory.GroupAction.Basic
import ConNF.Counting.SpecSame

/-!
# Orbits of ordered supports
-/

open Set Sum

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}

namespace OrdSupportClass

def Nice (S : OrdSupportClass β) : Prop :=
  ∃ S' : OrdSupportClass β, S'.Strong ∧ ∃ ρ : Allowable β, S = ρ • S'

theorem exists_strong_of_nice {S : OrdSupportClass β} (h : S.Nice) :
    ∃ S' : OrdSupportClass β, S'.Strong ∧ ∃ ρ : Allowable β, S = ρ • S' :=
  h

end OrdSupportClass

end ConNF
