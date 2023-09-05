import ConNF.Foa
import ConNF.Counting.OrdSupportEquiv
import ConNF.Counting.Spec

/-!
# Specifying two strong supports at once
-/

open Quiver Set Sum WithBot

open scoped Classical

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}
  {σ : Spec β} {S T U : OrdSupport β} (hS : S.Strong) (hT : T.Strong)
  (hσS : Specifies σ S)

namespace Spec

-- structure Equiv (S T : OrdSupport β) (σ τ : Spec β) extends OrdSupport.Equiv S T where
--   specifies_left : Specifies σ S
--   specifies_right : Specifies τ T

end Spec

end ConNF
