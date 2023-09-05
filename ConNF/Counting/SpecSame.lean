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
  {σ : Spec β} {S T U : OrdSupport β}
  (hS : S.Strong) (hU: U.Strong)
  (hσS : Specifies σ S) (hσT : Specifies σ T)
  {r : Tree Reorder β} (hr : OrdSupport.IsEquiv r T U)

namespace Spec



end Spec

end ConNF
