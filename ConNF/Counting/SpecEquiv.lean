import ConNF.Counting.Spec
import ConNF.Counting.CodingFunctionEquiv

/-!
# Equivalences of specifications
-/

open MulAction Set Sum

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}

namespace Time

def reorder (i : Time β) (r : Tree Reorder β) : Time β :=
  (r i.2 i.1, i.2)

def reorder_symm (i : Time β) (r : Tree Reorder β) : Time β :=
  ((r i.2).symm i.1, i.2)

end Time

namespace Spec

structure ReorderSupports (σ : Spec β) (r : Tree Reorder β) : Prop where
  inflexibleCoe
    (A : ExtendedIndex β) (h : InflexibleCoePath A) (χ : CodingFunction (h.δ : Iic α))
    (i : Time β) (hi : (σ.cond i).Dom) :
    (σ.cond i).get hi = SpecCondition.inflexibleCoe A h χ →
    χ.ReorderSupports (r.comp (h.B.cons (coe_lt h.hδ)))

end Spec

namespace SpecCondition

noncomputable def reorder (c : SpecCondition β) (r : Tree Reorder β)
    {σ : Spec β} {i : Time β} (hi : (σ.cond i).Dom) (hc : c = (σ.cond i).get hi)
    (h : σ.ReorderSupports r) : SpecCondition β :=
  match c with
  | .atom A i => .atom A (i.reorder r)
  | .flexible A => .flexible A
  | .inflexibleCoe A P χ => .inflexibleCoe A P (χ.reorder (r.comp (P.B.cons (coe_lt P.hδ)))
      (h.inflexibleCoe A P χ i hi hc.symm))
  | .inflexibleBot A P i => .inflexibleBot A P (i.reorder r)

end SpecCondition

namespace Spec

noncomputable def reorder (σ : Spec β) (r : Tree Reorder β) (h : σ.ReorderSupports r) : Spec β where
  cond i := ⟨(σ.cond (i.reorder_symm r)).Dom,
    fun hi => ((σ.cond (i.reorder_symm r)).get hi).reorder r hi rfl h⟩
  dom_small := sorry

structure IsEquiv (r : Tree Reorder β) (σ₁ σ₂ : Spec β) : Prop where
  reorderSupports_left : σ₁.ReorderSupports r
  reorderSupports_right : σ₂.ReorderSupports (reorderSymm r)
  dom_right (i : Time β) (hi : (σ₁.cond i).Dom) : (σ₂.cond (i.reorder r)).Dom
  dom_left (i : Time β) (hi : (σ₂.cond i).Dom) : (σ₁.cond (i.reorder_symm r)).Dom
  reorder_right (i : Time β) (hi : (σ₁.cond i).Dom) :
    (σ₂.cond (i.reorder r)).get (dom_right i hi) =
    ((σ₁.cond i).get hi).reorder r hi rfl reorderSupports_left
  reorder_left (i : Time β) (hi : (σ₂.cond i).Dom) :
    (σ₁.cond (i.reorder_symm r)).get (dom_left i hi) =
    ((σ₂.cond i).get hi).reorder _ hi rfl reorderSupports_right

end Spec

end ConNF
