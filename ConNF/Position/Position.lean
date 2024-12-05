import ConNF.Base.Params

/-!
# Position functions

In this file, we define what it means for a type to have a position function.

## Main declarations

* `ConNF.Position`: The typeclass that stores a position function for a type.
-/

universe u

open Cardinal

namespace ConNF

variable [Params.{u}]

class Position (X : Type _) where
  pos : X ↪ μ

export Position (pos)

theorem card_le_of_position {X : Type _} [Position X] :
    #X ≤ #μ :=
  mk_le_of_injective pos.injective

@[elab_as_elim]
def pos_induction {X : Type _} [Position X] {C : X → Sort _} (x : X)
    (h : ∀ x, (∀ y, pos y < pos x → C y) → C x) : C x :=
  WellFounded.induction (InvImage.wf pos (inferInstanceAs <| IsWellFounded μ (· < ·)).wf) x h

end ConNF
