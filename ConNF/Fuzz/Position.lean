import Mathlib.Order.RelClasses
import Mathlib.Logic.Embedding.Basic

namespace ConNF

class Position (α : Type _) (β : outParam <| Type _) where
  pos : α ↪ β

export Position (pos)

variable {α : Type _} {β : Type _} [Position α β]

theorem pos_injective :
    Function.Injective (pos : α → β) :=
  pos.inj'

instance [LT β] : LT α :=
  ⟨InvImage (· < ·) pos⟩

theorem pos_lt_pos [LT β] (c d : α) :
    pos c < pos d ↔ c < d :=
  Iff.rfl

theorem isWellOrder_invImage {r : β → β → Prop} (h : IsWellOrder β r)
    (f : α → β) (hf : Function.Injective f) :
    IsWellOrder α (InvImage r f) where
  trichotomous := by
    intro x y
    have := h.trichotomous (f x) (f y)
    rw [hf.eq_iff] at this
    exact this
  trans x y z := h.trans (f x) (f y) (f z)
  wf := InvImage.wf _ h.wf

instance [LT β] [IsWellOrder β (· < ·)] : IsWellOrder α (· < ·) :=
  isWellOrder_invImage inferInstance _ pos_injective

instance [LT β] [IsWellOrder β (· < ·)] : IsWellOrder α (InvImage (· < ·) pos) :=
  isWellOrder_invImage inferInstance _ pos_injective

instance [LT β] [IsWellOrder β (· < ·)] : WellFoundedRelation α :=
  IsWellOrder.toHasWellFounded

end ConNF
