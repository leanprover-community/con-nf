import Mathlib.SetTheory.Ordinal.Arithmetic

class LtWellOrder (α : Type _) extends LinearOrder α, IsWellOrder α (· < ·)

variable {α β : Type _}

instance [LinearOrder α] [IsWellOrder α (· < ·)] : LtWellOrder α := ⟨⟩

open Ordinal

theorem noMaxOrder_of_ordinal_type_eq [LtWellOrder α]
    (h : (type ((· < ·) : α → α → Prop)).IsLimit) : NoMaxOrder α := by
  constructor
  intro a
  have := (Ordinal.succ_lt_of_isLimit h).mpr (Ordinal.typein_lt_type (· < ·) a)
  obtain ⟨b, hb⟩ := Ordinal.typein_surj (· < ·) this
  use b
  have := Order.lt_succ (Ordinal.typein ((· < ·) : α → α → Prop) a)
  rw [← hb, Ordinal.typein_lt_typein] at this
  exact this
