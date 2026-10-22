module

public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

class LtWellOrder (α : Type _) extends LinearOrder α, IsWellOrder α (· < ·)

variable {α β : Type _}

instance [LinearOrder α] [IsWellOrder α (· < ·)] : LtWellOrder α := ⟨⟩

open Ordinal
