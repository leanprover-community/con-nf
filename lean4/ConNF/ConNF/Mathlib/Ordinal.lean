import Mathlib.SetTheory.Ordinal.Arithmetic

open Set

universe u

variable {ι α : Type u} {s : Set α}

namespace Ordinal

protected theorem IsLimit.isSuccLimit {o : Ordinal} (h : o.IsLimit) : Order.IsSuccLimit o := by
  rw [Order.isSuccLimit_iff_succ_lt]; exact h.2

end Ordinal
