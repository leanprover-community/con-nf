import ConNF.Construction.Hypotheses

/-!
# Codes

In this file, we define codes representing t-sets of type `α`.

## Main declarations

* `ConNF.Code`: Codes representing t-sets at type `α`.
* `ConNF.NonemptyCode`: Nonempty `α`-codes.
-/

open Set WithBot

universe u

namespace ConNF

variable [Params.{u}] [Level] [ModelDataLt] {β : Λ} [LtLevel β] {s t : Set (TSet β)}

/-- An `α` code is a type index `β < α` together with a set of tangles of type `β`.
There is at most one t-set with this code. Any t-set has exactly one code for each proper type index
`β < α`, and possibly a code for `β = ⊥`. -/
@[ext]
structure Code : Type u where
  (β : TypeIndex)
  [inst : LtLevel β]
  (members : Set (TSet β))

instance (c : Code) : LtLevel c.β := c.inst

instance : Inhabited Code :=
  ⟨⟨⊥, ∅⟩⟩

/-- Nonempty codes. -/
abbrev NonemptyCode : Type u :=
  { c : Code // c.members.Nonempty }

namespace Code

variable {α}
variable {c : Code}

/-- A code is empty if it has no element. -/
protected def IsEmpty (c : Code) : Prop :=
  c.members = ∅

protected theorem IsEmpty.eq : c.IsEmpty → c.members = ∅ :=
  id

@[simp]
theorem isEmpty_mk : (mk β s).IsEmpty ↔ s = ∅ :=
  Iff.rfl

@[simp]
theorem mk_inj : mk β s = mk β t ↔ s = t :=
  by simp only [mk.injEq, heq_eq_eq, true_and]

end Code

end ConNF
