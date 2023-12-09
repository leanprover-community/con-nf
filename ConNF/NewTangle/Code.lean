import ConNF.NewTangle.Hypotheses

/-!
# Codes

In this file, we define codes representing tangles of type `α`.

## Main declarations

* `ConNF.Code`: Codes representing `α`-tangles.
* `ConNF.NonemptyCode`: Nonempty `α`-codes.
-/

open Set WithBot

universe u

namespace ConNF

variable [Params.{u}] (α : Λ) [TangleDataLt α] {β : Λ} [IsLt β α] {s t : Set (Tangle β)}

/-- An `α` code is a type index `β < α` together with a set of tangles of type `β`. -/
@[ext]
structure Code : Type u where
  (β : TypeIndex)
  [inst : IsLt β α]
  (members : Set (Tangle β))

instance (c : Code α) : IsLt c.β α := c.inst

instance : Inhabited (Code α) :=
  let _ := isLtBot α
  ⟨⟨⊥, ∅⟩⟩

/-- Nonempty codes. -/
abbrev NonemptyCode : Type u :=
  { c : Code α // c.members.Nonempty }

namespace Code

variable {α}
variable {c : Code α}

/-- A code is empty if it has no element. -/
protected def IsEmpty (c : Code α) : Prop :=
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
