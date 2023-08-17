import ConNF.Phase1.Basic

#align_import phase1.code

open Set WithBot

universe u

namespace ConNF

variable [Params.{u}] (α : Λ) [CoreTangleCumul α] {β : iioIndex α} {s t : Set (Tangle β)}

/-- An `α` code is a type index `β < α` together with a set of tangles of type `β`. -/
def Code : Type u :=
  Σ β : iioIndex α, Set (Tangle β)
deriving Inhabited

/-- Nonempty codes. -/
abbrev NonemptyCode : Type u :=
  { c : Code α // c.2.Nonempty }

namespace Code

variable {α} {c : Code α}

/-- Constructor for `code`. -/
def mk : ∀ β : iioIndex α, Set (Tangle β) → Code α :=
  Sigma.mk

theorem mk_def : mk β s = ⟨β, s⟩ :=
  rfl

@[simp]
theorem fst_mk (β : iioIndex α) (s : Set (Tangle β)) : (mk β s).1 = β :=
  rfl

@[simp]
theorem snd_mk (β : iioIndex α) (s : Set (Tangle β)) : (mk β s).2 = s :=
  rfl

/-- A code is empty if it has no element. -/
protected def IsEmpty (c : Code α) : Prop :=
  c.2 = ∅

protected theorem IsEmpty.eq : c.isEmpty → c.2 = ∅ :=
  id

@[simp]
theorem isEmpty_mk : (mk β s).isEmpty ↔ s = ∅ :=
  Iff.rfl

@[simp]
theorem mk_inj : mk β s = mk β t ↔ s = t := by simp [mk]

end Code

end ConNF
