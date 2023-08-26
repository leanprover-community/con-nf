import ConNF.Fuzz.Hypotheses

open Set WithBot

universe u

namespace ConNF

variable [Params.{u}] (α : Λ) [CoreTangleCumul α] {β : IioBot α} {s t : Set (Tangle β)}

/-- An `α` code is a type index `β < α` together with a set of tangles of type `β`. -/
def Code : Type u :=
  (β : IioBot α) × Set (Tangle β)

instance : Inhabited (Code α) :=
⟨⟨⊥, ∅⟩⟩

/-- Nonempty codes. -/
abbrev NonemptyCode : Type u :=
  { c : Code α // c.2.Nonempty }

namespace Code

@[ext]
theorem Code.ext {c₀ c₁ : Code α} (h₀ : c₀.1 = c₁.1) (h₁ : HEq c₀.2 c₁.2) : c₀ = c₁ :=
  Sigma.ext h₀ h₁

variable {α}
variable {c : Code α}

/-- Constructor for `code`. -/
def mk : ∀ β : IioBot α, Set (Tangle β) → Code α :=
  Sigma.mk

theorem mk_def : mk β s = ⟨β, s⟩ :=
  rfl

@[simp]
theorem fst_mk (β : IioBot α) (s : Set (Tangle β)) : (mk β s).1 = β :=
  rfl

@[simp]
theorem snd_mk (β : IioBot α) (s : Set (Tangle β)) : (mk β s).2 = s :=
  rfl

/-- A code is empty if it has no element. -/
protected def IsEmpty (c : Code α) : Prop :=
  c.2 = ∅

protected theorem IsEmpty.eq : c.IsEmpty → c.2 = ∅ :=
  id

@[simp]
theorem isEmpty_mk : (mk β s).IsEmpty ↔ s = ∅ :=
  Iff.rfl

@[simp]
theorem mk_inj : mk β s = mk β t ↔ s = t := by
  rw [Sigma.ext_iff]
  simp

end Code

end ConNF
