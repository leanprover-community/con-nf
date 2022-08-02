import phase1.basic

open set with_bot

universe u

namespace con_nf
variables [params.{u}] (α : Λ) [core_tangle_cumul α] {β : Iio (α : type_index)}
  {s t : set (tangle β)}

/-- An `α` code is a type index `β < α` together with a set of tangles of type `β`. -/
@[ext] structure code : Type u :=
(extension : Iio (α : type_index))
(elts : set (tangle extension))

instance : inhabited (code α) := ⟨⟨⊥, ∅⟩⟩

/-- Nonempty codes. -/
abbreviation nonempty_code : Type u := {c : code α // c.elts.nonempty}

namespace code
variables {α}

/-- A code is empty if it has no element. -/
protected def is_empty (c : code α) : Prop := c.elts = ∅

@[simp] lemma is_empty_mk : (⟨β, s⟩ : code α).is_empty ↔ s = ∅ := iff.rfl

lemma mk_inj : (⟨β, s⟩ : code α) = ⟨β, t⟩ ↔ s = t := by simp

end code
end con_nf
