import phase1.basic

open set

universe u

namespace con_nf
variables [params.{u}] (α : Λ) [weak_tangle_cumul α] {β : Iio (α : type_index)}
  {s t : set (tangle β)}

/-- An `α` code is a type index `β < α` together with a set of tangles of type `β`. -/
@[ext] structure code : Type u :=
(extension : type_index)
(extension_lt : extension < α)
(elts : set (tangle ⟨extension, extension_lt⟩))

lemma code.eq_of_elts_eq (γ : type_index) (hγ : γ < α) (A B : set (tangle α γ hγ)) :
  (⟨γ, hγ, A⟩ : code α) = ⟨γ, hγ, B⟩ ↔ A = B := by simp

/-- Nonempty codes. -/
abbreviation nonempty_code : Type u := {c : code α // c.elts.nonempty}

namespace code
variables {α}

/-- A code is empty if it has no element. -/
protected def is_empty (c : code α) : Prop := c.elts = ∅

@[simp] lemma is_empty_mk : (⟨β, s⟩ : code α).is_empty ↔ s = ∅ := iff.rfl

@[simp] lemma mk_inj : (⟨β, s⟩ : code α) = ⟨β, t⟩ ↔ s = t :=
by rw [ext_iff, and_iff_right rfl, heq_iff_eq]

end code
end con_nf
