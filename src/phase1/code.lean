import phase1.basic

universe u

namespace con_nf
variables [params.{u}] (α : Λ) [phase_1 α] {β : type_index} {hβ : β < α}
  {s t : set (tangle α β hβ)}

/-- An `α` code is a type index `β < α` together with a set of tangles of type `β`. -/
@[ext] structure code : Type u :=
(extension : type_index)
(extension_lt : extension < α)
(elts : set (tangle α extension extension_lt))

lemma code.eq_of_elts_eq (γ : type_index) (hγ : γ < α) (A B : set (tangle α γ hγ)) :
  (⟨γ, hγ, A⟩ : code α) = ⟨γ, hγ, B⟩ ↔ A = B := by simp

/-- Nonempty codes. -/
abbreviation nonempty_code : Type u := {c : code α // c.elts.nonempty}

namespace code
variables {α}

/-- A code is empty if it has no element. -/
protected def is_empty (c : code α) : Prop := c.elts = ∅

@[simp] lemma is_empty_mk : (⟨β, hβ, s⟩ : code α).is_empty ↔ s = ∅ := iff.rfl

@[simp] lemma mk_inj (s t : set (tangle α β hβ)) : (⟨β, hβ, s⟩ : code α) = ⟨β, hβ, t⟩ ↔ s = t :=
by rw [ext_iff, and_iff_right rfl, heq_iff_eq]

end code
end con_nf
