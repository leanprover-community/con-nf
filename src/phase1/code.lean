import phase1.basic

open equiv equiv.perm with_bot

noncomputable theory

universe u

namespace con_nf
variables [params.{u}] (α : Λ) [phase_1a α] {β : type_index} {hβ : β < α}
  {s t : set (tangle α β hβ)}

/-- An `α` code is a type index `β < α` together with a set of tangles of type `β`. -/
@[ext] structure code : Type u :=
(extension : type_index)
(extension_lt : extension < α)
(elts : set (tangle α extension extension_lt))

/-- Nonempty codes. -/
abbreviation nonempty_code : Type u := {c : code α // c.elts.nonempty}

variables {α}

/-- A code is empty if it has no element.-/
protected def code.is_empty (c : code α) : Prop := c.elts = ∅

@[simp] lemma code.is_empty_mk : (⟨β, hβ, s⟩ : code α).is_empty ↔ s = ∅ := iff.rfl

@[simp] lemma code.mk_inj (s t : set (tangle α β hβ)) : (⟨β, hβ, s⟩ : code α) = ⟨β, hβ, t⟩ ↔ s = t :=
by rw [code.ext_iff, and_iff_right rfl, heq_iff_eq]

variables (α)

/-- Suppose that the set of tangles embeds into the set of codes. -/
class phase_1a_embedding :=
(tangle_embedding : Π (β < α), tangle _ β (coe_lt_coe.2 ‹_›) ↪ code α)

open phase_1a_embedding
variable [phase_1a_embedding.{u} α]

def code.is_tangle {β < α} (c : code α) : Prop :=
∃ t : tangle α β (coe_lt_coe.2 ‹_›), c = tangle_embedding β ‹_› t

end con_nf
