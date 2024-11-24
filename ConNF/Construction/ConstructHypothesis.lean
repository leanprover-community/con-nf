import ConNF.Construction.ConstructMotive

/-!
# New file

In this file...

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal WithBot

namespace ConNF

variable [Params.{u}] {α : Λ} (M : (β : Λ) → (β : TypeIndex) < α → Motive β)
  (H : (β : Λ) → (h : (β : TypeIndex) < α) → Hypothesis (M β h) λ γ h' ↦ M γ (h'.trans h))

def constructHypothesis (α : Λ) (M : (β : Λ) → (β : TypeIndex) < α → Motive β)
    (H : (β : Λ) → (h : (β : TypeIndex) < α) → Hypothesis (M β h) λ γ h' ↦ M γ (h'.trans h)) :
    Hypothesis (constructMotive α M H) M :=
  {
    allPermSderiv := sorry
    allPermBotSderiv := sorry
    singleton := sorry
    allPermSderiv_forget := sorry
    allPermBotSderiv_forget := sorry
    pos_atom_lt_pos := sorry
    pos_nearLitter_lt_pos := sorry
    smul_fuzz := sorry
    smul_fuzz_bot := sorry
    allPerm_of_smul_fuzz := sorry
    tSet_ext := sorry
    typedMem_singleton_iff := sorry
  }

end ConNF
