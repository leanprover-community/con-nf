import Mathlib.Tactic.Have
import Mathlib.ModelTheory.Satisfiability

/-!
# Typical ambiguity
-/

open FirstOrder Language Theory Structure

namespace ConNF

variable {L : Language} (ϕ : L →ᴸ L) (M : Type _) [L.Structure M] [Nonempty M]

/-- A weaker version of the assumption that `ϕ` is an expansion on `M`. -/
class IsEndomorphismOn (ϕ : L →ᴸ L) (M : Type _) [L.Structure M] : Prop where
  map_onSentence : ∀ (S : L.Sentence), M ⊨ ϕ.onSentence S ↔ M ⊨ S

export IsEndomorphismOn (map_onSentence)

variable [IsEndomorphismOn ϕ M]

attribute [simp] map_onSentence

@[simp]
theorem onTerm_relabel {α β : Type _} {L L' : Language}
    (ϕ : L →ᴸ L') (T : L.Term α) (g : α → β) :
    ϕ.onTerm (T.relabel g) = (ϕ.onTerm T).relabel g := by
  induction T
  case var x => rfl
  case func l f ts ih =>
    simp only [LHom.onTerm, Term.relabel, Term.func.injEq, heq_eq_eq, true_and]
    funext i
    exact ih i

@[simp]
theorem onBoundedFormula_relabel {α β : Type _} {L L' : Language} {n k : ℕ}
    (ϕ : L →ᴸ L') (F : L.BoundedFormula α n) (g : α → β ⊕ Fin k) :
    ϕ.onBoundedFormula (F.relabel g) = (ϕ.onBoundedFormula F).relabel g := by
  induction F
  case falsum i => rfl
  case equal i t₁ t₂ =>
    simp only [LHom.onBoundedFormula, onTerm_relabel]
    rfl
  case rel n l R ts =>
    simp only [LHom.onBoundedFormula, Function.comp, onTerm_relabel]
    rfl
  case imp i f₁ f₂ ih₁ ih₂ =>
    simp only [LHom.onBoundedFormula, BoundedFormula.relabel_imp, BoundedFormula.imp.injEq]
    exact ⟨ih₁, ih₂⟩
  case all i f ih =>
    simp only [LHom.onBoundedFormula, BoundedFormula.castLE_rfl, BoundedFormula.relabel_all,
      Nat.add_eq, Nat.add_zero, BoundedFormula.all.injEq]
    exact ih

@[simp]
theorem onFormula_relabel {α β : Type _} {L L' : Language}
    (ϕ : L →ᴸ L') (F : L.Formula α) (g : α → β) :
    ϕ.onFormula (F.relabel g) = (ϕ.onFormula F).relabel g :=
  onBoundedFormula_relabel ϕ F _

@[simp]
theorem onFormula_realize_of_isEmpty {α : Type _} [IsEmpty α] (F : L.Formula α) (v : α → M) :
    (ϕ.onFormula F).Realize v ↔ F.Realize v := by
  have : v = (default : Empty → M) ∘ (default : α → Empty)
  · ext x
    exact IsEmpty.elim inferInstance x
  rw [this, ← Formula.realize_relabel, ← Formula.realize_relabel]
  change M ⊨ (ϕ.onFormula F).relabel default ↔ M ⊨ F.relabel default
  rw [← map_onSentence (ϕ := ϕ) (F.relabel default), ← onFormula_relabel]
  rfl

theorem specker_aux₁ {m n : ℕ} (A : L.BoundedFormula Empty 1) (P : Fin m → L.Formula (Fin n))
    (k : Fin (n + 1)) :
    ∃ e : Fin (n + 1) → M,
    (∀ x : M, A.Realize Empty.elim (fun _ => x) → A.Realize Empty.elim (fun _ => e k)) ∧
    ∀ i, (P i).Realize (fun j => e j) ↔ (ϕ.onFormula (P i)).Realize (fun j => e j.succ) := by
  induction n with
  | zero =>
    refine ⟨fun _ => Classical.epsilon (fun x : M => A.Realize Empty.elim (fun _ => x)), ?_, ?_⟩
    · intro x hx
      exact Classical.epsilon_spec (p := fun x : M => A.Realize Empty.elim (fun _ => x)) ⟨x, hx⟩
    · simp only [onFormula_realize_of_isEmpty, implies_true]
  | succ n ih => sorry

end ConNF
