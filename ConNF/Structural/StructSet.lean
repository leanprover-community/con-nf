import ConNF.BaseType.Atom

/-!
# Structural sets

A structural set is an object of the supertype structure that our model resides inside.
In this file, we define structural sets.

## Main declarations

* `ConNF.StructSet`: The type of structural sets.
-/

universe u

namespace ConNF

variable [Params.{u}] {α : Λ}

/-- A *structural set* is an object that may become a *t-set*, an element of the model.
The type of structural sets forms a model of TTT without extensionality. -/
def StructSet : TypeIndex → Type u
  | ⊥ => Atom
  | (α : Λ) => ∀ β : TypeIndex, β < α → Set (StructSet β)
termination_by x => x

namespace StructSet

/-- The "identity" equivalence between `Atom` and `StructSet ⊥`. -/
def toBot : Atom ≃ StructSet ⊥ :=
  Equiv.cast <| by unfold StructSet; rfl

/-- The "identity" equivalence between `StructSet ⊥` and `Atom`. -/
def ofBot : StructSet ⊥ ≃ Atom :=
  Equiv.cast <| by unfold StructSet; rfl

/-- The "identity" equivalence between `∀ β < α, Set (StructSet β)` and `StructSet α`. -/
def toCoe : (∀ β : TypeIndex, β < α → Set (StructSet β)) ≃ StructSet α :=
  Equiv.cast <| by unfold StructSet; rfl

/-- The "identity" equivalence between `StructSet α` and `∀ β < α, Set (StructSet β)`. -/
def ofCoe : StructSet α ≃ ∀ β : TypeIndex, β < α → Set (StructSet β) :=
  Equiv.cast <| by unfold StructSet; rfl

@[simp]
theorem toBot_symm : toBot.symm = ofBot :=
  rfl

@[simp]
theorem ofBot_symm : ofBot.symm = toBot :=
  rfl

@[simp]
theorem toCoe_symm : toCoe.symm = (ofCoe : StructSet α ≃ _) :=
  rfl

@[simp]
theorem ofCoe_symm : ofCoe.symm = (toCoe : _ ≃ StructSet α) :=
  rfl

@[simp]
theorem toBot_ofBot (a) : toBot (ofBot a) = a := by
  unfold toBot ofBot
  simp only [Equiv.cast_apply, cast_cast, cast_eq]

@[simp]
theorem ofBot_toBot (a) : ofBot (toBot a) = a := by
  unfold toBot ofBot
  simp only [Equiv.cast_apply, cast_cast, cast_eq]

@[simp]
theorem toCoe_ofCoe (a : StructSet α) : toCoe (ofCoe a) = a := by simp [toCoe, ofCoe]

@[simp]
theorem ofCoe_toCoe (a) : ofCoe (toCoe a : StructSet α) = a := by simp [toCoe, ofCoe]

@[simp]
theorem toBot_inj {a b} : toBot a = toBot b ↔ a = b :=
  toBot.injective.eq_iff

@[simp]
theorem ofBot_inj {a b} : ofBot a = ofBot b ↔ a = b :=
  ofBot.injective.eq_iff

@[simp]
theorem toCoe_inj {a b} : (toCoe a : StructSet α) = toCoe b ↔ a = b :=
  toCoe.injective.eq_iff

@[simp]
theorem ofCoe_inj {a b : StructSet α} : ofCoe a = ofCoe b ↔ a = b :=
  ofCoe.injective.eq_iff

theorem toBot_eq_iff {a b} : toBot a = b ↔ a = ofBot b := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact (ofBot_toBot a).symm
  · rintro rfl
    exact toBot_ofBot b

theorem ofBot_eq_iff {a b} : ofBot a = b ↔ a = toBot b := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact (toBot_ofBot a).symm
  · rintro rfl
    exact ofBot_toBot b

/-- Extensionality for structural sets at proper type indices. If two structural sets have the same
extensions at every lower type index, then they are the same. -/
theorem coe_ext {α : Λ} {a b : StructSet α} :
    a = b ↔ ∀ β hβ t, t ∈ ofCoe a β hβ ↔ t ∈ ofCoe b β hβ := by
  constructor
  · rintro rfl
    simp only [implies_true, forall_const]
  intro h
  rw [← ofCoe_inj]
  ext β hβ t
  exact h β hβ t

end StructSet

end ConNF
