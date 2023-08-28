import ConNF.BaseType.Atom

/-!
# Pretangles

A pretangle is an object of the supertype structure that our model resides inside.
In this file, we define pretangles.

## Main declarations

* `ConNF.Pretangle`: The type of pretangles.
-/

universe u

namespace ConNF

variable [Params.{u}] {α : Λ}

/-- A *pretangle* is an object that may become a *tangle*, an element of the model.
The type of pretangles forms a model of TTT without extensionality. -/
def Pretangle : TypeIndex → Type u
  | ⊥ => Atom
  | (α : Λ) => ∀ β : TypeIndex, β < α → Set (Pretangle β)
termination_by Pretangle x => x

namespace Pretangle

/-- The "identity" equivalence between `Atom` and `Pretangle ⊥`. -/
def toBot : Atom ≃ Pretangle ⊥ :=
  Equiv.cast <| by unfold Pretangle; rfl

/-- The "identity" equivalence between `Pretangle ⊥` and `Atom`. -/
def ofBot : Pretangle ⊥ ≃ Atom :=
  Equiv.cast <| by unfold Pretangle; rfl

/-- The "identity" equivalence between `Π β < α, Set (Pretangle β)` and `Pretangle α`. -/
def toCoe : (∀ β : TypeIndex, β < α → Set (Pretangle β)) ≃ Pretangle α :=
  Equiv.cast <| by unfold Pretangle; rfl

/-- The "identity" equivalence between `Pretangle α` and `Π β < α, Set (Pretangle β)`. -/
def ofCoe : Pretangle α ≃ ∀ β : TypeIndex, β < α → Set (Pretangle β) :=
  Equiv.cast <| by unfold Pretangle; rfl

@[simp]
theorem toBot_symm : toBot.symm = ofBot :=
  rfl

@[simp]
theorem ofBot_symm : ofBot.symm = toBot :=
  rfl

@[simp]
theorem toCoe_symm : toCoe.symm = (ofCoe : Pretangle α ≃ _) :=
  rfl

@[simp]
theorem ofCoe_symm : ofCoe.symm = (toCoe : _ ≃ Pretangle α) :=
  rfl

@[simp]
theorem toBot_ofBot (a) : toBot (ofBot a) = a := by simp [toBot, ofBot]

@[simp]
theorem ofBot_toBot (a) : ofBot (toBot a) = a := by simp [toBot, ofBot]

@[simp]
theorem toCoe_ofCoe (a : Pretangle α) : toCoe (ofCoe a) = a := by simp [toCoe, ofCoe]

@[simp]
theorem ofCoe_toCoe (a) : ofCoe (toCoe a : Pretangle α) = a := by simp [toCoe, ofCoe]

@[simp]
theorem toBot_inj {a b} : toBot a = toBot b ↔ a = b :=
  toBot.injective.eq_iff

@[simp]
theorem ofBot_inj {a b} : ofBot a = ofBot b ↔ a = b :=
  ofBot.injective.eq_iff

@[simp]
theorem toCoe_inj {a b} : (toCoe a : Pretangle α) = toCoe b ↔ a = b :=
  toCoe.injective.eq_iff

@[simp]
theorem ofCoe_inj {a b : Pretangle α} : ofCoe a = ofCoe b ↔ a = b :=
  ofCoe.injective.eq_iff

end Pretangle

end ConNF
