import ConNF.Phase0.Params

#align_import phase0.pretangle

/-!
# Pretangles
-/


noncomputable section

universe u

namespace ConNf

variable [Params.{u}] {α : Λ}

/-- A *pretangle* is an object that may become a *tangle*, an element of the model.
The type of pretangles forms a model of TTT without extensionality. -/
def Pretangle : TypeIndex → Type u
  | ⊥ => Atom
  | (α : Λ) => ∀ β : TypeIndex, β < α → Set (pretangle β)

namespace Pretangle

/-- The "identity" equivalence between `atom` and `pretangle ⊥`. -/
def toBot : Atom ≃ Pretangle ⊥ :=
  Equiv.cast <| by unfold pretangle

/-- The "identity" equivalence between `pretangle ⊥` and `atom`. -/
def ofBot : Pretangle ⊥ ≃ Atom :=
  Equiv.cast <| by unfold pretangle

/-- The "identity" equivalence between `Π β < α, set (pretangle β)` and `pretangle α`. -/
def toCoe : (∀ β : TypeIndex, β < α → Set (Pretangle β)) ≃ Pretangle α :=
  Equiv.cast <| by unfold pretangle

/-- The "identity" equivalence between `pretangle α` and `Π β < α, set (pretangle β)`. -/
def ofCoe : Pretangle α ≃ ∀ β : TypeIndex, β < α → Set (Pretangle β) :=
  Equiv.cast <| by unfold pretangle

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
theorem toBot_ofBot (a) : toBot (ofBot a) = a := by simp [to_bot, of_bot]

@[simp]
theorem ofBot_toBot (a) : ofBot (toBot a) = a := by simp [to_bot, of_bot]

@[simp]
theorem toCoe_ofCoe (a : Pretangle α) : toCoe (ofCoe a) = a := by simp [to_coe, of_coe]

@[simp]
theorem ofCoe_toCoe (a) : ofCoe (toCoe a : Pretangle α) = a := by simp [to_coe, of_coe]

@[simp]
theorem toBot_inj {a b} : toBot a = toBot b ↔ a = b :=
  toBot.Injective.eq_iff

@[simp]
theorem ofBot_inj {a b} : ofBot a = ofBot b ↔ a = b :=
  ofBot.Injective.eq_iff

@[simp]
theorem toCoe_inj {a b} : (toCoe a : Pretangle α) = toCoe b ↔ a = b :=
  toCoe.Injective.eq_iff

@[simp]
theorem ofCoe_inj {a b : Pretangle α} : ofCoe a = ofCoe b ↔ a = b :=
  ofCoe.Injective.eq_iff

-- Yaël: Note, this instance is useless as it won't fire because `β < α` is not a class
/-- The membership relation defined on pretangles.
This is exactly the membership relation on tangles, without the extensionality condition that
allows this membership relation to be used in a model of TTT. -/
instance hasMem {β : TypeIndex} (hβ : β < α) : Membership (Pretangle β) (Pretangle α) :=
  ⟨fun b a => b ∈ ofCoe a β hβ⟩

end Pretangle

end ConNf
