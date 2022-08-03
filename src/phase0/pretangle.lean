import phase0.params

/-!
# Pretangles
-/

noncomputable theory

universe u

namespace con_nf
variables [params.{u}] {α : Λ}

/-- A *pretangle* is an object that may become a *tangle*, an element of the model.
The type of pretangles forms a model of TTT without extensionality. -/
def pretangle : type_index → Type u
| ⊥ := atom
| (α : Λ) := Π β : type_index, β < α → set (pretangle β)
using_well_founded { dec_tac := `[assumption] }

namespace pretangle

/-- The "identity" equivalence between `atom` and `pretangle ⊥`. -/
def to_bot : atom ≃ pretangle ⊥ := equiv.cast $ by unfold pretangle

/-- The "identity" equivalence between `pretangle ⊥` and `atom`. -/
def of_bot : pretangle ⊥ ≃ atom := equiv.cast $ by unfold pretangle

/-- The "identity" equivalence between `Π β < α, set (pretangle β)` and `pretangle α`. -/
def to_coe : (Π β : type_index, β < α → set (pretangle β)) ≃ pretangle α :=
equiv.cast $ by unfold pretangle

/-- The "identity" equivalence between `pretangle α` and `Π β < α, set (pretangle β)`. -/
def of_coe : pretangle α ≃ Π β : type_index, β < α → set (pretangle β) :=
equiv.cast $ by unfold pretangle

@[simp] lemma to_bot_symm : to_bot.symm = of_bot := rfl
@[simp] lemma of_bot_symm : of_bot.symm = to_bot := rfl
@[simp] lemma to_coe_symm : to_coe.symm = (of_coe : pretangle α ≃ _) := rfl
@[simp] lemma of_coe_symm : of_coe.symm = (to_coe : _ ≃ pretangle α) := rfl
@[simp] lemma to_bot_of_bot (a) : to_bot (of_bot a) = a := by simp [to_bot, of_bot]
@[simp] lemma of_bot_to_bot (a) : of_bot (to_bot a) = a := by simp [to_bot, of_bot]
@[simp] lemma to_coe_of_coe (a : pretangle α) : to_coe (of_coe a) = a := by simp [to_coe, of_coe]
@[simp] lemma of_coe_to_coe (a) : of_coe (to_coe a : pretangle α) = a := by simp [to_coe, of_coe]
@[simp] lemma to_bot_inj {a b} : to_bot a = to_bot b ↔ a = b := to_bot.injective.eq_iff
@[simp] lemma of_bot_inj {a b} : of_bot a = of_bot b ↔ a = b := of_bot.injective.eq_iff
@[simp] lemma to_coe_inj {a b} : (to_coe a : pretangle α) = to_coe b ↔ a = b :=
to_coe.injective.eq_iff
@[simp] lemma of_coe_inj {a b : pretangle α} : of_coe a = of_coe b ↔ a = b :=
of_coe.injective.eq_iff

-- Yaël: Note, this instance is useless as it won't fire because `β < α` is not a class
/-- The membership relation defined on pretangles.
This is exactly the membership relation on tangles, without the extensionality condition that
allows this membership relation to be used in a model of TTT. -/
instance has_mem {β : type_index} (hβ : β < α) : has_mem (pretangle β) (pretangle α) :=
⟨λ b a, b ∈ of_coe a β hβ⟩

end pretangle
end con_nf
