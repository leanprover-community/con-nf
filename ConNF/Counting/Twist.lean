import ConNF.Setup.ModelData

/-!
# Twisting sets

In this file, we define the notion of a designated support for a t-set.

## Main declarations

* `ConNF.TSet.designatedSupport`: The designated support for a t-set.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}] {α : TypeIndex} [ModelData α]

def TSet.orbitRel : Rel (TSet α) (TSet α) :=
  λ x y ↦ ∃ ρ : AllPerm α, ρ • x = y

theorem TSet.orbitRel_isEquivalence :
    Equivalence (orbitRel (α := α)) := by
  constructor
  · intro S
    use 1
    rw [one_smul]
  · rintro S T ⟨ρ, h⟩
    use ρ⁻¹
    rw [← h, inv_smul_smul]
  · rintro S T U ⟨ρ₁, h₁⟩ ⟨ρ₂, h₂⟩
    use ρ₂ * ρ₁
    rw [mul_smul, h₁, h₂]

instance TSet.setoid (α : TypeIndex) [ModelData α] : Setoid (TSet α) where
  r := orbitRel
  iseqv := orbitRel_isEquivalence

def TSetOrbit (α : TypeIndex) [ModelData α] : Type u :=
  Quotient (TSet.setoid α)

def TSet.orbit (x : TSet α) : TSetOrbit α :=
  Quotient.mk (TSet.setoid α) x

theorem TSetOrbit.exists_tSet (o : TSetOrbit α) : ∃ x : TSet α, TSet.orbit x = o := by
  induction o using Quot.inductionOn
  case h S => exact ⟨S, rfl⟩

theorem TSet.orbit_eq_iff {x y : TSet α} :
    orbit x = orbit y ↔ ∃ ρ : AllPerm α, ρ • x = y :=
  ⟨Quotient.exact, Quotient.sound (a := x)⟩

@[simp]
theorem TSet.smul_orbit {x : TSet α} {ρ : AllPerm α} :
    orbit (ρ • x) = orbit x := by
  symm
  rw [orbit_eq_iff]
  use ρ

def TSetOrbit.repr (o : TSetOrbit α) : TSet α :=
  o.exists_tSet.choose

@[simp]
theorem TSetOrbit.repr_orbit (o : TSetOrbit α) : TSet.orbit o.repr = o :=
  o.exists_tSet.choose_spec

def TSetOrbit.repr_support (o : TSetOrbit α) : Support α :=
  (exists_support o.repr).choose

theorem TSetOrbit.repr_support_spec (o : TSetOrbit α) : o.repr_support.Supports o.repr :=
  (exists_support o.repr).choose_spec

theorem TSet.exists_twist (x : TSet α) : ∃ ρ : AllPerm α, ρ • (orbit x).repr = x := by
  rw [← orbit_eq_iff, TSetOrbit.repr_orbit]

def twist (x : TSet α) : AllPerm α :=
  (TSet.exists_twist x).choose

theorem twist_spec (x : TSet α) : twist x • (TSet.orbit x).repr = x :=
  (TSet.exists_twist x).choose_spec

def designatedSupport (x : TSet α) : Support α :=
  (twist x)ᵁ • (TSet.orbit x).repr_support

theorem designatedSupport_supports (x : TSet α) : (designatedSupport x).Supports x := by
  have := (TSet.orbit x).repr_support_spec.smul (twist x)
  rwa [twist_spec] at this

end ConNF
