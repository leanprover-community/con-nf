import ConNF.Coherent.CoherentData

/-!
# Coding functions

In this file, we define coding functions.

## Main declarations

* `ConNF.CodingFunction`: The type of coding functions.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}] [Level] [CoherentData] {β : TypeIndex} [LeLevel β]

def Support.orbitRel : Rel (Support β) (Support β) :=
  λ S T ↦ ∃ ρ : AllPerm β, ρᵁ • S = T

theorem Support.orbitRel_isEquivalence :
    Equivalence (orbitRel (β := β)) := by
  constructor
  · intro S
    use 1
    rw [allPermForget_one, one_smul]
  · rintro S T ⟨ρ, h⟩
    use ρ⁻¹
    rw [allPermForget_inv, ← h, inv_smul_smul]
  · rintro S T U ⟨ρ₁, h₁⟩ ⟨ρ₂, h₂⟩
    use ρ₂ * ρ₁
    rw [allPermForget_mul, mul_smul, h₁, h₂]

instance Support.setoid (β : TypeIndex) [LeLevel β] : Setoid (Support β) where
  r := orbitRel
  iseqv := orbitRel_isEquivalence

def SupportOrbit (β : TypeIndex) [LeLevel β] : Type u :=
  Quotient (Support.setoid β)

def Support.orbit (S : Support β) : SupportOrbit β :=
  Quotient.mk (Support.setoid β) S

theorem SupportOrbit.out_orbit (o : SupportOrbit β) : o.out.orbit = o := by
  rw [Support.orbit, Quotient.out_eq]

theorem SupportOrbit.exists_support (o : SupportOrbit β) : ∃ S : Support β, S.orbit = o := by
  induction o using Quot.inductionOn
  case h S => exact ⟨S, rfl⟩

theorem Support.orbit_eq_iff {S T : Support β} :
    S.orbit = T.orbit ↔ ∃ ρ : AllPerm β, ρᵁ • S = T :=
  ⟨Quotient.exact, Quotient.sound (a := S)⟩

@[simp]
theorem Support.smul_orbit {S : Support β} {ρ : AllPerm β} :
    (ρᵁ • S).orbit = S.orbit := by
  symm
  rw [orbit_eq_iff]
  use ρ

structure CodingFunction (β : TypeIndex) [LeLevel β] where
  rel : Rel (Support β) (TSet β)
  rel_coinjective : rel.Coinjective
  rel_dom_nonempty : rel.dom.Nonempty
  supports_of_rel {S : Support β} {x : TSet β} : rel S x → S.Supports x
  orbit_eq_of_mem_dom {S T : Support β} : S ∈ rel.dom → T ∈ rel.dom → S.orbit = T.orbit
  smul_rel {S : Support β} {x : TSet β} (h : rel S x) (ρ : AllPerm β) : rel (ρᵁ • S) (ρ • x)

namespace CodingFunction

theorem ext' {χ₁ χ₂ : CodingFunction β}
    (h : ∀ S x, χ₁.rel S x ↔ χ₂.rel S x) : χ₁ = χ₂ := by
  obtain ⟨r₁, _⟩ := χ₁
  obtain ⟨r₂, _⟩ := χ₂
  have : r₁ = r₂ := by
    ext S x
    exact h S x
  cases this
  rfl

theorem ext_aux {χ₁ χ₂ : CodingFunction β} {S : Support β} {x : TSet β}
    (h₁ : χ₁.rel S x) (h₂ : χ₂.rel S x) :
    χ₁.rel ≤ χ₂.rel := by
  intro T y h
  have := χ₁.orbit_eq_of_mem_dom ⟨x, h₁⟩ ⟨y, h⟩
  rw [Support.orbit_eq_iff] at this
  obtain ⟨ρ, rfl⟩ := this
  cases χ₁.rel_coinjective.coinjective h (χ₁.smul_rel h₁ ρ)
  exact χ₂.smul_rel h₂ ρ

theorem ext {χ₁ χ₂ : CodingFunction β} (S : Support β) (x : TSet β)
    (h₁ : χ₁.rel S x) (h₂ : χ₂.rel S x) :
    χ₁ = χ₂ := by
  apply ext'
  intro _ _
  constructor
  · apply ext_aux h₁ h₂
  · apply ext_aux h₂ h₁

theorem exists_allPerm_of_rel {χ : CodingFunction β} {S T : Support β} {x y : TSet β}
    (h₁ : χ.rel S x) (h₂ : χ.rel T y) :
    ∃ ρ : AllPerm β, ρᵁ • S = T ∧ ρ • x = y := by
  have := χ.orbit_eq_of_mem_dom ⟨x, h₁⟩ ⟨y, h₂⟩
  rw [Support.orbit_eq_iff] at this
  obtain ⟨ρ, hρ⟩ := this
  refine ⟨ρ, hρ, ?_⟩
  have := χ.smul_rel h₁ ρ
  exact χ.rel_coinjective.coinjective this (hρ ▸ h₂)

end CodingFunction

def Tangle.code (t : Tangle β) : CodingFunction β where
  rel S x := ∃ ρ : AllPerm β, ρᵁ • t.support = S ∧ ρ • t.set = x
  rel_coinjective := by
    constructor
    rintro x₁ x₂ S ⟨ρ₁, hρ₁, rfl⟩ ⟨ρ₂, rfl, rfl⟩
    exact t.support_supports.smul_eq_smul hρ₁
  rel_dom_nonempty := by
    refine ⟨t.support, t.set, 1, ?_⟩
    simp only [allPermForget_one, one_smul, and_self]
  supports_of_rel := by
    rintro _ _ ⟨ρ, rfl, rfl⟩
    exact t.support_supports.smul ρ
  orbit_eq_of_mem_dom := by
    rintro _ _ ⟨_, ρ₁, rfl, rfl⟩ ⟨_, ρ₂, rfl, rfl⟩
    simp only [Support.smul_orbit]
  smul_rel := by
    rintro _ _ ⟨ρ₁, rfl, rfl⟩ ρ₂
    use ρ₂ * ρ₁
    simp only [allPermForget_mul, mul_smul, and_self]

theorem Tangle.code_rel_self (t : Tangle β) :
    t.code.rel t.support t.set := by
  use 1
  simp only [allPermForget_one, one_smul, and_self]

theorem Tangle.code_eq_code_iff (t₁ t₂ : Tangle β) :
    t₁.code = t₂.code ↔ ∃ ρ : AllPerm β, ρ • t₁ = t₂ := by
  constructor
  · intro h
    have := t₂.code_rel_self
    rw [← h] at this
    obtain ⟨ρ, hρ₁, hρ₂⟩ := this
    use ρ
    exact Tangle.ext hρ₂ hρ₁
  · rintro ⟨ρ, rfl⟩
    symm
    apply CodingFunction.ext _ _ (ρ • t₁).code_rel_self
    use ρ
    exact ⟨rfl, rfl⟩

@[simp]
theorem Tangle.smul_code (t : Tangle β) (ρ : AllPerm β) :
    (ρ • t).code = t.code := by
  symm
  rw [code_eq_code_iff]
  use ρ

end ConNF
