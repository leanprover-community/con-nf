import ConNF.Counting.Twist
import ConNF.Counting.CodingFunction

/-!
# Recoding

In this file, we show that all coding functions of level `β > γ` can be expressed in terms of a set
of `γ`-coding functions.

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}] [Level] [CoherentData] {β γ : Λ} [LeLevel β] [LeLevel γ]
    (hγ : (γ : TypeIndex) < β)

def Combination (x : TSet β) (S : Support β) (χs : Set (CodingFunction β)) : Prop :=
  ∀ y : TSet γ, y ∈[hγ] x ↔ ∃ χ ∈ χs, ∃ T z, χ.rel T z ∧ S ≤ T ∧ y ∈[hγ] z

theorem combination_unique {x₁ x₂ : TSet β} {S : Support β} {χs : Set (CodingFunction β)}
    (hx₁ : Combination hγ x₁ S χs) (hx₂ : Combination hγ x₂ S χs) :
    x₁ = x₂ := by
  apply tSet_ext hγ
  intro y
  rw [hx₁, hx₂]

theorem Combination.smul {x : TSet β} {S : Support β} {χs : Set (CodingFunction β)}
    (h : Combination hγ x S χs) (ρ : AllPerm β) :
    Combination hγ (ρ • x) (ρᵁ • S) χs := by
  intro y
  rw [TSet.mem_smul_iff, h]
  constructor
  · rintro ⟨χ, hχ, T, z, hTz, hST, hyz⟩
    refine ⟨χ, hχ, ρᵁ • T, ρ • z, χ.smul_rel hTz ρ, Support.smul_le_smul hST ρᵁ, ?_⟩
    rwa [TSet.mem_smul_iff]
  · rintro ⟨χ, hχ, T, z, hTz, hST, hyz⟩
    refine ⟨χ, hχ, ρ⁻¹ᵁ • T, ρ⁻¹ • z, χ.smul_rel hTz ρ⁻¹, ?_, ?_⟩
    · have := Support.smul_le_smul hST ρ⁻¹ᵁ
      simp only [allPermForget_inv, inv_smul_smul] at this ⊢
      exact this
    · rwa [TSet.mem_smul_iff, inv_inv, allPerm_inv_sderiv, smul_inv_smul]

inductive RaisedRel (s : Set (CodingFunction β)) (o : SupportOrbit β) : Rel (Support β) (TSet β)
  | mk : (S : Support β) → S.orbit = o → (x : TSet β) → Combination hγ x S s → RaisedRel s o S x

theorem raisedRel_coinjective (s : Set (CodingFunction β)) (o : SupportOrbit β) :
    (RaisedRel hγ s o).Coinjective := by
  constructor
  rintro x₁ x₂ S ⟨_, rfl, _, hx₁⟩ ⟨_, _, _, hx₂⟩
  exact combination_unique hγ hx₁ hx₂

theorem raisedRel_dom_nonempty {s : Set (CodingFunction β)} {o : SupportOrbit β}
    (hso : ∀ S, S.orbit = o → ∃ x, Combination hγ x S s ∧ S.Supports x) :
    (RaisedRel hγ s o).dom.Nonempty := by
  obtain ⟨S, hS⟩ := o.exists_support
  obtain ⟨x, hx, _⟩ := hso S hS
  exact ⟨S, x, .mk S hS x hx⟩

theorem supports_of_raisedRel {s : Set (CodingFunction β)} {o : SupportOrbit β}
    (hso : ∀ S, S.orbit = o → ∃ x, Combination hγ x S s ∧ S.Supports x)
    {S : Support β} {x : TSet β} :
    RaisedRel hγ s o S x → S.Supports x := by
  rintro ⟨S, hS, x, hx⟩
  obtain ⟨y, hy₁, hy₂⟩ := hso S hS
  cases combination_unique hγ hx hy₁
  exact hy₂

theorem orbit_eq_of_mem_dom_raisedRel (s : Set (CodingFunction β)) (o : SupportOrbit β)
    {S : Support β} (hS : S ∈ (RaisedRel hγ s o).dom) :
    S.orbit = o := by
  obtain ⟨x, _, hS⟩ := hS
  exact hS

theorem smul_raisedRel (s : Set (CodingFunction β)) (o : SupportOrbit β)
    {S : Support β} {x : TSet β} (h : RaisedRel hγ s o S x) (ρ : AllPerm β) :
    RaisedRel hγ s o (ρᵁ • S) (ρ • x) := by
  obtain ⟨_, hS, _, hx⟩ := h
  refine ⟨ρᵁ • S, ?_, ρ • x, ?_⟩
  · rwa [Support.smul_orbit]
  · exact hx.smul hγ ρ

def raised (s : Set (CodingFunction β)) (o : SupportOrbit β)
    (hso : ∀ S, S.orbit = o → ∃ x, Combination hγ x S s ∧ S.Supports x) : CodingFunction β where
  rel := RaisedRel hγ s o
  rel_coinjective := raisedRel_coinjective hγ s o
  rel_dom_nonempty := raisedRel_dom_nonempty hγ hso
  supports_of_rel := supports_of_raisedRel hγ hso
  orbit_eq_of_mem_dom hS hT := (orbit_eq_of_mem_dom_raisedRel hγ s o hS).trans
    (orbit_eq_of_mem_dom_raisedRel hγ s o hT).symm
  smul_rel := smul_raisedRel hγ s o

theorem scoderiv_supports_singleton (S : Support γ) (y : TSet γ) (h : S.Supports y) :
    (S ↗ hγ).Supports (singleton hγ y) := by
  constructor
  case nearLitters_eq_empty_of_bot => rintro ⟨⟩
  intro ρ hρ
  apply tSet_ext hγ
  intro z
  have := h.supports (ρ ↘ hγ) ?_
  · rw [TSet.mem_smul_iff, typedMem_singleton_iff, typedMem_singleton_iff]
    conv_rhs => rw [← this]
    constructor
    · rintro rfl
      rw [allPerm_inv_sderiv, smul_inv_smul]
    · rintro rfl
      rw [allPerm_inv_sderiv, inv_smul_smul]
  · rw [Support.smul_eq_iff] at hρ ⊢
    intro A
    constructor
    · rintro a ⟨i, ha⟩
      have := (hρ (A ↗ hγ)).1 a ?_
      · rwa [allPermSderiv_forget, Tree.sderiv_apply]
      · exact ⟨i, ⟨A, a⟩, ha, rfl⟩
    · rintro N ⟨i, hN⟩
      have := (hρ (A ↗ hγ)).2 N ?_
      · rwa [allPermSderiv_forget, Tree.sderiv_apply]
      · exact ⟨i, ⟨A, N⟩, hN, rfl⟩

theorem raisedSingleton_supports (S : Support β) (y : TSet γ) :
    (S + designatedSupport y ↗ hγ).Supports (singleton hγ y) := by
  have := scoderiv_supports_singleton hγ (designatedSupport y) y (designatedSupport_supports y)
  apply this.mono le_add_left
  rintro ⟨⟩

def raisedSingleton (S : Support β) (y : TSet γ) : CodingFunction β :=
  (Tangle.mk (singleton hγ y) (S + designatedSupport y ↗ hγ) (raisedSingleton_supports hγ S y)).code

end ConNF
