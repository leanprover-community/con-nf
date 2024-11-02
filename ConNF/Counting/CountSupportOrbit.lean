import ConNF.Counting.SMulSpec
import ConNF.Counting.SpecSame

/-!
# Counting support orbits

In this file, we prove an upper bound on the amount of orbits of supports that can exist.

## Main declarations

* `ConNF.card_supportOrbit_lt`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}] [Level] [CoherentData] {β : TypeIndex} [LeLevel β]

-- TODO: fix in blueprint
structure WeakSpec (β : TypeIndex) [LeLevel β] where
  atomsBound : Tree κ β
  nearLittersBound : Tree κ β
  atoms : Tree (Set κ) β
  nearLitters : Tree (Set κ) β
  spec : Spec β

instance : SuperA (WeakSpec β) (Tree (Set κ) β) where
  superA := WeakSpec.atoms

instance : SuperN (WeakSpec β) (Tree (Set κ) β) where
  superN := WeakSpec.nearLitters

def WeakSpec.Specifies (σ : WeakSpec β) (S : Support β) : Prop :=
  ∃ T : Support β, T.Strong ∧ S.Subsupport T ∧ σ.spec = T.spec ∧
    (σ.atomsBound = λ A ↦ (S ⇘. A)ᴬ.bound) ∧
    (σ.nearLittersBound = λ A ↦ (S ⇘. A)ᴺ.bound) ∧
    (σᴬ = λ A ↦ (S ⇘. A)ᴬ.rel.dom) ∧
    (σᴺ = λ A ↦ (S ⇘. A)ᴺ.rel.dom)

theorem WeakSpec.exists (S : Support β) : ∃ σ : WeakSpec β, σ.Specifies S :=
  ⟨⟨_, _, _, _, _⟩, S.strong, S.strong_strong, S.subsupport_strong, rfl, rfl, rfl, rfl, rfl⟩

theorem WeakSpec.exists_conv (σ : WeakSpec β) {S T : Support β}
    (hS : σ.Specifies S) (hT : σ.Specifies T) :
    ∃ ρ : AllPerm β, ρᵁ • S = T := by
  obtain ⟨U, hU, hSU, hσU, habU, hNbU, haU, hNU⟩ := hS
  obtain ⟨V, hV, hSV, hσV, habV, hNbV, haV, hNV⟩ := hT
  obtain ⟨ρ, rfl⟩ := Support.exists_conv (hσU.symm.trans hσV) hU hV
  use ρ
  apply Support.ext
  intro A
  apply BaseSupport.ext
  · rw [Support.smul_derivBot, BaseSupport.smul_atoms]
    apply Enumeration.ext
    · have := habU.symm.trans habV
      rw [funext_iff] at this
      exact this A
    ext i a
    have := haU.symm.trans haV
    conv at this =>
      rw [funext_iff]; intro
      rw [funext_iff]; intro
      rw [eq_iff_iff]
    constructor
    · intro hS
      obtain ⟨b, hb⟩ := (this A i).mp ⟨_, hS⟩
      have ha' := (hSU A).1 i ((ρᵁ A)⁻¹ • a) hS
      have hb' := (hSV A).1 i b hb
      have := (U ⇘. A)ᴬ.rel_coinjective.coinjective ha' hb'
      simp only [smul_left_cancel_iff] at this
      rwa [this]
    · intro hT
      obtain ⟨b, hb⟩ := (this A i).mpr ⟨_, hT⟩
      have ha' := (hSV A).1 i a hT
      have hb' := (hSU A).1 i b hb
      have := (U ⇘. A)ᴬ.rel_coinjective.coinjective ha' hb'
      rwa [← this] at hb
  · rw [Support.smul_derivBot, BaseSupport.smul_nearLitters]
    apply Enumeration.ext
    · have := hNbU.symm.trans hNbV
      rw [funext_iff] at this
      exact this A
    ext i N₁
    have := hNU.symm.trans hNV
    conv at this =>
      rw [funext_iff]; intro
      rw [funext_iff]; intro
      rw [eq_iff_iff]
    constructor
    · intro hS
      obtain ⟨N₂, hN₂⟩ := (this A i).mp ⟨_, hS⟩
      have h₁' := (hSU A).2 i ((ρᵁ A)⁻¹ • N₁) hS
      have h₂' := (hSV A).2 i N₂ hN₂
      have := (U ⇘. A)ᴺ.rel_coinjective.coinjective h₁' h₂'
      simp only [smul_left_cancel_iff] at this
      rwa [this]
    · intro hT
      obtain ⟨N₂, hN₂⟩ := (this A i).mpr ⟨_, hT⟩
      have h₁' := (hSV A).2 i N₁ hT
      have h₂' := (hSU A).2 i N₂ hN₂
      have := (U ⇘. A)ᴺ.rel_coinjective.coinjective h₁' h₂'
      rwa [← this] at hN₂

def weakSpecEquiv :
    WeakSpec β ≃ Tree κ β × Tree κ β × Tree (Set κ) β × Tree (Set κ) β × Spec β where
  toFun σ := ⟨σ.atomsBound, σ.nearLittersBound, σᴬ, σᴺ, σ.spec⟩
  invFun σ := ⟨σ.1, σ.2.1, σ.2.2.1, σ.2.2.2.1, σ.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_weakSpec_of_card_spec (h : #(Spec β) < #μ) : #(WeakSpec β) < #μ := by
  rw [Cardinal.eq.mpr ⟨weakSpecEquiv⟩]
  simp only [mk_prod, Cardinal.lift_id]
  apply mul_lt_of_lt μ_isStrongLimit.aleph0_le (card_tree_lt κ_lt_μ)
  apply mul_lt_of_lt μ_isStrongLimit.aleph0_le (card_tree_lt κ_lt_μ)
  apply mul_lt_of_lt μ_isStrongLimit.aleph0_le
  · apply card_tree_lt
    rw [mk_set]
    exact μ_isStrongLimit.2 _ κ_lt_μ
  apply mul_lt_of_lt μ_isStrongLimit.aleph0_le
  · apply card_tree_lt
    rw [mk_set]
    exact μ_isStrongLimit.2 _ κ_lt_μ
  exact h

def specEquiv :
    Spec β ≃ Tree (Enumeration AtomCond) β × Tree (Enumeration (NearLitterCond β)) β where
  toFun σ := ⟨σᴬ, σᴺ⟩
  invFun σ := ⟨σ.1, σ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def atomCondEquiv : AtomCond ≃ Set κ × Set κ where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def nearLitterCondEquiv :
    NearLitterCond β ≃ FlexCond ⊕ (P : InflexiblePath β) × InflexCond P.δ where
  toFun x := match x with
    | .flex y => .inl y
    | .inflex P y => .inr ⟨P, y⟩
  invFun x := x.elim .flex (λ x ↦ .inflex x.1 x.2)
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

def flexCondEquiv : FlexCond ≃ Set κ where
  toFun x := x.1
  invFun x := ⟨x⟩
  left_inv _ := rfl
  right_inv _ := rfl

def inflexCondEquiv (δ : TypeIndex) [LeLevel δ] :
    InflexCond δ ≃ CodingFunction δ × Tree (Rel κ κ) δ × Tree (Rel κ κ) δ where
  toFun x := (x.χ, x.atoms, x.nearLitters)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_spec_of_card_codingFunction
    (h : ∀ δ < β, [LeLevel δ] → #(CodingFunction δ) < #μ) : #(Spec β) < #μ := by
  rw [Cardinal.eq.mpr ⟨specEquiv⟩, mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  apply mul_lt_of_lt μ_isStrongLimit.aleph0_le
  · apply card_tree_lt
    apply card_enumeration_lt
    rw [Cardinal.eq.mpr ⟨atomCondEquiv⟩, mk_prod, mk_set, Cardinal.lift_id]
    exact mul_lt_of_lt μ_isStrongLimit.aleph0_le
      (μ_isStrongLimit.2 _ κ_lt_μ) (μ_isStrongLimit.2 _ κ_lt_μ)
  · apply card_tree_lt
    apply card_enumeration_lt
    rw [Cardinal.eq.mpr ⟨nearLitterCondEquiv⟩, mk_sum, Cardinal.lift_id, mk_sigma, Cardinal.lift_id]
    apply add_lt_of_lt μ_isStrongLimit.aleph0_le
    · rw [Cardinal.eq.mpr ⟨flexCondEquiv⟩, mk_set]
      exact μ_isStrongLimit.2 _ κ_lt_μ
    · refine (sum_lt_prod _ (λ _ ↦ #μ) ?_).trans_le ?_
      · intro P
        rw [Cardinal.eq.mpr ⟨inflexCondEquiv P.δ⟩]
        simp only [mk_prod, Cardinal.lift_id]
        apply mul_lt_of_lt μ_isStrongLimit.aleph0_le (h P.δ (P.hδ.trans_le P.A.le))
        apply mul_lt_of_lt μ_isStrongLimit.aleph0_le <;>
        · apply card_tree_lt
          rw [Rel]
          rw [Cardinal.eq.mpr ⟨(Equiv.curry _ _ _).symm⟩]
          change #(Set (κ × κ)) < #μ
          rw [mk_set, mk_prod, Cardinal.lift_id, mul_mk_eq_max, max_self]
          exact μ_isStrongLimit.2 _ κ_lt_μ
      · rw [prod_const, Cardinal.lift_id, Cardinal.lift_id]
        apply mk_pow_le_of_mk_lt_ord_cof μ_isStrongLimit
        exact card_inflexiblePath_lt β

theorem card_supportOrbit_lt' : #(SupportOrbit β) ≤ #(WeakSpec β) := by
  have := WeakSpec.exists (β := β)
  choose σ hσ using this
  apply mk_le_of_injective (f := λ o ↦ σ o.out)
  intro o₁ o₂ ho
  dsimp only at ho
  have h₁ := hσ o₁.out
  have h₂ := hσ o₂.out
  rw [ho] at h₁
  obtain ⟨ρ, hρ⟩ := WeakSpec.exists_conv _ h₁ h₂
  have := congr_arg Support.orbit hρ
  rwa [Support.smul_orbit, SupportOrbit.out_orbit, SupportOrbit.out_orbit] at this

theorem card_supportOrbit_lt (h : ∀ δ < β, [LeLevel δ] → #(CodingFunction δ) < #μ) :
    #(SupportOrbit β) < #μ :=
  card_supportOrbit_lt'.trans_lt (card_weakSpec_of_card_spec (card_spec_of_card_codingFunction h))

end ConNF
