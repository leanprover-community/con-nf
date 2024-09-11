import ConNF.FOA.StrApprox

/-!
# Approximations of structural permutations

In this file, we state and prove the freedom of action theorem.

## Main declarations

* `ConNF.StrApprox.Approximates`: A structural approximation approximates an allowable permutation
    if it agrees with it wherever it is defined.
* `ConNF.StrApprox.ExactlyApproximates`: A structural approximation exactly approximates an
    allowable permutation if it approximates the permutation and every undefined atom is
    "typical" in a suitable sense.
* `ConNF.StrApprox.FreedomOfAction`: Freedom of action for structural approximations:
    every coherent approximation exactly approximates some allowable permutation.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}]

namespace BaseApprox

structure Approximates (ψ : BaseApprox) (π : BasePerm) : Prop where
  atoms : ∀ a₁ a₂, ψᴬ a₁ a₂ → a₂ = π • a₁
  nearLitters : ∀ N₁ N₂, ψᴺ N₁ N₂ → N₂ = π • N₁

structure ExactlyApproximates (ψ : BaseApprox) (π : BasePerm)
    extends ψ.Approximates π : Prop where
  smul_litter : ∀ a, a ∉ ψᴬ.dom → (π • a)ᴸ = π • aᴸ
  inv_smul_litter : ∀ a, a ∉ ψᴬ.dom → (π⁻¹ • a)ᴸ = π⁻¹ • aᴸ

end BaseApprox

namespace StrApprox

variable [Level] [CoherentData] {β : TypeIndex} [LeLevel β]

def Approximates (ψ : StrApprox β) (ρ : AllPerm β) : Prop :=
  ∀ A, (ψ A).Approximates (ρᵁ A)

def ExactlyApproximates (ψ : StrApprox β) (ρ : AllPerm β) : Prop :=
  ∀ A, (ψ A).ExactlyApproximates (ρᵁ A)

theorem ExactlyApproximates.toApproximates {ψ : StrApprox β} {ρ : AllPerm β}
    (h : ψ.ExactlyApproximates ρ) :
    ψ.Approximates ρ :=
  λ A ↦ (h A).toApproximates

def FreedomOfAction (β : TypeIndex) [LeLevel β] : Prop :=
  ∀ ψ : StrApprox β, ψ.Coherent → ∃ ρ, ψ.ExactlyApproximates ρ

theorem smul_atom_mem_dom_of_approximates {ψ : StrApprox β} {ρ : AllPerm β}
    (h : ψ.Approximates ρ) {A : β ↝ ⊥} {a : Atom} (ha : a ∈ (ψ A)ᴬ.dom) :
    ρᵁ A • a ∈ (ψ A)ᴬ.dom := by
  obtain ⟨b, ha⟩ := ha
  cases (h A).atoms a b ha
  exact (ψ A).atoms_permutative.mem_dom ha

theorem smul_nearLitter_mem_dom_of_approximates {ψ : StrApprox β} {ρ : AllPerm β}
    (h : ψ.Approximates ρ) {A : β ↝ ⊥} {N : NearLitter} (hN : N ∈ (ψ A)ᴺ.dom) :
    ρᵁ A • N ∈ (ψ A)ᴺ.dom := by
  obtain ⟨N', hN⟩ := hN
  cases (h A).nearLitters N N' hN
  exact (ψ A).nearLitters_permutative.mem_dom hN

theorem inv_smul_atom_mem_dom_of_approximates {ψ : StrApprox β} {ρ : AllPerm β}
    (h : ψ.Approximates ρ) {A : β ↝ ⊥} {a : Atom} (ha : a ∈ (ψ A)ᴬ.dom) :
    (ρᵁ A)⁻¹ • a ∈ (ψ A)ᴬ.dom := by
  obtain ⟨b, ha⟩ := ha
  obtain ⟨c, ha'⟩ := (ψ A).atoms_permutative.mem_codom ha
  cases (h A).atoms c a ha'
  rw [inv_smul_smul]
  exact ⟨_, ha'⟩

theorem inv_smul_nearLitter_mem_dom_of_approximates {ψ : StrApprox β} {ρ : AllPerm β}
    (h : ψ.Approximates ρ) {A : β ↝ ⊥} {N : NearLitter} (hN : N ∈ (ψ A)ᴺ.dom) :
    (ρᵁ A)⁻¹ • N ∈ (ψ A)ᴺ.dom := by
  obtain ⟨N', hN⟩ := hN
  obtain ⟨N'', hN'⟩ := (ψ A).nearLitters_permutative.mem_codom hN
  cases (h A).nearLitters N'' N hN'
  rw [inv_smul_smul]
  exact ⟨_, hN'⟩

theorem zsmul_atom_mem_dom_of_approximates {ψ : StrApprox β} {ρ : AllPerm β}
    (h : ψ.Approximates ρ) {A : β ↝ ⊥} {a : Atom} (ha : a ∈ (ψ A)ᴬ.dom) (n : ℤ) :
    (ρᵁ A) ^ n • a ∈ (ψ A)ᴬ.dom := by
  induction n using Int.inductionOn' (b := 0) with
  | H0 => exact ha
  | Hs k _ ih =>
    rw [add_comm, zpow_add, zpow_one, mul_smul]
    exact smul_atom_mem_dom_of_approximates h ih
  | Hp k _ ih =>
    rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg, zpow_one, mul_smul]
    exact inv_smul_atom_mem_dom_of_approximates h ih

theorem zsmul_nearLitter_mem_dom_of_approximates {ψ : StrApprox β} {ρ : AllPerm β}
    (h : ψ.Approximates ρ) {A : β ↝ ⊥} {N : NearLitter} (hN : N ∈ (ψ A)ᴺ.dom) (n : ℤ) :
    (ρᵁ A) ^ n • N ∈ (ψ A)ᴺ.dom := by
  induction n using Int.inductionOn' (b := 0) with
  | H0 => rwa [zpow_zero, one_smul]
  | Hs k _ ih =>
    rw [add_comm, zpow_add, zpow_one, mul_smul]
    exact smul_nearLitter_mem_dom_of_approximates h ih
  | Hp k _ ih =>
    rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg, zpow_one, mul_smul]
    exact inv_smul_nearLitter_mem_dom_of_approximates h ih

theorem zsmul_atom_mem_dom_iff_of_approximates {ψ : StrApprox β} {ρ : AllPerm β}
    (h : ψ.Approximates ρ) {A : β ↝ ⊥} {a : Atom} (n : ℤ) :
    (ρᵁ A) ^ n • a ∈ (ψ A)ᴬ.dom ↔ a ∈ (ψ A)ᴬ.dom := by
  constructor
  · intro ha
    have := zsmul_atom_mem_dom_of_approximates h ha (-n)
    rwa [zpow_neg, inv_smul_smul] at this
  · intro ha
    exact zsmul_atom_mem_dom_of_approximates h ha n

theorem zsmul_nearLitter_mem_dom_iff_of_approximates {ψ : StrApprox β} {ρ : AllPerm β}
    (h : ψ.Approximates ρ) {A : β ↝ ⊥} {N : NearLitter} (n : ℤ) :
    (ρᵁ A) ^ n • N ∈ (ψ A)ᴺ.dom ↔ N ∈ (ψ A)ᴺ.dom := by
  constructor
  · intro hN
    have := zsmul_nearLitter_mem_dom_of_approximates h hN (-n)
    rwa [zpow_neg, inv_smul_smul] at this
  · intro hN
    exact zsmul_nearLitter_mem_dom_of_approximates h hN n

theorem smul_support_eq_smul_of_approximates {ψ : StrApprox β} {ρ : AllPerm β}
    (h : ψ.Approximates ρ) {S : Support β}
    (hSA : ∀ A, ∀ a ∈ (S ⇘. A)ᴬ, a ∈ (ψ A)ᴬ.dom)
    (hSN : ∀ A, ∀ N ∈ (S ⇘. A)ᴺ, N ∈ (ψ A)ᴺ.dom) :
    ψ • S = ρᵁ • S := by
  rw [smul_support_eq_smul_iff]
  intro A
  constructor
  · intro a ha
    obtain ⟨b, hb⟩ := hSA A a ha
    rwa [← (h A).atoms a b hb]
  · intro a ha
    obtain ⟨b, hb⟩ := hSN A a ha
    rwa [← (h A).nearLitters a b hb]

/-- Add a flexible litter to this approximation. -/
def addFlexible (ψ : StrApprox β) (A : β ↝ ⊥) (L : Litter) (hLψ : L ∉ (ψ A)ᴸ.dom) :
    StrApprox β :=
  ψ.addOrbit A (λ _ ↦ L) (λ _ _ _ ↦ id) (λ _ ↦ hLψ)

theorem addFlexible_coherent {ψ : StrApprox β} {A : β ↝ ⊥} {L : Litter} {hLψ : L ∉ (ψ A)ᴸ.dom}
    (hψ : ψ.Coherent) (hL : ¬Inflexible A L) :
    (ψ.addFlexible A L hLψ).Coherent := by
  apply addOrbit_coherent hψ
  intro
  rwa [coherentAt_flexible hL]

theorem addInflexible_aux (P : InflexiblePath β) (t : Tangle P.δ) (ρ : AllPerm P.δ) :
    ∀ m n k : ℤ, fuzz P.hδε (ρ ^ m • t) = fuzz P.hδε (ρ ^ n • t) →
      fuzz P.hδε (ρ ^ (m + k) • t) = fuzz P.hδε (ρ ^ (n + k) • t) := by
  intro m n k h
  have := congr_arg (ρ ^ k • ·) (fuzz_injective h)
  dsimp only at this
  rw [smul_smul, smul_smul, ← zpow_add, ← zpow_add, add_comm, add_comm k] at this
  rw [this]

def addInflexible' (ψ : StrApprox β) {A : β ↝ ⊥}
    (P : InflexiblePath β) (t : Tangle P.δ) (ρ : AllPerm P.δ)
    (hL : ∀ n : ℤ, fuzz P.hδε (ρ ^ n • t) ∉ (ψ A)ᴸ.dom) :
    StrApprox β :=
  ψ.addOrbit A (λ n ↦ fuzz P.hδε (ρ ^ n • t)) (addInflexible_aux P t ρ) hL

theorem smul_support_zpow {ψ : StrApprox β} {ρ : AllPerm β} (h : ψ.Approximates ρ)
    (t : Tangle β) {n : ℤ}
    (hLA : ∀ B, ∀ a ∈ (t.support ⇘. B)ᴬ, a ∈ (ψ B)ᴬ.dom)
    (hLN : ∀ B, ∀ N ∈ (t.support ⇘. B)ᴺ, N ∈ (ψ B)ᴺ.dom) :
    ψ • (ρ ^ n • t).support = ρᵁ • (ρ ^ n • t).support := by
  apply smul_support_eq_smul_of_approximates h
  · intro B a ha
    rw [Tangle.smul_support, Support.smul_derivBot, BaseSupport.smul_atoms,
      Enumeration.mem_smul_iff, allPermForget_zpow, Tree.zpow_apply, ← zpow_neg] at ha
    rw [← zsmul_atom_mem_dom_iff_of_approximates h (-n)]
    exact hLA B _ ha
  · intro B N hN
    rw [Tangle.smul_support, Support.smul_derivBot, BaseSupport.smul_nearLitters,
      Enumeration.mem_smul_iff, allPermForget_zpow, Tree.zpow_apply, ← zpow_neg] at hN
    rw [← zsmul_nearLitter_mem_dom_iff_of_approximates h (-n)]
    exact hLN B _ hN

theorem addInflexible'_coherent {ψ : StrApprox β} {A : β ↝ ⊥}
    {P : InflexiblePath β} {t : Tangle P.δ} (hA : A = P.A ↘ P.hε ↘.)
    {ρ : AllPerm P.δ} (hρ : Approximates (ψ ⇘ P.A ↘ P.hδ) ρ)
    {hL : ∀ n : ℤ, fuzz P.hδε (ρ ^ n • t) ∉ (ψ A)ᴸ.dom}
    (hψ : ψ.Coherent)
    (hLA : ∀ B, ∀ a ∈ (t.support ⇘. B)ᴬ, a ∈ (ψ (P.A ↘ P.hδ ⇘ B))ᴬ.dom)
    (hLN : ∀ B, ∀ N ∈ (t.support ⇘. B)ᴺ, N ∈ (ψ (P.A ↘ P.hδ ⇘ B))ᴺ.dom) :
    (ψ.addInflexible' P t ρ hL).Coherent := by
  apply addOrbit_coherent hψ
  intro n
  rw [coherentAt_inflexible hA rfl]
  use ρ
  constructor
  · apply smul_support_zpow hρ
    · simp only [Tree.sderiv_apply, Tree.deriv_apply, Path.deriv_scoderiv]
      exact hLA
    · simp only [Tree.sderiv_apply, Tree.deriv_apply, Path.deriv_scoderiv]
      exact hLN
  · rw [add_comm, zpow_add, zpow_one, mul_smul]

theorem mem_dom_of_inflexible {ψ : StrApprox β} {A : β ↝ ⊥} {L : Litter}
    {P : InflexiblePath β} {t : Tangle P.δ} (hA : A = P.A ↘ P.hε ↘.) (ht : L = fuzz P.hδε t)
    {ρ : AllPerm P.δ} (hρ : Approximates (ψ ⇘ P.A ↘ P.hδ) ρ)
    {n : ℤ} (hL : fuzz P.hδε (ρ ^ n • t) ∈ (ψ A)ᴸ.dom)
    (hψ : ψ.Coherent)
    (hLA : ∀ B, ∀ a ∈ (t.support ⇘. B)ᴬ, a ∈ (ψ (P.A ↘ P.hδ ⇘ B))ᴬ.dom)
    (hLN : ∀ B, ∀ N ∈ (t.support ⇘. B)ᴺ, N ∈ (ψ (P.A ↘ P.hδ ⇘ B))ᴺ.dom) :
    L ∈ (ψ A)ᴸ.dom := by
  induction n using Int.inductionOn' (b := 0) with
  | H0 =>
    rw [zpow_zero, one_smul] at hL
    rwa [ht]
  | Hs k _ ih =>
    apply ih
    rw [← (ψ A).litters_permutative.codom_eq_dom] at hL
    obtain ⟨L', hL⟩ := hL
    have := smul_eq_of_coherentAt_inflexible' hA rfl (hψ A L' _ hL) ρ⁻¹ ?_
    · rw [smul_smul, ← zpow_neg_one, ← zpow_add, neg_add_cancel_comm_assoc] at this
      rw [← this]
      exact ⟨_, hL⟩
    · have := smul_support_zpow hρ t (n := k) ?_ ?_
      · rw [Tangle.smul_support, allPermForget_zpow] at this
        rw [Tangle.smul_support, smul_smul, allPermForget_inv, ← zpow_neg_one, allPermForget_zpow,
          ← zpow_add, neg_add_cancel_comm_assoc, this, add_comm, zpow_add, zpow_one, mul_smul]
      · simp only [Tree.sderiv_apply, Tree.deriv_apply, Path.deriv_scoderiv]
        exact hLA
      · simp only [Tree.sderiv_apply, Tree.deriv_apply, Path.deriv_scoderiv]
        exact hLN
  | Hp k _ ih =>
    apply ih
    obtain ⟨L', hL⟩ := hL
    have := smul_eq_of_coherentAt_inflexible hA rfl (hψ A _ L' hL) ρ ?_
    · rw [smul_smul, mul_self_zpow, sub_add_cancel] at this
      rw [← this]
      exact (ψ A).litters_permutative.mem_dom hL
    · apply smul_support_zpow hρ
      · simp only [Tree.sderiv_apply, Tree.deriv_apply, Path.deriv_scoderiv]
        exact hLA
      · simp only [Tree.sderiv_apply, Tree.deriv_apply, Path.deriv_scoderiv]
        exact hLN

open scoped Classical in
def addInflexible (ψ : StrApprox β) (A : β ↝ ⊥)
    (P : InflexiblePath β) (t : Tangle P.δ) (ρ : AllPerm P.δ) : StrApprox β :=
  if hL : ∀ n : ℤ, fuzz P.hδε (ρ ^ n • t) ∉ (ψ A)ᴸ.dom then ψ.addInflexible' P t ρ hL else ψ

theorem le_addInflexible (ψ : StrApprox β) (A : β ↝ ⊥)
    (P : InflexiblePath β) (t : Tangle P.δ) (ρ : AllPerm P.δ) :
    ψ ≤ ψ.addInflexible A P t ρ := by
  rw [addInflexible]
  split_ifs
  · exact le_addOrbit
  · exact le_rfl

theorem addInflexible_coherent {ψ : StrApprox β} {A : β ↝ ⊥}
    {P : InflexiblePath β} {t : Tangle P.δ} (hA : A = P.A ↘ P.hε ↘.)
    {ρ : AllPerm P.δ} (hρ : Approximates (ψ ⇘ P.A ↘ P.hδ) ρ)
    (hψ : ψ.Coherent)
    (hLA : ∀ B, ∀ a ∈ (t.support ⇘. B)ᴬ, a ∈ (ψ (P.A ↘ P.hδ ⇘ B))ᴬ.dom)
    (hLN : ∀ B, ∀ N ∈ (t.support ⇘. B)ᴺ, N ∈ (ψ (P.A ↘ P.hδ ⇘ B))ᴺ.dom) :
    (ψ.addInflexible A P t ρ).Coherent := by
  rw [addInflexible]
  split_ifs
  · exact addInflexible'_coherent hA hρ hψ hLA hLN
  · exact hψ

theorem mem_addInflexible_dom {ψ : StrApprox β} {A : β ↝ ⊥} {L : Litter}
    {P : InflexiblePath β} {t : Tangle P.δ} (hA : A = P.A ↘ P.hε ↘.) (hL : L = fuzz P.hδε t)
    {ρ : AllPerm P.δ} (hρ : Approximates (ψ ⇘ P.A ↘ P.hδ) ρ)
    (hψ : ψ.Coherent)
    (hLA : ∀ B, ∀ a ∈ (t.support ⇘. B)ᴬ, a ∈ (ψ (P.A ↘ P.hδ ⇘ B))ᴬ.dom)
    (hLN : ∀ B, ∀ N ∈ (t.support ⇘. B)ᴺ, N ∈ (ψ (P.A ↘ P.hδ ⇘ B))ᴺ.dom) :
    L ∈ (ψ.addInflexible A P t ρ A)ᴸ.dom := by
  rw [addInflexible]
  split_ifs with hL'
  · rw [addInflexible', addOrbit_apply, BaseApprox.addOrbit_litters, Rel.sup_dom,
      BaseApprox.addOrbitLitters_dom]
    right
    use 0
    simp only [zpow_zero, one_smul, hL]
  · push_neg at hL'
    obtain ⟨n, hn⟩ := hL'
    exact mem_dom_of_inflexible hA hL hρ hn hψ hLA hLN

theorem exists_extension_of_minimal (ψ : StrApprox β) (A : β ↝ ⊥) (L : Litter) (hψ : ψ.Coherent)
    (foa : ∀ δ < β, [LeLevel δ] → FreedomOfAction δ)
    (hLA : ∀ B, ∀ a, pos a < pos L → a ∈ (ψ B)ᴬ.dom)
    (hLN : ∀ B, ∀ N, pos N < pos L → N ∈ (ψ B)ᴺ.dom) :
    ∃ χ ≥ ψ, χ.Coherent ∧ L ∈ (χ A)ᴸ.dom := by
  obtain (⟨P, t, hA, ht⟩ | hL) := inflexible_cases A L
  · obtain ⟨ρ, hρ⟩ := foa P.δ (P.hδ.trans_le P.A.le) (ψ ⇘ (P.A ↘ P.hδ)) (hψ.comp (P.A ↘ P.hδ))
    have h₁ : ∀ (B : P.δ ↝ ⊥), ∀ a ∈ (t.support ⇘. B)ᴬ, a ∈ (ψ (P.A ↘ P.hδ ⇘ B))ᴬ.dom := by
      intro B a ha
      apply hLA
      rw [ht]
      exact (pos_atom_lt_pos t B a ha).trans (pos_fuzz P.hδε t)
    have h₂ : ∀ (B : P.δ ↝ ⊥), ∀ N ∈ (t.support ⇘. B)ᴺ, N ∈ (ψ (P.A ↘ P.hδ ⇘ B))ᴺ.dom := by
      intro B N hN
      apply hLN
      rw [ht]
      exact (pos_nearLitter_lt_pos t B N hN).trans (pos_fuzz P.hδε t)
    refine ⟨addInflexible ψ A P t ρ, le_addInflexible ψ A P t ρ, ?_, ?_⟩
    · refine addInflexible_coherent hA ?_ hψ h₁ h₂
      rw [Tree.deriv_sderiv]
      exact hρ.toApproximates
    · refine mem_addInflexible_dom hA ht ?_ hψ h₁ h₂
      rw [Tree.deriv_sderiv]
      exact hρ.toApproximates
  · by_cases hL' : L ∈ (ψ A)ᴸ.dom
    · use ψ
    · refine ⟨addFlexible ψ A L hL', le_addOrbit, addFlexible_coherent hψ hL, ?_⟩
      rw [addFlexible, addOrbit_apply, BaseApprox.addOrbit_litters, Rel.sup_dom,
        BaseApprox.addOrbitLitters_dom]
      right
      use 0

end StrApprox

end ConNF
