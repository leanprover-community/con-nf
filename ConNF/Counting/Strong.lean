import ConNF.Basic.ReflTransGen
import ConNF.FOA.Inflexible

/-!
# Strong supports

In this file, we define strong supports.

## Main declarations

* `ConNF.Support.Strong`: The property that a support is strong.
-/

noncomputable section
universe u

open Cardinal Ordinal
open scoped symmDiff

namespace ConNF

variable [Params.{u}] {β : TypeIndex}

structure BaseSupport.Closed (S : BaseSupport) : Prop where
  interference_subset {N₁ N₂ : NearLitter} :
    N₁ ∈ Sᴺ → N₂ ∈ Sᴺ → ∀ a ∈ interference N₁ N₂, a ∈ Sᴬ

namespace Support

variable [Level] [CoherentData] [LeLevel β]

structure PreStrong (S : Support β) : Prop where
  support_le {A : β ↝ ⊥} {N : NearLitter} (h : N ∈ (S ⇘. A)ᴺ)
    (P : InflexiblePath β) (t : Tangle P.δ)
    (hA : A = P.A ↘ P.hε ↘.) (ht : Nᴸ = fuzz P.hδε t) :
    t.support ≤ S ⇘ (P.A ↘ P.hδ)

structure Closed (S : Support β) : Prop where
  closed : ∀ A, (S ⇘. A).Closed

structure Strong (S : Support β) extends S.PreStrong, S.Closed : Prop

theorem PreStrong.smul {S : Support β} (hS : S.PreStrong) (ρ : AllPerm β) : (ρᵁ • S).PreStrong := by
  constructor
  intro A N hN P t hA ht
  rw [smul_derivBot, BaseSupport.smul_nearLitters, Enumeration.mem_smul] at hN
  have := hS.support_le hN P (ρ⁻¹ ⇘ P.A ↘ P.hδ • t) hA ?_
  · convert smul_le_smul this (ρᵁ ⇘ P.A ↘ P.hδ) using 1
    · rw [Tangle.smul_support, smul_smul,
        allPermSderiv_forget, allPermDeriv_forget, allPermForget_inv,
        Tree.inv_deriv, Tree.inv_sderiv, mul_inv_cancel, one_smul]
    · ext B : 1
      rw [smul_derivBot, Tree.sderiv_apply, Tree.deriv_apply, Path.deriv_scoderiv]
      rfl
  · rw [← smul_fuzz P.hδ P.hε P.hδε, allPermDeriv_forget, allPermForget_inv,
      BasePerm.smul_nearLitter_litter, ← Tree.inv_apply, hA, ht]
    rfl

theorem Closed.smul {S : Support β} (hS : S.Closed) (ρ : AllPerm β) : (ρᵁ • S).Closed := by
  constructor
  intro A
  constructor
  intro N₁ N₂ h₁ h₂
  simp only [smul_derivBot, BaseSupport.smul_nearLitters, BaseSupport.smul_atoms,
    Enumeration.mem_smul] at h₁ h₂ ⊢
  intro a ha
  apply (hS.closed A).interference_subset h₁ h₂
  rwa [← BasePerm.smul_interference, Set.smul_mem_smul_set_iff]

theorem Strong.smul {S : Support β} (hS : S.Strong) (ρ : AllPerm β) : (ρᵁ • S).Strong :=
  ⟨hS.toPreStrong.smul ρ, hS.toClosed.smul ρ⟩

def Constrains : Rel (β ↝ ⊥ × NearLitter) (β ↝ ⊥ × NearLitter) :=
  λ x y ↦ ∃ (P : InflexiblePath β) (t : Tangle P.δ) (B : P.δ ↝ ⊥),
    x.1 = P.A ↘ P.hδ ⇘ B ∧ x.2 ∈ (t.support ⇘. B)ᴺ ∧ y.1 = P.A ↘ P.hε ↘. ∧ y.2ᴸ = fuzz P.hδε t

theorem constrains_subrelation :
    Subrelation (Constrains (β := β)) (InvImage (pos · < pos ·) Prod.snd) := by
  rintro ⟨A₁, N₁⟩ ⟨A₂, N₂⟩ ⟨P, t, B, rfl, hN₁, _, ht⟩
  apply (pos_nearLitter_lt_pos t B N₁ hN₁).trans
  apply (pos_fuzz P.hδε t).trans
  rw [← ht]
  exact N₂.pos_litter_lt_pos

theorem constrains_wf : WellFounded (Constrains (β := β)) := by
  apply constrains_subrelation.wf
  apply InvImage.wf Prod.snd
  apply InvImage.wf pos
  exact wellFounded_lt

theorem not_constrains_of_flexible {x : β ↝ ⊥ × NearLitter} {A : β ↝ ⊥} {N : NearLitter}
    (h : ¬Inflexible A Nᴸ) : ¬Constrains x (A, N) := by
  rintro ⟨P, t, B, _, _, hA, ht⟩
  exact h ⟨P, t, hA, ht⟩

theorem constrains_iff_of_inflexible {x : β ↝ ⊥ × NearLitter} {A : β ↝ ⊥} {N : NearLitter}
    (P : InflexiblePath β) (t : Tangle P.δ) (hA : A = P.A ↘ P.hε ↘.) (ht : Nᴸ = fuzz P.hδε t) :
    Constrains x (A, N) ↔ x ∈ (t.support ⇗ (P.A ↘ P.hδ))ᴺ := by
  obtain ⟨C, N'⟩ := x
  constructor
  · rintro ⟨P', t', B, hx₁, hx₂, hA', ht'⟩
    cases inflexiblePath_subsingleton hA hA' ht ht'
    cases fuzz_injective (ht.symm.trans ht')
    rw [Enumeration.mem_path_iff]
    subst hx₁
    rw [← Enumeration.deriv_derivBot, deriv_nearLitters, derivBot_nearLitters,
      Support.coderiv_deriv_eq]
    exact hx₂
  · intro hx
    rw [Enumeration.mem_path_iff, derivBot_nearLitters] at hx
    obtain ⟨i, ⟨B, N''⟩, h, hx⟩ := hx
    cases hx
    exact ⟨P, t, B, rfl, ⟨i, h⟩, hA, ht⟩

theorem constrains_small (y : β ↝ ⊥ × NearLitter) :
    Small {x | Constrains x y} := by
  obtain ⟨A, N⟩ := y
  obtain (⟨P, t, hA, ht⟩ | h) := inflexible_cases A Nᴸ
  · simp only [constrains_iff_of_inflexible P t hA ht]
    exact (t.support ⇗ (P.A ↘ P.hδ))ᴺ.coe_small
  · simp only [not_constrains_of_flexible h, Set.setOf_false, small_empty]

theorem reflTransGen_constrains_small (s : Set (β ↝ ⊥ × NearLitter)) (hs : Small s) :
    Small {x | ∃ y ∈ s, Relation.ReflTransGen Constrains x y} := by
  have := Rel.card_reflTransGen_lt (constrains_small (β := β)) κ_isRegular aleph0_lt_κ
  convert small_biUnion hs (λ x _ ↦ this x) using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop', nonempty_prop]

/-- A support that contains all of the near-litters that transitively constrain something in `S`. -/
def constrainsNearLitters (S : Support β) : Support β :=
  ⟨.empty, .ofSet _ (reflTransGen_constrains_small Sᴺ Sᴺ.coe_small)⟩

theorem mem_constrainsNearLitters_nearLitters (S : Support β) (A : β ↝ ⊥) (N : NearLitter) :
    N ∈ (S.constrainsNearLitters ⇘. A)ᴺ ↔
    ∃ B N', N' ∈ (S ⇘. B)ᴺ ∧ Relation.ReflTransGen Constrains (A, N) (B, N') := by
  apply (Enumeration.mem_ofSet_iff _ (reflTransGen_constrains_small Sᴺ Sᴺ.coe_small) _).trans
  simp only [Prod.exists, Set.mem_setOf_eq]
  rfl

theorem constrainsNearLitters_atoms (S : Support β) (A : β ↝ ⊥) :
    (S.constrainsNearLitters ⇘. A)ᴬ = .empty :=
  rfl

-- TODO: Fix this in the blueprint

def ConstrainsAtom (S : Support β) (a : β ↝ ⊥ × Atom) : Prop :=
  ∃ (P : InflexiblePath β) (t : Tangle P.δ) (B : P.δ ↝ ⊥) (A : β ↝ ⊥) (N : NearLitter),
    a.1 = P.A ↘ P.hδ ⇘ B ∧ a.2 ∈ (t.support ⇘. B)ᴬ ∧
    A = P.A ↘ P.hε ↘. ∧ Nᴸ = fuzz P.hδε t ∧ N ∈ (S ⇘. A)ᴺ

theorem constrainsAtoms_small (S : Support β) :
    Small {a | ConstrainsAtom S a} := by
  suffices Small (⋃ N ∈ Sᴺ,
      ⋃ (x : (P : InflexiblePath β) × Tangle P.δ)
        (_ : N.1 = x.1.A ↘ x.1.hε ↘. ∧ N.2ᴸ = fuzz x.1.hδε x.2),
      (x.2.supportᴬ ⇗ (x.1.A ↘ x.1.hδ) : Set (β ↝ ⊥ × Atom))) by
    apply this.mono
    rintro ⟨_, a⟩ ⟨P, t, B, A, N, rfl, ha, hA, ht, hN⟩
    simp only [Set.mem_iUnion]
    refine ⟨(A, N), hN, ⟨P, t⟩, ⟨hA, ht⟩, ?_⟩
    rwa [coderiv_atoms, ← Enumeration.mem_iff, Enumeration.mem_path_iff,
      ← Enumeration.deriv_derivBot, deriv_atoms, coderiv_deriv_eq, derivBot_atoms]
  apply small_biUnion Sᴺ.coe_small
  intro N _
  apply small_biUnion
  · apply small_of_subsingleton
    rintro ⟨P₁, t₁⟩ ⟨hA₁, ht₁⟩ ⟨P₂, t₂⟩ ⟨hA₂, ht₂⟩
    cases inflexiblePath_subsingleton hA₁ hA₂ ht₁ ht₂
    cases fuzz_injective (ht₁.symm.trans ht₂)
    rfl
  · intro _ _
    exact Enumeration.coe_small _

/-- A support that contains all the atoms that constrain something in `S`. -/
def constrainsAtoms (S : Support β) : Support β :=
  ⟨.ofSet _ S.constrainsAtoms_small, .empty⟩

theorem mem_constrainsAtoms_atoms (S : Support β) (A : β ↝ ⊥) (a : Atom) :
    a ∈ (S.constrainsAtoms ⇘. A)ᴬ ↔ ConstrainsAtom S (A, a) :=
  Enumeration.mem_ofSet_iff _ S.constrainsAtoms_small _

theorem constrainsAtoms_nearLitters (S : Support β) (A : β ↝ ⊥) :
    (S.constrainsAtoms ⇘. A)ᴺ = .empty :=
  rfl

def preStrong (S : Support β) : Support β :=
  (S + S.constrainsNearLitters) + (S + S.constrainsNearLitters).constrainsAtoms

theorem subsupport_preStrong (S : Support β) :
    S.Subsupport S.preStrong :=
  subsupport_add.trans subsupport_add

theorem preStrong_atoms (S : Support β) (A : β ↝ ⊥) :
    (S.preStrong ⇘. A)ᴬ = (S ⇘. A)ᴬ + ((S + S.constrainsNearLitters).constrainsAtoms ⇘. A)ᴬ := by
  simp only [preStrong, add_derivBot, BaseSupport.add_atoms, constrainsNearLitters_atoms,
    Enumeration.add_empty]

theorem preStrong_nearLitters (S : Support β) (A : β ↝ ⊥) :
    (S.preStrong ⇘. A)ᴺ = (S ⇘. A)ᴺ + (S.constrainsNearLitters ⇘. A)ᴺ := by
  simp only [preStrong, add_derivBot, BaseSupport.add_nearLitters, constrainsAtoms_nearLitters,
    Enumeration.add_empty]

theorem preStrong_preStrong (S : Support β) : S.preStrong.PreStrong := by
  constructor
  intro A N hN P t hA ht B
  constructor
  · intro a ha
    rw [Support.deriv_derivBot, preStrong_atoms, Enumeration.mem_add_iff, mem_constrainsAtoms_atoms]
    refine Or.inr ⟨P, t, B, A, N, rfl, ha, hA, ht, ?_⟩
    rwa [preStrong_nearLitters] at hN
  · intro N' hN'
    rw [Support.deriv_derivBot, preStrong_nearLitters, Enumeration.mem_add_iff,
      mem_constrainsNearLitters_nearLitters]
    rw [preStrong_nearLitters, Enumeration.mem_add_iff,
      mem_constrainsNearLitters_nearLitters] at hN
    obtain (hN | ⟨A', N'', hN''₁, hN''₂⟩) := hN
    · exact Or.inr ⟨A, N, hN, Relation.ReflTransGen.single ⟨P, t, B, rfl, hN', hA, ht⟩⟩
    · exact Or.inr ⟨A', N'', hN''₁, hN''₂.head ⟨P, t, B, rfl, hN', hA, ht⟩⟩

omit [Level] [CoherentData] [LeLevel β] in
theorem interference_small (S : Support β) :
    Small {a : β ↝ ⊥ × Atom |
      ∃ N₁ N₂, N₁ ∈ (S ⇘. a.1)ᴺ ∧ N₂ ∈ (S ⇘. a.1)ᴺ ∧ a.2 ∈ interference N₁ N₂} := by
  suffices Small (⋃ N₁ ∈ Sᴺ, ⋃ N₂ ∈ Sᴺ, (N₁.1, ·) '' interference N₁.2 N₂.2) by
    apply this.mono
    rintro ⟨A, a⟩ ⟨N₁, N₂, hN₁, hN₂, ha⟩
    simp only [Set.mem_iUnion]
    exact ⟨(A, N₁), hN₁, (A, N₂), hN₂, a, ha, rfl⟩
  apply small_biUnion Sᴺ.coe_small
  intro N₁ _
  apply small_biUnion Sᴺ.coe_small
  intro N₂ _
  apply Small.image
  exact ConNF.interference_small _ _

def interferenceSupport (S : Support β) : Support β :=
  ⟨.ofSet _ S.interference_small, .empty⟩

omit [Level] [CoherentData] [LeLevel β] in
theorem mem_interferenceSupport_atoms (S : Support β) (A : β ↝ ⊥) (a : Atom) :
    a ∈ (S.interferenceSupport ⇘. A)ᴬ ↔
    ∃ N₁ ∈ (S ⇘. A)ᴺ, ∃ N₂ ∈ (S ⇘. A)ᴺ, a ∈ interference N₁ N₂ := by
  apply (Enumeration.mem_ofSet_iff _ S.interference_small _).trans
  simp only [exists_and_left, Set.mem_setOf_eq]

omit [Level] [CoherentData] [LeLevel β] in
theorem interferenceSupport_nearLitters (S : Support β) (A : β ↝ ⊥) :
    (S.interferenceSupport ⇘. A)ᴺ = .empty :=
  rfl

def close (S : Support β) : Support β :=
  S + S.interferenceSupport

omit [Level] [CoherentData] [LeLevel β] in
theorem subsupport_close (S : Support β) :
    S.Subsupport S.close :=
  subsupport_add

omit [Level] [CoherentData] [LeLevel β] in
theorem close_atoms (S : Support β) (A : β ↝ ⊥) :
    (S.close ⇘. A)ᴬ = (S ⇘. A)ᴬ + (S.interferenceSupport ⇘. A)ᴬ :=
  rfl

omit [Level] [CoherentData] [LeLevel β] in
theorem close_nearLitters (S : Support β) (A : β ↝ ⊥) :
    (S.close ⇘. A)ᴺ = (S ⇘. A)ᴺ := by
  rw [close, add_derivBot, BaseSupport.add_nearLitters, interferenceSupport_nearLitters,
    Enumeration.add_empty]

omit [Level] [CoherentData] [LeLevel β] in
theorem close_closed (S : Support β) :
    S.close.Closed := by
  constructor
  intro A
  constructor
  intro N₁ N₂ hN₁ hN₂ a ha
  rw [close_nearLitters] at hN₁ hN₂
  rw [close_atoms, Enumeration.mem_add_iff, mem_interferenceSupport_atoms]
  exact Or.inr ⟨N₁, hN₁, N₂, hN₂, ha⟩

def strong (S : Support β) : Support β :=
  S.preStrong.close

theorem preStrong_subsupport_strong (S : Support β) :
    S.preStrong.Subsupport S.strong :=
  S.preStrong.subsupport_close

theorem subsupport_strong (S : Support β) :
    S.Subsupport S.strong :=
  S.subsupport_preStrong.trans S.preStrong_subsupport_strong

theorem strong_strong (S : Support β) :
    S.strong.Strong := by
  constructor
  · constructor
    intro A N hN P t hA ht
    rw [strong, close_nearLitters] at hN
    apply (S.preStrong_preStrong.support_le hN P t hA ht).trans
    intro B
    exact (S.preStrong_subsupport_strong (P.A ↘ P.hδ ⇘ B)).le
  · exact close_closed _

end Support
end ConNF
