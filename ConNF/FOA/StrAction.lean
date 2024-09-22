import ConNF.Aux.PermutativeExtension
import ConNF.FOA.StrApprox
import ConNF.FOA.BaseAction

/-!
# Structural actions

In this file, we define structural actions.

## Main declarations

* `ConNF.StrAction`: Structural actions.
-/

noncomputable section
universe u

open Cardinal Ordinal
open scoped symmDiff

namespace ConNF
namespace BaseAction

variable [Params.{u}]

structure FlexApprox [Level] [CoherentData] {β : TypeIndex} [LeLevel β]
    (A : β ↝ ⊥) (ξ : BaseAction) (ψ : BaseApprox) : Prop where
  atoms_le_atoms : ξᴬ ≤ ψ.exceptions
  flexible_of_mem_dom {L : Litter} : L ∈ ψᴸ.dom → ¬Inflexible A L
  litters_of_flexible {L₁ L₂ : Litter} : ¬Inflexible A L₁ → ξᴸ L₁ L₂ → ψᴸ L₁ L₂
  symmDiff_subset_dom {N : NearLitter} : N ∈ ξᴺ.dom → Nᴬ ∆ Nᴸᴬ ⊆ ψᴬ.dom
  symmDiff_subset_codom {N : NearLitter} : N ∈ ξᴺ.codom → Nᴬ ∆ Nᴸᴬ ⊆ ψᴬ.codom
  mem_iff_mem {N₁ N₂ : NearLitter} : ξᴺ N₁ N₂ → ∀ a₂,
    a₂ ∈ N₂ᴬ ↔ (∃ a₁ ∈ N₁ᴬ, ψ.exceptions a₁ a₂) ∨ (a₂ ∉ ψ.exceptions.dom ∧ a₂ᴸ = N₂ᴸ)

section FlexApprox

theorem card_litter_dom_compl {ξ : BaseAction} : #((ξᴸ.dom ∪ ξᴸ.codom)ᶜ : Set Litter) = #μ := by
  have : Infinite Litter := by
    rw [infinite_iff, card_litter]
    exact aleph0_le_of_isSuccLimit μ_isStrongLimit.isSuccLimit
  refine (mk_compl_of_infinite _ ?_).trans card_litter
  rw [card_litter]
  apply (mk_union_le _ _).trans_lt
  apply add_lt_of_lt (aleph0_le_of_isSuccLimit μ_isStrongLimit.isSuccLimit)
  · exact ξ.litters_dom_small.trans κ_lt_μ
  · exact ξ.litters_codom_small.trans κ_lt_μ

theorem litter_dom_compl_infinite {ξ : BaseAction} : (ξᴸ.dom ∪ ξᴸ.codom)ᶜ.Infinite := by
  rw [← Set.infinite_coe_iff, infinite_iff, card_litter_dom_compl]
  exact aleph0_le_of_isSuccLimit μ_isStrongLimit.isSuccLimit

def littersExtension' (ξ : BaseAction) : Rel Litter Litter :=
  ξᴸ.permutativeExtension' ξ.litters_oneOne (ξᴸ.dom ∪ ξᴸ.codom)ᶜ litter_dom_compl_infinite
    (ξ.litters_dom_small.le.trans (κ_le_μ.trans card_litter_dom_compl.symm.le))
    disjoint_compl_right

theorem le_littersExtension' (ξ : BaseAction) :
    ξᴸ ≤ ξ.littersExtension' :=
  Rel.le_permutativeExtension'

theorem littersExtension'_permutative (ξ : BaseAction) :
    ξ.littersExtension'.Permutative :=
  Rel.permutativeExtension'_permutative

def littersExtension (ξ : BaseAction) : Rel Litter Litter :=
  ξ.littersExtension' ⊔ (λ L₁ L₂ ↦ L₁ = L₂ ∧ L₁ ∉ ξ.littersExtension'.dom)

theorem le_littersExtension (ξ : BaseAction) :
    ξᴸ ≤ ξ.littersExtension :=
  ξ.le_littersExtension'.trans le_sup_left

theorem littersExtension_bijective (ξ : BaseAction) :
    ξ.littersExtension.Bijective := by
  constructor <;> constructor <;> constructor
  · rintro L₁ L₂ L₃ (h | ⟨rfl, h⟩) (h' | ⟨rfl, h'⟩)
    · exact ξ.littersExtension'_permutative.coinjective h h'
    · cases h' ⟨L₁, h⟩
    · cases h ⟨L₂, h'⟩
    · rfl
  · intro L
    by_cases h : L ∈ ξ.littersExtension'.dom
    · obtain ⟨L', h⟩ := h
      exact ⟨L', Or.inl h⟩
    · exact ⟨L, Or.inr ⟨rfl, h⟩⟩
  · rintro L₁ L₂ L₃ (h | ⟨rfl, h⟩) (h' | ⟨rfl, h'⟩)
    · exact ξ.littersExtension'_permutative.injective h h'
    · cases h' (ξ.littersExtension'_permutative.mem_dom h)
    · cases h (ξ.littersExtension'_permutative.mem_dom h')
    · rfl
  · intro L
    by_cases h : L ∈ ξ.littersExtension'.dom
    · obtain ⟨L', h⟩ := ξ.littersExtension'_permutative.codom_eq_dom ▸ h
      exact ⟨L', Or.inl h⟩
    · exact ⟨L, Or.inr ⟨rfl, h⟩⟩

def litterPerm (ξ : BaseAction) : Equiv.Perm Litter :=
  ξ.littersExtension.toEquiv ξ.littersExtension_bijective

theorem litterPerm_eq {ξ : BaseAction} {L₁ L₂ : Litter} (h : ξᴸ L₁ L₂) :
    ξ.litterPerm L₁ = L₂ := by
  apply (ξ.littersExtension.toEquiv_eq_iff ξ.littersExtension_bijective L₁ L₂).mpr
  apply le_littersExtension
  exact h

def insideAll (ξ : BaseAction) : Set Atom :=
  {a | ∀ N, (N ∈ ξᴺ.dom ∨ N ∈ ξᴺ.codom) → Nᴸ = aᴸ → a ∈ Nᴬ}

theorem diff_insideAll_small (ξ : BaseAction) (L : Litter) :
    Small (Lᴬ \ ξ.insideAll) := by
  have : Lᴬ \ ξ.insideAll ⊆ (⋃ N ∈ {N | (N ∈ ξᴺ.dom ∨ N ∈ ξᴺ.codom) ∧ Nᴸ = L}, Lᴬ \ Nᴬ) := by
    rintro a ⟨rfl, ha⟩
    rw [insideAll, Set.mem_setOf_eq] at ha
    push_neg at ha
    obtain ⟨N, hN, h₁, h₂⟩ := ha
    exact Set.mem_biUnion (x := N) ⟨hN, h₁⟩ ⟨rfl, h₂⟩
  apply Small.mono this
  apply small_biUnion
  · apply (small_union ξ.nearLitters_dom_small ξ.nearLitters_codom_small).mono
    exact Set.sep_subset _ _
  · rintro N ⟨_, rfl⟩
    exact N.diff_small'

theorem card_insideAll_inter (ξ : BaseAction) (L : Litter) :
    #(ξ.insideAll \ (ξᴬ.dom ∪ ξᴬ.codom) ∩ Lᴬ : Set Atom) = #κ := by
  apply le_antisymm
  · refine le_of_le_of_eq ?_ L.card_atoms
    apply mk_le_mk_of_subset
    exact Set.inter_subset_right
  · rw [← not_lt]
    intro h
    apply L.atoms_not_small
    apply (small_union (small_union (small_union h (ξ.diff_insideAll_small L))
      ξ.atoms_dom_small) ξ.atoms_codom_small).mono
    intro a ha
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff, not_or, mem_litter_atoms_iff]
    tauto

def orbitRestriction (ξ : BaseAction) : Rel.OrbitRestriction (ξᴬ.dom ∪ ξᴬ.codom) Litter where
  sandbox := ξ.insideAll \ (ξᴬ.dom ∪ ξᴬ.codom)
  sandbox_disjoint := Set.disjoint_sdiff_left.symm
  categorise a := aᴸ
  catPerm := ξ.litterPerm
  le_card_categorise L := by
    change _ ≤ #(ξ.insideAll \ (ξᴬ.dom ∪ ξᴬ.codom) ∩ Lᴬ : Set Atom)
    rw [card_insideAll_inter, max_le_iff]
    constructor
    · exact κ_isRegular.aleph0_le
    · apply (mk_union_le _ _).trans
      apply add_le_of_le κ_isRegular.aleph0_le
      · exact ξ.atoms_dom_small.le
      · exact ξ.atoms_codom_small.le

def atomPerm (ξ : BaseAction) : Rel Atom Atom :=
  ξᴬ.permutativeExtension ξ.orbitRestriction

variable [Level] [CoherentData] {β : TypeIndex} [LeLevel β] {A : β ↝ ⊥} {ξ : BaseAction}

end FlexApprox

end BaseAction
end ConNF
