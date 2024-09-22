import ConNF.Aux.PermutativeExtension
import ConNF.FOA.BaseAction
import ConNF.FOA.StrApprox

/-!
# Flexible approximations

In this file, we define flexible approximations.

## Main declarations

* `ConNF.FlexApprox`: Flexible approximations.
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
    exact aleph0_lt_κ.le.trans κ_le_μ
  refine (mk_compl_of_infinite _ ?_).trans card_litter
  rw [card_litter]
  apply (mk_union_le _ _).trans_lt
  apply add_lt_of_lt (aleph0_lt_κ.le.trans κ_le_μ)
  · exact ξ.litters_dom_small.trans κ_lt_μ
  · exact ξ.litters_codom_small.trans κ_lt_μ

theorem litter_dom_compl_infinite {ξ : BaseAction} : (ξᴸ.dom ∪ ξᴸ.codom)ᶜ.Infinite := by
  rw [← Set.infinite_coe_iff, infinite_iff, card_litter_dom_compl]
  exact aleph0_lt_κ.le.trans κ_le_μ

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

/-- TODO: Move this to `PermutativeExtension` and do it abstractly. -/
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

theorem le_atomPerm (ξ : BaseAction) :
    ξᴬ ≤ ξ.atomPerm :=
  ξᴬ.le_permutativeExtension _

theorem dom_subset_dom_atomPerm (ξ : BaseAction) :
    ξᴬ.dom ⊆ ξ.atomPerm.dom :=
  Rel.dom_mono ξ.le_atomPerm

theorem codom_subset_codom_atomPerm (ξ : BaseAction) :
    ξᴬ.codom ⊆ ξ.atomPerm.codom := by
  rintro b ⟨a, h⟩
  exact ⟨a, ξ.le_atomPerm a b h⟩

theorem atomPerm_permutative (ξ : BaseAction) :
    ξ.atomPerm.Permutative :=
  ξᴬ.permutativeExtension_permutative _ ξ.atoms_oneOne

theorem litter_of_atomPerm {ξ : BaseAction} {a₁ a₂ : Atom} :
    ξ.atomPerm a₁ a₂ → ξᴬ a₁ a₂ ∨ (a₁ ∉ ξᴬ.dom ∧ a₂ ∉ ξᴬ.codom ∧ a₂ᴸ = ξ.litterPerm a₁ᴸ) :=
  ξᴬ.categorise_permutativeExtension_of_oneOne _ ξ.atoms_oneOne

theorem atomPerm_dom_subset (ξ : BaseAction) :
    ξ.atomPerm.dom ⊆ ξᴬ.dom ∪ ξᴬ.codom ∪ ξ.insideAll := by
  apply (ξᴬ.dom_permutativeExtension_subset _).trans
  dsimp only [orbitRestriction]
  rw [Set.union_diff_self]

theorem atomPerm_small (ξ : BaseAction) :
    Small ξ.atomPerm.dom := by
  apply (ξᴬ.card_permutativeExtension _ ξ.atoms_oneOne.toCoinjective).trans_lt
  rw [max_lt_iff]
  constructor
  · exact aleph0_lt_κ
  · exact ξ.atoms_dom_small

theorem atomPerm_mem_iff_mem {ξ : BaseAction} (hξ : ξ.Nice) {a₁ a₂ : Atom} {N₁ N₂ : NearLitter}
    (ha : ξ.atomPerm a₁ a₂) (hN : ξᴺ N₁ N₂) :
    a₁ ∈ N₁ᴬ ↔ a₂ ∈ N₂ᴬ := by
  obtain (ha | ⟨ha₁, ha₂, haL⟩) := litter_of_atomPerm ha
  · exact ξ.mem_iff_mem ha hN
  · have := litterPerm_eq (BaseAction.litters.mk hN)
    rw [hξ.mem_litter_dom_iff ⟨N₂, hN⟩ ha₁, hξ.mem_litter_codom_iff ⟨N₁, hN⟩ ha₂, haL, ← this,
      Equiv.apply_eq_iff_eq]

theorem atomPerm_mem_iff {ξ : BaseAction} (hξ : ξ.Nice)
    {N₁ N₂ : NearLitter} (hN : ξᴺ N₁ N₂) (a₂ : Atom) :
    a₂ ∈ N₂ᴬ ↔ (∃ a₁ ∈ N₁ᴬ, ξ.atomPerm a₁ a₂) ∨ a₂ ∉ ξ.atomPerm.dom ∧ a₂ᴸ = N₂ᴸ := by
  constructor
  · by_contra! h
    obtain ⟨h₁, h₂, h₃⟩ := h
    have h : a₂ ∈ ξ.atomPerm.codom := by
      by_contra h
      rw [hξ.mem_litter_codom_iff ⟨N₁, hN⟩ (λ h' ↦ h (ξ.codom_subset_codom_atomPerm h'))] at h₁
      rw [ξ.atomPerm_permutative.codom_eq_dom] at h
      exact h₃ h h₁
    obtain ⟨a₁, h⟩ := h
    refine h₂ a₁ ?_ h
    rwa [atomPerm_mem_iff_mem hξ h hN]
  · rintro (⟨a₁, ha⟩ | ⟨ha₂, hN₂⟩)
    · rw [atomPerm_mem_iff_mem hξ ha.2 hN] at ha
      exact ha.1
    · rwa [hξ.mem_litter_codom_iff ⟨N₁, hN⟩]
      intro h
      apply ha₂
      rw [← ξ.atomPerm_permutative.codom_eq_dom]
      exact ξ.codom_subset_codom_atomPerm h

variable [Level] [CoherentData] {β : TypeIndex} [LeLevel β] {A : β ↝ ⊥} {ξ : BaseAction}

def flexLitterRel (ξ : BaseAction) (A : β ↝ ⊥) : Rel Litter Litter :=
  ξᴸ ⊓ (λ L₁ L₂ ↦ ¬Inflexible A L₁ ∧ ¬Inflexible A L₂)

theorem flexLitterRel_dom_small (ξ : BaseAction) (A : β ↝ ⊥) :
    Small (ξ.flexLitterRel A).dom :=
  ξ.litters_dom_small.mono <| Rel.inf_dom.trans Set.inter_subset_left

theorem card_inflexible (A : β ↝ ⊥) :
    #{L | ¬Inflexible A L} = #μ := by
  apply le_antisymm
  · apply (mk_subtype_le _).trans
    rw [card_litter]
  · refine mk_le_of_injective (f := λ ν ↦ ⟨⟨ν, ⊥, α, WithBot.bot_ne_coe⟩, ?_⟩) ?_
    · rintro ⟨P, t, rfl, h⟩
      exact (P.hε.trans_le (P.A.le.trans LeLevel.elim)).ne
        (congr_arg WithBot.some (congr_arg Litter.γ h).symm)
    · intro ν₁ ν₂ h
      cases h
      rfl

theorem card_inflexible_diff_dom (ξ : BaseAction) (A : β ↝ ⊥) :
    #({L | ¬Inflexible A L} \ (ξᴸ.dom ∪ ξᴸ.codom) : Set Litter) = #μ := by
  apply le_antisymm
  · apply (mk_subtype_le _).trans
    rw [card_litter]
  · by_contra! h
    apply (le_mk_diff_add_mk {L | ¬Inflexible A L} (ξᴸ.dom ∪ ξᴸ.codom)).not_lt
    rw [card_inflexible]
    apply add_lt_of_lt (aleph0_lt_κ.le.trans κ_le_μ) h
    apply (mk_union_le _ _).trans_lt
    apply add_lt_of_lt (aleph0_lt_κ.le.trans κ_le_μ)
    · exact ξ.litters_dom_small.trans κ_lt_μ
    · exact ξ.litters_codom_small.trans κ_lt_μ

def flexLitterPerm (ξ : BaseAction) (A : β ↝ ⊥) : Rel Litter Litter :=
  (ξ.flexLitterRel A).permutativeExtension' (ξ.litters_oneOne.mono inf_le_left)
    ({L | ¬Inflexible A L} \ (ξᴸ.dom ∪ ξᴸ.codom))
    (by
      rw [← Set.infinite_coe_iff, infinite_iff, card_inflexible_diff_dom]
      exact aleph0_lt_κ.le.trans κ_le_μ)
    ((ξ.flexLitterRel_dom_small A).le.trans (κ_le_μ.trans_eq (ξ.card_inflexible_diff_dom A).symm))
    (by
      rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_not_mem]
      rintro L₁ ⟨⟨L₂, h₁⟩ | ⟨L₂, h₁⟩, h₂⟩
      · exact h₂.2 (Or.inl ⟨L₂, h₁.1⟩)
      · exact h₂.2 (Or.inr ⟨L₂, h₁.1⟩))

theorem le_flexLitterPerm (ξ : BaseAction) (A : β ↝ ⊥) :
    ξ.flexLitterRel A ≤ ξ.flexLitterPerm A :=
  Rel.le_permutativeExtension'

theorem flexLitterPerm_permutative (ξ : BaseAction) (A : β ↝ ⊥) :
    (ξ.flexLitterPerm A).Permutative :=
  Rel.permutativeExtension'_permutative

theorem dom_flexLitterPerm_subset (ξ : BaseAction) (A : β ↝ ⊥) :
    (ξ.flexLitterPerm A).dom ⊆ {L | ¬Inflexible A L} := by
  apply Rel.dom_permutativeExtension'_subset.trans
  rw [Set.union_subset_iff, Set.union_subset_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro L₁ ⟨L₂, h⟩
    exact h.2.1
  · rintro L₁ ⟨L₂, h⟩
    exact h.2.2
  · exact Set.diff_subset

def flexApprox (ξ : BaseAction) (A : β ↝ ⊥) : BaseApprox where
  exceptions := ξ.atomPerm
  litters := ξ.flexLitterPerm A
  exceptions_permutative := ξ.atomPerm_permutative
  litters_permutative' := ξ.flexLitterPerm_permutative A
  exceptions_small := λ _ ↦ ξ.atomPerm_small.mono Set.inter_subset_right

def MapFlexible (ξ : BaseAction) (A : β ↝ ⊥) : Prop :=
  ∀ {L₁ L₂}, ξᴸ L₁ L₂ → (Inflexible A L₁ ↔ Inflexible A L₂)

theorem flexApprox_flexApprox {ξ : BaseAction} {A : β ↝ ⊥} (hξ₁ : ξ.MapFlexible A) (hξ₂ : ξ.Nice) :
    ξ.FlexApprox A (ξ.flexApprox A) where
  atoms_le_atoms := ξ.le_atomPerm
  flexible_of_mem_dom h := ξ.dom_flexLitterPerm_subset A h
  litters_of_flexible h₁ h₂ := ξ.le_flexLitterPerm A _ _ ⟨h₂, h₁, by rwa [hξ₁ h₂] at h₁⟩
  symmDiff_subset_dom h := (hξ₂.symmDiff_subset_dom _ h).trans
    (ξ.dom_subset_dom_atomPerm.trans (Rel.dom_mono le_sup_left))
  symmDiff_subset_codom h := (hξ₂.symmDiff_subset_codom _ h).trans
    (ξ.codom_subset_codom_atomPerm.trans (Rel.dom_mono le_sup_left))
  mem_iff_mem {N₁ N₂} h := atomPerm_mem_iff hξ₂ h

end FlexApprox

end BaseAction
end ConNF
