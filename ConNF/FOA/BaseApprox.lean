import ConNF.ModelData.Support
import ConNF.FOA.Coherent

/-!
# Base approximations

In this file, we define base approximations.

## Main declarations

* `ConNF.BaseApprox`: A base approximation consists of a partial permutation of atoms and a partial
  permutation of near-litters.
-/

noncomputable section
universe u

open Cardinal Ordinal Rel Set
open scoped symmDiff

namespace ConNF

variable [Params.{u}]

structure BaseApprox where
  exceptions : Rel Atom Atom
  litters : Rel Litter Litter
  exceptions_permutative : exceptions.Permutative
  litters_permutative' : litters.Permutative
  exceptions_small (L : Litter) : Small (Lᴬ ∩ exceptions.dom)

namespace BaseApprox

instance : SuperL BaseApprox (Rel Litter Litter) where
  superL := litters

@[simp]
theorem mk_litters (exceptions : Rel Atom Atom) (litters : Rel Litter Litter)
    (exceptions_permutative : exceptions.Permutative)
    (litters_permutative' : litters.Permutative)
    (exceptions_small : ∀ L, Small (Lᴬ ∩ exceptions.dom)) :
    (BaseApprox.mk exceptions litters exceptions_permutative
      litters_permutative' exceptions_small)ᴸ = litters :=
  rfl

@[ext]
theorem ext {ψ χ : BaseApprox} (h₁ : ψ.exceptions = χ.exceptions) (h₂ : ψᴸ = χᴸ) :
    ψ = χ := by
  cases ψ; cases χ; cases h₁; cases h₂; rfl

theorem litters_permutative (ψ : BaseApprox) :
    ψᴸ.Permutative :=
  ψ.litters_permutative'

instance : Inv BaseApprox where
  inv ψ := {
    exceptions := ψ.exceptions.inv
    litters := ψᴸ.inv
    exceptions_permutative := ψ.exceptions_permutative.inv
    litters_permutative' := ψ.litters_permutative.inv
    exceptions_small := λ L ↦ ψ.exceptions_permutative.inv_dom ▸ ψ.exceptions_small L
  }

@[simp]
theorem inv_exceptions (ψ : BaseApprox) :
    ψ⁻¹.exceptions = ψ.exceptions.inv :=
  rfl

@[simp]
theorem inv_litters (ψ : BaseApprox) :
    ψ⁻¹ᴸ = ψᴸ.inv :=
  rfl

@[simp]
theorem inv_inv (ψ : BaseApprox) :
    ψ⁻¹⁻¹ = ψ :=
  rfl

def sublitterAtoms (ψ : BaseApprox) (L : Litter) : Set Atom :=
  Lᴬ \ ψ.exceptions.dom

theorem sublitterAtoms_near (ψ : BaseApprox) (L : Litter) : ψ.sublitterAtoms L ~ Lᴬ := by
  rw [sublitterAtoms, Near, symmDiff_comm, symmDiff_diff_self]
  exact ψ.exceptions_small L

def sublitter (ψ : BaseApprox) (L : Litter) : NearLitter where
  litter := L
  atoms := ψ.sublitterAtoms L
  atoms_near_litter' := ψ.sublitterAtoms_near L

theorem sublitter_atoms {ψ : BaseApprox} {L : Litter} :
    (ψ.sublitter L)ᴬ = Lᴬ \ ψ.exceptions.dom :=
  rfl

theorem sublitter_subset {ψ : BaseApprox} {L : Litter} :
    (ψ.sublitter L)ᴬ ⊆ Lᴬ :=
  λ {_} ↦ And.left

theorem sublitter_atoms_disjoint {ψ : BaseApprox} {L : Litter} :
    Disjoint (ψ.sublitter L)ᴬ ψ.exceptions.dom :=
  sublitter_atoms ▸ disjoint_sdiff_left

@[simp]
theorem inv_sublitter (ψ : BaseApprox) (L : Litter) :
    ψ⁻¹.sublitter L = ψ.sublitter L := by
  ext a
  rw [sublitter_atoms, sublitter_atoms, inv_exceptions, ψ.exceptions_permutative.inv_dom]

def nearLitterEquiv (N : NearLitter) : κ ≃ Nᴬ :=
  Nonempty.some (Cardinal.eq.mp N.card_atoms.symm)

theorem nearLitterEquiv_injective {N : NearLitter} {i₁ i₂ : κ}
    (h : (nearLitterEquiv N i₁ : Atom) = nearLitterEquiv N i₂) :
    i₁ = i₂ :=
  (nearLitterEquiv N).injective (Subtype.val_injective h)

theorem nearLitterEquiv_congr {N₁ N₂ : NearLitter} {i₁ i₂ : κ}
    (hN : N₁ = N₂) (hi : i₁ = i₂) :
    (nearLitterEquiv N₁ i₁ : Atom) = nearLitterEquiv N₂ i₂ := by
  cases hN
  cases hi
  rfl

theorem nearLitterEquiv_mem (N : NearLitter) (i : κ) :
    (nearLitterEquiv N i : Atom) ∈ Nᴬ :=
  (nearLitterEquiv N i).prop

@[simp]
theorem nearLitterEquiv_litter (ψ : BaseApprox) (L : Litter) (i : κ) :
    (nearLitterEquiv (ψ.sublitter L) i : Atom)ᴸ = L :=
  sublitter_subset (nearLitterEquiv (ψ.sublitter L) i).prop

theorem nearLitterEquiv_not_mem_dom (ψ : BaseApprox) (L : Litter) (i : κ) :
    (nearLitterEquiv (ψ.sublitter L) i : Atom) ∉ ψ.exceptions.dom :=
  (nearLitterEquiv (ψ.sublitter L) i).prop.right

inductive typical (ψ : BaseApprox) : Rel Atom Atom where
  | mk (L₁ L₂ : Litter) (h : ψᴸ L₁ L₂) (i : κ) :
      ψ.typical (nearLitterEquiv (ψ.sublitter L₁) i) (nearLitterEquiv (ψ.sublitter L₂) i)

theorem typical_iff {ψ : BaseApprox} {a₁ a₂ : Atom} :
    ψ.typical a₁ a₂ ↔ ψᴸ a₁ᴸ a₂ᴸ ∧ ∃ i,
      a₁ = nearLitterEquiv (ψ.sublitter a₁ᴸ) i ∧ a₂ = nearLitterEquiv (ψ.sublitter a₂ᴸ) i := by
  constructor
  · rintro ⟨L₁, L₂, h, i⟩
    rw [nearLitterEquiv_litter, nearLitterEquiv_litter]
    exact ⟨h, i, rfl, rfl⟩
  · rintro ⟨h, i, h₁, h₂⟩
    rw [h₁, h₂]
    exact typical.mk a₁ᴸ a₂ᴸ h i

theorem not_mem_dom_of_typical {ψ : BaseApprox} {a₁ a₂ : Atom} (h : ψ.typical a₁ a₂) :
    a₁ ∉ ψ.exceptions.dom := by
  rw [typical_iff] at h
  obtain ⟨-, i, h, -⟩ := h
  have := ψ.nearLitterEquiv_not_mem_dom a₁ᴸ i
  rwa [h]

theorem typical_inv_of_typical {ψ : BaseApprox} {a₁ a₂ : Atom} (h : ψ.typical a₁ a₂) :
    ψ⁻¹.typical a₂ a₁ := by
  rw [typical_iff] at h ⊢
  obtain ⟨h, i, h₁, h₂⟩ := h
  rw [inv_sublitter, inv_sublitter]
  exact ⟨h, i, h₂, h₁⟩

theorem typical_inv_iff_typical {ψ : BaseApprox} {a₁ a₂ : Atom} :
    ψ⁻¹.typical a₂ a₁ ↔ ψ.typical a₁ a₂ :=
  ⟨typical_inv_of_typical, typical_inv_of_typical⟩

@[simp]
theorem inv_typical {ψ : BaseApprox} :
    ψ⁻¹.typical = ψ.typical.inv := by
  ext a₁ a₂
  rw [typical_inv_iff_typical]
  rfl

def atoms (ψ : BaseApprox) : Rel Atom Atom :=
  ψ.exceptions ⊔ ψ.typical

instance : SuperA BaseApprox (Rel Atom Atom) where
  superA := atoms

theorem atoms_def (ψ : BaseApprox) :
    ψᴬ = ψ.exceptions ⊔ ψ.typical :=
  rfl

theorem exceptions_le_atoms (ψ : BaseApprox) :
    ψ.exceptions ≤ ψᴬ :=
  le_sup_left

theorem exceptions_dom_subset_atoms_dom (ψ : BaseApprox) :
    ψ.exceptions.dom ⊆ ψᴬ.dom :=
  Rel.dom_mono ψ.exceptions_le_atoms

theorem mem_dom_atoms_of_litter_mem_dom {ψ : BaseApprox} {a : Atom} (h : aᴸ ∈ ψᴸ.dom) :
    a ∈ ψᴬ.dom := by
  obtain ⟨L, h⟩ := h
  rw [atoms_def, sup_dom]
  by_cases ha : a ∈ ψ.exceptions.dom
  · left
    exact ha
  · right
    use nearLitterEquiv (ψ.sublitter L) ((nearLitterEquiv (ψ.sublitter aᴸ)).symm ⟨a, rfl, ha⟩)
    rw [typical_iff]
    refine ⟨?_, (nearLitterEquiv (ψ.sublitter aᴸ)).symm ⟨a, rfl, ha⟩, ?_, ?_⟩
    · rwa [nearLitterEquiv_litter]
    · rw [Equiv.apply_symm_apply]
    · apply nearLitterEquiv_congr
      · rw [nearLitterEquiv_litter]
      · rfl

@[simp]
theorem inv_atoms (ψ : BaseApprox) :
    ψ⁻¹ᴬ = ψᴬ.inv := by
  rw [atoms_def, atoms_def, inv_exceptions, inv_typical, sup_inv]

theorem typical_injective (ψ : BaseApprox) :
    ψ.typical.Injective := by
  constructor
  intro a₁ a₂ b h₁ h₂
  rw [typical_iff] at h₁ h₂
  obtain ⟨h₁L, i₁, h₁, h₃⟩ := h₁
  obtain ⟨h₂L, i₂, h₂, h₄⟩ := h₂
  cases nearLitterEquiv_injective (h₃.symm.trans h₄)
  rw [ψ.litters_permutative.injective h₁L h₂L] at h₁
  exact h₁.trans h₂.symm

theorem typical_coinjective (ψ : BaseApprox) :
    ψ.typical.Coinjective := by
  have := ψ⁻¹.typical_injective
  rwa [inv_typical, inv_injective_iff] at this

theorem typical_codomEqDom (ψ : BaseApprox) :
    ψ.typical.CodomEqDom := by
  rw [codomEqDom_iff']
  constructor
  · rintro _ _ ⟨L₁, L₂, h, i⟩
    obtain ⟨L₃, h'⟩ := ψ.litters_permutative.mem_dom h
    exact ⟨_, typical.mk L₂ L₃ h' i⟩
  · rintro _ _ ⟨L₁, L₂, h, i⟩
    obtain ⟨L₀, h'⟩ := ψ.litters_permutative.mem_codom h
    exact ⟨_, typical.mk L₀ L₁ h' i⟩

theorem typical_permutative (ψ : BaseApprox) :
    ψ.typical.Permutative :=
  ⟨⟨ψ.typical_injective, ψ.typical_coinjective⟩, ψ.typical_codomEqDom⟩

theorem exceptions_typical_disjoint (ψ : BaseApprox) :
    Disjoint ψ.exceptions.dom ψ.typical.dom := by
  rw [disjoint_iff_forall_ne]
  rintro a ha _ ⟨b, hb⟩ rfl
  exact not_mem_dom_of_typical hb ha

theorem atoms_permutative (ψ : BaseApprox) :
    ψᴬ.Permutative :=
  sup_permutative ψ.exceptions_permutative ψ.typical_permutative ψ.exceptions_typical_disjoint

theorem atoms_image_eq_typical_image (ψ : BaseApprox) {s : Set Atom}
    (hs : Disjoint ψ.exceptions.dom s) :
    ψᴬ.image s = ψ.typical.image s := by
  rw [atoms_def, sup_image, image_empty_of_disjoint_dom hs, empty_union]

theorem typical_image_sublitter (ψ : BaseApprox) {L₁ L₂ : Litter} (h : ψᴸ L₁ L₂) :
    ψ.typical.image (ψ.sublitter L₁)ᴬ = (ψ.sublitter L₂)ᴬ := by
  ext a
  constructor
  · rintro ⟨b, hb, L₁', L₂', hL, i⟩
    cases (sublitter_subset hb).symm.trans (ψ.nearLitterEquiv_litter L₁' i)
    cases ψ.litters_permutative.coinjective h hL
    apply nearLitterEquiv_mem
  · intro ha
    use nearLitterEquiv (ψ.sublitter L₁) ((nearLitterEquiv (ψ.sublitter L₂)).symm ⟨a, ha⟩)
    constructor
    · exact Subtype.coe_prop _
    · convert typical.mk L₁ L₂ h ((nearLitterEquiv (ψ.sublitter L₂)).symm ⟨a, ha⟩) using 1
      rw [Equiv.apply_symm_apply]

theorem image_near_of_near (ψ : BaseApprox) (s : Set Atom)
    {L₁ L₂ : Litter} (hL : ψᴸ L₁ L₂) (hsL : s ~ L₁ᴬ) :
    ψᴬ.image s ~ L₂ᴬ := by
  calc
    ψᴬ.image s
    _ = ψᴬ.image ((s ∆ L₁ᴬ) ∆ L₁ᴬ) := by rw [symmDiff_symmDiff_cancel_right]
    _ = ψᴬ.image (s ∆ L₁ᴬ) ∆ ψᴬ.image L₁ᴬ := by rw [ψ.atoms_permutative.image_symmDiff]
    _ ~ ψᴬ.image L₁ᴬ := near_symmDiff_self_of_small
          (image_small_of_coinjective ψ.atoms_permutative.toCoinjective hsL)
    _ = ψᴬ.image ((ψ.sublitter L₁)ᴬ ∪ (L₁ᴬ ∩ ψ.exceptions.dom)) := by
          rw [sublitter_atoms, diff_union_inter]
    _ = ψᴬ.image (ψ.sublitter L₁)ᴬ ∪ ψᴬ.image (L₁ᴬ ∩ ψ.exceptions.dom) := by rw [Rel.image_union]
    _ ~ ψᴬ.image (ψ.sublitter L₁)ᴬ := near_union_of_small
          (image_small_of_coinjective ψ.atoms_permutative.toCoinjective (ψ.exceptions_small L₁))
    _ = ψ.typical.image (ψ.sublitter L₁)ᴬ :=
          ψ.atoms_image_eq_typical_image sublitter_atoms_disjoint.symm
    _ = (ψ.sublitter L₂)ᴬ := ψ.typical_image_sublitter hL
    _ ~ L₂ᴬ := (ψ.sublitter L₂).atoms_near_litter

def nearLitters (ψ : BaseApprox) : Rel NearLitter NearLitter :=
  λ N₁ N₂ ↦ ψᴸ N₁ᴸ N₂ᴸ ∧ N₁ᴬ ⊆ ψᴬ.dom ∧ ψᴬ.image N₁ᴬ = N₂ᴬ

instance : SuperN BaseApprox (Rel NearLitter NearLitter) where
  superN := nearLitters

theorem nearLitters_def (ψ : BaseApprox) {N₁ N₂ : NearLitter} :
    ψᴺ N₁ N₂ ↔ ψᴸ N₁ᴸ N₂ᴸ ∧ N₁ᴬ ⊆ ψᴬ.dom ∧ ψᴬ.image N₁ᴬ = N₂ᴬ :=
  Iff.rfl

theorem mem_dom_nearLitters {ψ : BaseApprox} {N : NearLitter}
    (hL : Nᴸ ∈ ψᴸ.dom) (ha : ∀ a ∈ Nᴬ \ Nᴸᴬ, a ∈ ψᴬ.dom) :
    N ∈ ψᴺ.dom := by
  obtain ⟨L, hL⟩ := hL
  use ⟨L, ψᴬ.image Nᴬ, ψ.image_near_of_near Nᴬ hL N.atoms_near_litter⟩
  refine ⟨hL, ?_, rfl⟩
  intro a ha'
  by_cases ha'' : a ∈ Nᴸᴬ
  · apply mem_dom_atoms_of_litter_mem_dom
    rw [ha'']
    exact ⟨L, hL⟩
  · exact ha a ⟨ha', ha''⟩

@[simp]
theorem inv_nearLitters (ψ : BaseApprox) : ψ⁻¹ᴺ = ψᴺ.inv := by
  ext N₁ N₂
  rw [inv_def, nearLitters_def, nearLitters_def, inv_litters, inv_def, inv_atoms,
    and_congr_right_iff, inv_image]
  intro
  constructor
  · rintro ⟨h₁, h₂⟩
    have := h₂.symm.trans_subset (ψᴬ.preimage_subset_dom N₁ᴬ)
    exact ⟨this, (ψ.atoms_permutative.preimage_eq_iff_image_eq h₁ this).mp h₂⟩
  · rintro ⟨h₁, h₂⟩
    have := h₂.symm.trans_subset (ψᴬ.image_subset_codom N₂ᴬ)
    exact ⟨this, (ψ.atoms_permutative.preimage_eq_iff_image_eq this h₁).mpr h₂⟩

theorem atoms_subset_dom_of_nearLitters_left {ψ : BaseApprox} {N₁ N₂ : NearLitter} (h : ψᴺ N₁ N₂) :
    N₁ᴬ ⊆ ψᴬ.dom :=
  h.2.1

theorem atoms_subset_dom_of_nearLitters_right {ψ : BaseApprox} {N₁ N₂ : NearLitter} (h : ψᴺ N₁ N₂) :
    N₂ᴬ ⊆ ψᴬ.dom := by
  have := atoms_subset_dom_of_nearLitters_left (show ψ⁻¹ᴺ N₂ N₁ from ψ.inv_nearLitters ▸ h)
  rwa [inv_atoms, inv_dom, ψ.atoms_permutative.codom_eq_dom] at this

theorem nearLitters_injective (ψ : BaseApprox) : ψᴺ.Injective := by
  constructor
  intro N₁ N₂ N₃ h₁ h₂
  rw [nearLitters_def] at h₁ h₂
  apply NearLitter.ext
  apply ψ.atoms_permutative.image_injective h₁.2.1 h₂.2.1
  exact h₁.2.2.trans h₂.2.2.symm

theorem nearLitters_coinjective (ψ : BaseApprox) : ψᴺ.Coinjective := by
  have := ψ⁻¹.nearLitters_injective
  rwa [inv_nearLitters, inv_injective_iff] at this

theorem nearLitters_codom_subset_dom (ψ : BaseApprox) : ψᴺ.codom ⊆ ψᴺ.dom := by
  rintro N₂ ⟨N₁, h⟩
  obtain ⟨L₃, hL₃⟩ := ψ.litters_permutative.mem_dom h.1
  use ⟨L₃, ψᴬ.image N₂ᴬ, ψ.image_near_of_near N₂ᴬ hL₃ N₂.atoms_near_litter⟩
  exact ⟨hL₃, atoms_subset_dom_of_nearLitters_right h, rfl⟩

theorem nearLitters_permutative (ψ : BaseApprox) : ψᴺ.Permutative := by
  refine ⟨⟨ψ.nearLitters_injective, ψ.nearLitters_coinjective⟩,
    ⟨subset_antisymm ψ.nearLitters_codom_subset_dom ?_⟩⟩
  have := ψ⁻¹.nearLitters_codom_subset_dom
  rwa [inv_nearLitters] at this

instance : LE BaseApprox where
  le ψ χ := ψ.exceptions = χ.exceptions ∧ ψᴸ ≤ χᴸ

instance : PartialOrder BaseApprox where
  le_refl ψ := ⟨rfl, le_rfl⟩
  le_trans ψ₁ ψ₂ ψ₃ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm ψ₁ ψ₂ h₁ h₂ := BaseApprox.ext h₁.1 (le_antisymm h₁.2 h₂.2)

theorem litters_le_of_le {ψ χ : BaseApprox} (h : ψ ≤ χ) :
    ψᴸ ≤ χᴸ :=
  h.2

theorem sublitter_eq_of_le {ψ χ : BaseApprox} (h : ψ ≤ χ) (L : Litter) :
    ψ.sublitter L = χ.sublitter L := by
  ext a
  rw [sublitter, sublitter, NearLitter.mk_atoms, NearLitter.mk_atoms,
    sublitterAtoms, sublitterAtoms, h.1]

theorem typical_le_of_le {ψ χ : BaseApprox} (h : ψ ≤ χ) :
    ψ.typical ≤ χ.typical := by
  intro a₁ a₂ hψ
  obtain ⟨L₁, L₂, hψ, i⟩ := hψ
  rw [sublitter_eq_of_le h, sublitter_eq_of_le h]
  exact ⟨L₁, L₂, litters_le_of_le h L₁ L₂ hψ, i⟩

theorem atoms_le_of_le {ψ χ : BaseApprox} (h : ψ ≤ χ) :
    ψᴬ ≤ χᴬ :=
  sup_le_sup h.1.le (typical_le_of_le h)

theorem nearLitters_le_of_le {ψ χ : BaseApprox} (h : ψ ≤ χ) :
    ψᴺ ≤ χᴺ := by
  rintro N₁ N₂ ⟨h₁, h₂, h₃⟩
  refine ⟨litters_le_of_le h N₁ᴸ N₂ᴸ h₁, ?_, ?_⟩
  · exact h₂.trans <| dom_mono <| atoms_le_of_le h
  · rw [← h₃]
    symm
    apply image_eq_of_le_of_le (atoms_le_of_le h)
    intro a₁ ha₁ a₂ ha₂
    obtain ⟨a₃, ha₃⟩ := h₂ ha₁
    cases χ.atoms_permutative.coinjective ha₂ (atoms_le_of_le h a₁ a₃ ha₃)
    exact ha₃

/-- This creates new definitions of `·ᴬ` and `·ᴺ`, but the instances are definitionally equal
so no triangles are formed. -/
instance : BaseActionClass BaseApprox where
  atoms ψ := ψᴬ
  atoms_oneOne ψ := ψ.atoms_permutative.toOneOne
  nearLitters ψ := ψᴺ
  nearLitters_oneOne ψ := ψ.nearLitters_permutative.toOneOne

section addOrbit

def addOrbitLitters (f : ℤ → Litter) :
    Rel Litter Litter :=
  λ L₁ L₂ ↦ ∃ n : ℤ, L₁ = f n ∧ L₂ = f (n + 1)

@[simp]
theorem addOrbitLitters_dom (f : ℤ → Litter) :
    (addOrbitLitters f).dom = Set.range f := by
  ext L
  constructor
  · rintro ⟨_, n, rfl, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨_, n, rfl, rfl⟩

theorem addOrbitLitters_codomEqDom (f : ℤ → Litter) :
    (addOrbitLitters f).CodomEqDom := by
  constructor
  ext L
  constructor
  · rintro ⟨_, n, rfl, rfl⟩
    exact ⟨_, n + 1, rfl, rfl⟩
  · rintro ⟨_, n, rfl, rfl⟩
    refine ⟨_, n - 1, rfl, ?_⟩
    rw [sub_add_cancel]

theorem addOrbitLitters_oneOne (f : ℤ → Litter) (hf : ∀ m n k, f m = f n → f (m + k) = f (n + k)) :
    (addOrbitLitters f).OneOne := by
  constructor
  · constructor
    rintro L₁ L₂ L₃ ⟨m, rfl, rfl⟩ ⟨n, rfl, h⟩
    have := hf (m + 1) (n + 1) (-1) h
    rwa [add_neg_cancel_right, add_neg_cancel_right] at this
  · constructor
    rintro L₁ L₂ L₃ ⟨m, rfl, rfl⟩ ⟨n, h, rfl⟩
    exact hf m n 1 h

theorem addOrbitLitters_permutative (f : ℤ → Litter)
    (hf : ∀ m n k, f m = f n → f (m + k) = f (n + k)) :
    (addOrbitLitters f).Permutative :=
  ⟨addOrbitLitters_oneOne f hf, addOrbitLitters_codomEqDom f⟩

theorem disjoint_litters_dom_addOrbitLitters_dom
    (ψ : BaseApprox) (f : ℤ → Litter) (hfψ : ∀ n, f n ∉ ψᴸ.dom) :
    Disjoint ψᴸ.dom (addOrbitLitters f).dom := by
  rw [Set.disjoint_iff_forall_ne]
  rintro _ h₁ _ ⟨_, n, rfl, rfl⟩ rfl
  exact hfψ n h₁

def addOrbit (ψ : BaseApprox) (f : ℤ → Litter)
    (hf : ∀ m n k, f m = f n → f (m + k) = f (n + k)) (hfψ : ∀ n, f n ∉ ψᴸ.dom) : BaseApprox where
  exceptions := ψ.exceptions
  litters := ψ.litters ⊔ addOrbitLitters f
  exceptions_permutative := ψ.exceptions_permutative
  litters_permutative' :=
    sup_permutative ψ.litters_permutative (addOrbitLitters_permutative f hf)
      (disjoint_litters_dom_addOrbitLitters_dom ψ f hfψ)
  exceptions_small := ψ.exceptions_small

variable {ψ : BaseApprox} {f : ℤ → Litter} {hf : ∀ m n k, f m = f n → f (m + k) = f (n + k)}
  {hfψ : ∀ n, f n ∉ ψᴸ.dom}

theorem addOrbit_litters :
    (ψ.addOrbit f hf hfψ)ᴸ = ψᴸ ⊔ addOrbitLitters f :=
  rfl

theorem le_addOrbit :
    ψ ≤ ψ.addOrbit f hf hfψ :=
  ⟨rfl, le_sup_left⟩

end addOrbit

theorem upperBound_exceptions_small (c : Set BaseApprox) (hc : IsChain (· ≤ ·) c) (L : Litter) :
    Small (Lᴬ ∩ (⨆ ψ ∈ c, ψ.exceptions).dom) := by
  rw [biSup_dom]
  obtain (rfl | ⟨ψ, hψ⟩) := c.eq_empty_or_nonempty
  · simp only [mem_empty_iff_false, iUnion_of_empty, iUnion_empty, inter_empty, small_empty]
  · suffices ⋃ ψ ∈ c, ψ.exceptions.dom = ψ.exceptions.dom by
      rw [this]
      exact ψ.exceptions_small L
    ext a
    rw [mem_iUnion₂]
    constructor
    · rintro ⟨χ, hχ₁, hχ₂⟩
      obtain (h | h) := hc.total hψ hχ₁
      · rwa [h.1]
      · rwa [← h.1]
    · intro h
      exact ⟨ψ, hψ, h⟩

/-- An upper bound for a chain of base approximations. -/
def upperBound (c : Set BaseApprox) (hc : IsChain (· ≤ ·) c) : BaseApprox where
  exceptions := ⨆ ψ ∈ c, ψ.exceptions
  litters := ⨆ ψ ∈ c, ψᴸ
  exceptions_permutative := biSup_permutative_of_isChain
    (λ ψ _ ↦ ψ.exceptions_permutative) (hc.image _ _ _ (λ _ _ h ↦ h.1.le))
  litters_permutative' := biSup_permutative_of_isChain
    (λ ψ _ ↦ ψ.litters_permutative) (hc.image _ _ _ (λ _ _ h ↦ h.2))
  exceptions_small := upperBound_exceptions_small c hc

theorem le_upperBound (c : Set BaseApprox) (hc : IsChain (· ≤ ·) c) :
    ∀ ψ ∈ c, ψ ≤ upperBound c hc := by
  intro ψ hψ
  constructor
  · ext a₁ a₂
    simp only [upperBound, biSup_dom, biSup_apply_iff]
    constructor
    · intro h
      exact ⟨ψ, hψ, h⟩
    · rintro ⟨χ, hχ₁, hχ₂⟩
      obtain (h | h) := hc.total hψ hχ₁
      · rwa [h.1]
      · rwa [← h.1]
  · exact le_biSup _ hψ

def Total (ψ : BaseApprox) : Prop :=
  ∀ L, L ∈ ψᴸ.dom

theorem Total.atoms {ψ : BaseApprox} (h : ψ.Total) (a : Atom) :
    a ∈ ψᴬ.dom := by
  apply ψ.mem_dom_atoms_of_litter_mem_dom
  apply h

theorem Total.nearLitters {ψ : BaseApprox} (h : ψ.Total) (N : NearLitter) :
    N ∈ ψᴺ.dom := by
  apply ψ.mem_dom_nearLitters
  · apply h
  · intros
    apply h.atoms

theorem Total.atoms_bijective {ψ : BaseApprox} (h : ψ.Total) :
    ψᴬ.Bijective := by
  refine ⟨⟨ψ.atoms_permutative.toCoinjective, ?_⟩, ⟨ψ.atoms_permutative.toInjective, ?_⟩⟩
  · constructor
    exact h.atoms
  · constructor
    intro a
    have := h.atoms a
    rwa [← ψ.atoms_permutative.codom_eq_dom] at this

theorem Total.litters_bijective {ψ : BaseApprox} (h : ψ.Total) :
    ψᴸ.Bijective := by
  refine ⟨⟨ψ.litters_permutative.toCoinjective, ?_⟩, ⟨ψ.litters_permutative.toInjective, ?_⟩⟩
  · constructor
    exact h
  · constructor
    intro L
    have := h L
    rwa [← ψ.litters_permutative.codom_eq_dom] at this

theorem basePerm_apply_near_apply (ψ : BaseApprox) (h : ψ.Total) (s : Set Atom) (L : Litter) :
    s ~ Lᴬ → ψᴬ.toEquiv h.atoms_bijective '' s ~ (ψᴸ.toEquiv h.litters_bijective L)ᴬ := by
  intro hs
  rw [toEquiv_image]
  exact image_near_of_near ψ s (ψᴸ.toEquiv_rel h.litters_bijective L) hs

def basePerm (ψ : BaseApprox) (h : ψ.Total) : BasePerm where
  atoms := ψᴬ.toEquiv h.atoms_bijective
  litters := ψᴸ.toEquiv h.litters_bijective
  apply_near_apply := basePerm_apply_near_apply ψ h

theorem basePerm_smul_atom_def {ψ : BaseApprox} {h : ψ.Total} {a : Atom} :
    ψ.basePerm h • a = ψᴬ.toFunction h.atoms_bijective.toFunctional a :=
  rfl

theorem basePerm_smul_litter_def {ψ : BaseApprox} {h : ψ.Total} {L : Litter} :
    ψ.basePerm h • L = ψᴸ.toFunction h.litters_bijective.toFunctional L :=
  rfl

@[simp]
theorem basePerm_smul_atom_eq_iff {ψ : BaseApprox} {h : ψ.Total} {a₁ a₂ : Atom} :
    ψ.basePerm h • a₁ = a₂ ↔ ψᴬ a₁ a₂ := by
  rw [basePerm_smul_atom_def, toFunction_eq_iff]

@[simp]
theorem basePerm_inv_smul_atom_eq_iff {ψ : BaseApprox} {h : ψ.Total} {a₁ a₂ : Atom} :
    (ψ.basePerm h)⁻¹ • a₁ = a₂ ↔ ψᴬ a₂ a₁ := by
  rw [← basePerm_smul_atom_eq_iff (h := h), inv_smul_eq_iff, eq_comm]

@[simp]
theorem basePerm_smul_litter_eq_iff {ψ : BaseApprox} {h : ψ.Total} {L₁ L₂ : Litter} :
    ψ.basePerm h • L₁ = L₂ ↔ ψᴸ L₁ L₂ := by
  rw [basePerm_smul_litter_def, toFunction_eq_iff]

@[simp]
theorem basePerm_inv_smul_litter_eq_iff {ψ : BaseApprox} {h : ψ.Total} {L₁ L₂ : Litter} :
    (ψ.basePerm h)⁻¹ • L₁ = L₂ ↔ ψᴸ L₂ L₁ := by
  rw [← basePerm_smul_litter_eq_iff (h := h), inv_smul_eq_iff, eq_comm]

@[simp]
theorem basePerm_smul_nearLitter_eq_iff {ψ : BaseApprox} {h : ψ.Total} {N₁ N₂ : NearLitter} :
    ψ.basePerm h • N₁ = N₂ ↔ ψᴺ N₁ N₂ := by
  constructor
  · intro hN
    refine ⟨?_, ?_, ?_⟩
    · have := congr_arg (·ᴸ) hN
      dsimp only at this
      rwa [BasePerm.smul_nearLitter_litter, basePerm_smul_litter_eq_iff] at this
    · intro a _
      exact h.atoms a
    · have := congr_arg (·ᴬ) hN
      dsimp only at this
      rw [BasePerm.smul_nearLitter_atoms] at this
      rwa [← toEquiv_image _ h.atoms_bijective]
  · intro hN
    ext : 1
    have := hN.2.2
    rwa [← toEquiv_image _ h.atoms_bijective] at this

structure Approximates (ψ : BaseApprox) (π : BasePerm) : Prop where
  atoms : ∀ a₁ a₂, ψᴬ a₁ a₂ → a₂ = π • a₁
  nearLitters : ∀ N₁ N₂, ψᴺ N₁ N₂ → N₂ = π • N₁

theorem Approximates.litters {ψ : BaseApprox} {π : BasePerm} (h : ψ.Approximates π)
    (L₁ L₂ : Litter) : ψᴸ L₁ L₂ → π • L₁ = L₂ := by
  intro hL
  obtain ⟨N, hN⟩ := ψ.mem_dom_nearLitters (N := L₁ᴺ) ⟨L₂, hL⟩ (λ a h ↦ (h.2 h.1).elim)
  cases h.nearLitters L₁ᴺ N hN
  rw [ψ.litters_permutative.coinjective hL hN.1]
  rfl

theorem Approximates.mono {ψ χ : BaseApprox} {π : BasePerm} (hχ : χ.Approximates π) (h : ψ ≤ χ) :
    ψ.Approximates π := by
  constructor
  · intro a₁ a₂ hψ
    exact hχ.atoms a₁ a₂ (atoms_le_of_le h a₁ a₂ hψ)
  · intro N₁ N₂ hψ
    exact hχ.nearLitters N₁ N₂ (nearLitters_le_of_le h N₁ N₂ hψ)

structure ExactlyApproximates (ψ : BaseApprox) (π : BasePerm) : Prop
    extends ψ.Approximates π where
  smul_litter : ∀ a, a ∉ ψ.exceptions.dom → (π • a)ᴸ = π • aᴸ
  inv_smul_litter : ∀ a, a ∉ ψ.exceptions.dom → (π⁻¹ • a)ᴸ = π⁻¹ • aᴸ

theorem ExactlyApproximates.mono {ψ χ : BaseApprox} {π : BasePerm}
    (hχ : χ.ExactlyApproximates π) (h : ψ ≤ χ) :
    ψ.ExactlyApproximates π := by
  constructor
  · exact hχ.toApproximates.mono h
  · intro a ha
    apply hχ.smul_litter
    rwa [h.1] at ha
  · intro a ha
    apply hχ.inv_smul_litter
    rwa [h.1] at ha

open scoped Pointwise in
theorem ExactlyApproximates.smulSet_nearLitter
    {ψ : BaseApprox} {π : BasePerm} {N₁ N₂ : NearLitter}
    (hψ : ψ.ExactlyApproximates π) (hNπ : π • N₁ᴸ = N₂ᴸ) :
    π • (N₁ᴸᴬ \ ψ.exceptions.dom) = N₂ᴸᴬ \ ψ.exceptions.dom := by
  ext a
  constructor
  · rintro ⟨a, ⟨ha₁, ha₂⟩, rfl⟩
    have := hψ.smul_litter a ha₂
    rw [ha₁, hNπ] at this
    use this
    contrapose! ha₂
    obtain ⟨b, hab⟩ := ψ.exceptions_permutative.codom_eq_dom ▸ ha₂
    have := hψ.atoms b (π • a) (Or.inl hab)
    rw [smul_left_cancel_iff] at this
    cases this
    exact ⟨π • a, hab⟩
  · rintro ⟨ha₁, ha₂⟩
    refine ⟨π⁻¹ • a, ?_, smul_inv_smul π a⟩
    have := hψ.inv_smul_litter a ha₂
    rw [ha₁, eq_inv_smul_iff, ← hNπ, smul_left_cancel_iff] at this
    use this
    contrapose! ha₂
    obtain ⟨b, hab⟩ := ha₂
    have := hψ.atoms (π⁻¹ • a) b (Or.inl hab)
    rw [smul_inv_smul] at this
    cases this
    exact ψ.exceptions_permutative.mem_dom hab

open scoped Pointwise in
theorem Approximates.smulSet_eq_exceptions_image {ψ : BaseApprox} {π : BasePerm}
    (hψ : ψ.Approximates π) (s : Set Atom) (hs : s ⊆ ψ.exceptions.dom) :
    π • s = ψ.exceptions.image s := by
  ext a
  constructor
  · rintro ⟨a, h, rfl⟩
    refine ⟨a, h, ?_⟩
    obtain ⟨b, hb⟩ := hs h
    cases hψ.atoms a b (Or.inl hb)
    exact hb
  · rintro ⟨b, h, hab⟩
    refine ⟨b, h, ?_⟩
    cases hψ.atoms b a (Or.inl hab)
    rfl

theorem approximates_basePerm {ψ : BaseApprox} (h : ψ.Total) :
    ψ.Approximates (ψ.basePerm h) := by
  constructor
  · intro a₁ a₂ ha
    symm
    rwa [basePerm_smul_atom_eq_iff]
  · intro a₁ a₂ ha
    symm
    rwa [basePerm_smul_nearLitter_eq_iff]

theorem exactlyApproximates_basePerm {ψ : BaseApprox} (h : ψ.Total) :
    ψ.ExactlyApproximates (ψ.basePerm h) := by
  refine ⟨approximates_basePerm h, ?_, ?_⟩
  · intro a ha
    have : ψᴬ a (nearLitterEquiv (ψ.sublitter (ψ.basePerm h • aᴸ))
        ((nearLitterEquiv (ψ.sublitter aᴸ)).symm ⟨a, rfl, ha⟩)) := by
      right
      rw [typical_iff]
      refine ⟨?_, (nearLitterEquiv (ψ.sublitter aᴸ)).symm ⟨a, rfl, ha⟩, ?_, ?_⟩
      · simp only [nearLitterEquiv_litter]
        rw [← basePerm_smul_litter_eq_iff]
      · simp only [Equiv.apply_symm_apply]
      · apply nearLitterEquiv_congr
        · simp only [nearLitterEquiv_litter]
        · rfl
    rw [← basePerm_smul_atom_eq_iff (h := h)] at this
    rw [this, nearLitterEquiv_litter]
  · intro a ha
    have : ψᴬ (nearLitterEquiv (ψ.sublitter ((ψ.basePerm h)⁻¹ • aᴸ))
        ((nearLitterEquiv (ψ.sublitter aᴸ)).symm ⟨a, rfl, ha⟩)) a := by
      right
      rw [typical_iff]
      refine ⟨?_, (nearLitterEquiv (ψ.sublitter aᴸ)).symm ⟨a, rfl, ha⟩, ?_, ?_⟩
      · simp only [nearLitterEquiv_litter]
        rw [← basePerm_inv_smul_litter_eq_iff]
      · apply nearLitterEquiv_congr
        · simp only [nearLitterEquiv_litter]
        · rfl
      · simp only [Equiv.apply_symm_apply]
    rw [← basePerm_inv_smul_atom_eq_iff (h := h)] at this
    rw [this, nearLitterEquiv_litter]

end BaseApprox

end ConNF
