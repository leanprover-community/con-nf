import ConNF.Setup.NearLitter

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

-- TODO: In the blueprint we required `s ⊆ ψᴬ.dom`.
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
  λ N₁ N₂ ↦ ψᴸ N₁ᴸ N₂ᴸ ∧ ψᴬ.image N₁ᴬ = N₂ᴬ

end BaseApprox

end ConNF
