import ConNF.Setup.NearLitter

/-!
# Base actions

In this file, we define base actions.

## Main declarations

* `ConNF.BaseAction`: The type of base actions.
-/

noncomputable section
universe u

open Cardinal Ordinal
open scoped symmDiff

namespace ConNF

variable [Params.{u}]

structure BaseAction where
  atoms : Rel Atom Atom
  nearLitters : Rel NearLitter NearLitter
  atoms_dom_small' : Small atoms.dom
  nearLitters_dom_small' : Small nearLitters.dom
  atoms_oneOne' : atoms.OneOne
  mem_iff_mem' {a₁ a₂ : Atom} {N₁ N₂ : NearLitter} :
    atoms a₁ a₂ → nearLitters N₁ N₂ → (a₁ ∈ N₁ᴬ ↔ a₂ ∈ N₂ᴬ)
  litter_eq_litter_iff' {N₁ N₂ N₃ N₄ : NearLitter} :
    nearLitters N₁ N₃ → nearLitters N₂ N₄ → (N₁ᴸ = N₂ᴸ ↔ N₃ᴸ = N₄ᴸ)
  interference_subset_dom' {N₁ N₂ : NearLitter} :
    N₁ ∈ nearLitters.dom → N₂ ∈ nearLitters.dom → interference N₁ N₂ ⊆ atoms.dom
  interference_subset_codom' {N₁ N₂ : NearLitter} :
    N₁ ∈ nearLitters.codom → N₂ ∈ nearLitters.codom → interference N₁ N₂ ⊆ atoms.codom

namespace BaseAction

instance : SuperA BaseAction (Rel Atom Atom) where
  superA := atoms

instance : SuperN BaseAction (Rel NearLitter NearLitter) where
  superN := nearLitters

theorem atoms_dom_small (ξ : BaseAction) : Small ξᴬ.dom :=
  ξ.atoms_dom_small'

theorem nearLitters_dom_small (ξ : BaseAction) : Small ξᴺ.dom :=
  ξ.nearLitters_dom_small'

theorem atoms_oneOne (ξ : BaseAction) : ξᴬ.OneOne :=
  ξ.atoms_oneOne'

theorem mem_iff_mem {ξ : BaseAction} {a₁ a₂ : Atom} {N₁ N₂ : NearLitter} :
    ξᴬ a₁ a₂ → ξᴺ N₁ N₂ → (a₁ ∈ N₁ᴬ ↔ a₂ ∈ N₂ᴬ) :=
  ξ.mem_iff_mem'

theorem litter_eq_litter_iff {ξ : BaseAction} {N₁ N₂ N₃ N₄ : NearLitter} :
    ξᴺ N₁ N₃ → ξᴺ N₂ N₄ → (N₁ᴸ = N₂ᴸ ↔ N₃ᴸ = N₄ᴸ) :=
  ξ.litter_eq_litter_iff'

theorem interference_subset_dom {ξ : BaseAction} {N₁ N₂ : NearLitter} :
    N₁ ∈ ξᴺ.dom → N₂ ∈ ξᴺ.dom → interference N₁ N₂ ⊆ ξᴬ.dom :=
  ξ.interference_subset_dom'

theorem interference_subset_codom {ξ : BaseAction} {N₁ N₂ : NearLitter} :
    N₁ ∈ ξᴺ.codom → N₂ ∈ ξᴺ.codom → interference N₁ N₂ ⊆ ξᴬ.codom :=
  ξ.interference_subset_codom'

theorem mem_symmDiff_iff_mem_symmDiff {ξ : BaseAction} {a₁ a₂ : Atom} {N₁ N₂ N₃ N₄ : NearLitter} :
    ξᴬ a₁ a₂ → ξᴺ N₁ N₂ → ξᴺ N₃ N₄ → (a₁ ∈ N₁ᴬ ∆ N₃ᴬ ↔ a₂ ∈ N₂ᴬ ∆ N₄ᴬ) := by
  intro ha hN₁₂ hN₃₄
  simp only [Set.mem_symmDiff, mem_iff_mem ha hN₁₂, mem_iff_mem ha hN₃₄]

theorem nearLitters_coinjective (ξ : BaseAction) : ξᴺ.Coinjective := by
  constructor
  intro N₁ N₂ N h₁ h₂
  apply NearLitter.ext
  rw [← Set.symmDiff_eq_empty, Set.eq_empty_iff_forall_not_mem]
  intro a ha
  have := interference_subset_codom ⟨_, h₁⟩ ⟨_, h₂⟩
  rw [interference_eq_of_litter_eq ((litter_eq_litter_iff h₁ h₂).mp rfl)] at this
  obtain ⟨b, hba⟩ := this ha
  rw [← mem_symmDiff_iff_mem_symmDiff hba h₁ h₂] at ha
  simp only [symmDiff_self, Set.bot_eq_empty, Set.mem_empty_iff_false] at ha

theorem atoms_codom_small (ξ : BaseAction) : Small ξᴬ.codom :=
  small_codom_of_small_dom ξ.atoms_oneOne.toCoinjective ξ.atoms_dom_small

theorem nearLitters_codom_small (ξ : BaseAction) : Small ξᴺ.codom :=
  small_codom_of_small_dom ξ.nearLitters_coinjective ξ.nearLitters_dom_small

def inv (ξ : BaseAction) : BaseAction where
  atoms := ξᴬ.inv
  nearLitters := ξᴺ.inv
  atoms_dom_small' := ξ.atoms_codom_small
  nearLitters_dom_small' := ξ.nearLitters_codom_small
  atoms_oneOne' := ξ.atoms_oneOne.inv
  mem_iff_mem' h₁ h₂ := (ξ.mem_iff_mem h₁ h₂).symm
  litter_eq_litter_iff' h₁ h₂ := (ξ.litter_eq_litter_iff h₁ h₂).symm
  interference_subset_dom' := ξ.interference_subset_codom
  interference_subset_codom' := ξ.interference_subset_dom

instance : Inv BaseAction where
  inv := inv

@[simp]
theorem inv_atoms (ξ : BaseAction) : ξ⁻¹ᴬ = ξᴬ.inv :=
  rfl

@[simp]
theorem inv_nearLitters (ξ : BaseAction) : ξ⁻¹ᴺ = ξᴺ.inv :=
  rfl

theorem nearLitters_injective (ξ : BaseAction) : ξᴺ.Injective := by
  have := ξ⁻¹.nearLitters_coinjective
  rwa [inv_nearLitters, Rel.inv_coinjective_iff] at this

theorem nearLitters_oneOne (ξ : BaseAction) : ξᴺ.OneOne :=
  ⟨ξ.nearLitters_injective, ξ.nearLitters_coinjective⟩

inductive litters (ξ : BaseAction) : Rel Litter Litter
  | mk {N₁ N₂ : NearLitter} : ξᴺ N₁ N₂ → ξ.litters N₁ᴸ N₂ᴸ

instance : SuperL BaseAction (Rel Litter Litter) where
  superL := litters

theorem litters_iff {ξ : BaseAction} (L₁ L₂ : Litter) :
    ξᴸ L₁ L₂ ↔ ∃ N₁ N₂, N₁ᴸ = L₁ ∧ N₂ᴸ = L₂ ∧ ξᴺ N₁ N₂ := by
  constructor
  · rintro ⟨⟩
    refine ⟨_, _, rfl, rfl, ?_⟩
    assumption
  · rintro ⟨N₁, N₂, rfl, rfl, h⟩
    exact ⟨h⟩

theorem litters_coinjective (ξ : BaseAction) : ξᴸ.Coinjective := by
  constructor
  intro L₁ L₂ L h₁ h₂
  rw [litters_iff] at h₁ h₂
  obtain ⟨N₃, N₁, h₃, rfl, h₁⟩ := h₁
  obtain ⟨N₄, N₂, h₄, rfl, h₂⟩ := h₂
  exact (litter_eq_litter_iff h₁ h₂).mp (h₃.trans h₄.symm)

@[simp]
theorem inv_litters (ξ : BaseAction) : ξ⁻¹ᴸ = ξᴸ.inv := by
  ext L₁ L₂
  simp only [litters_iff, inv_nearLitters, exists_and_left, Rel.inv_def]
  tauto

theorem litters_injective (ξ : BaseAction) : ξᴸ.Injective := by
  have := ξ⁻¹.litters_coinjective
  rwa [inv_litters, Rel.inv_coinjective_iff] at this

theorem litters_oneOne (ξ : BaseAction) : ξᴸ.OneOne :=
  ⟨ξ.litters_injective, ξ.litters_coinjective⟩

end BaseAction

end ConNF
