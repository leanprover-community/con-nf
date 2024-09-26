import Mathlib.Logic.Equiv.Defs
import ConNF.Setup.NearLitter

/-!
# Base permutations

In this file, we define the group of base permutations, and their actions on atoms, litters, and
near-litters.

## Main declarations

* `ConNF.BasePerm`: The type of base permutations.
-/

universe u

open Cardinal Equiv
open scoped Pointwise

namespace ConNF

variable [Params.{u}]

structure BasePerm where
  atoms : Perm Atom
  litters : Perm Litter
  apply_near_apply (s : Set Atom) (L : Litter) : s ~ Lᴬ → atoms '' s ~ (litters L)ᴬ

namespace BasePerm

instance : SuperA BasePerm (Perm Atom) where
  superA := atoms

instance : SuperL BasePerm (Perm Litter) where
  superL := litters

instance : SMul BasePerm Atom where
  smul π a := πᴬ a

instance : SMul BasePerm Litter where
  smul π L := πᴸ L

theorem smul_near_smul (π : BasePerm) (s : Set Atom) (L : Litter) :
    s ~ Lᴬ → π • s ~ (π • L)ᴬ :=
  π.apply_near_apply s L

instance : SMul BasePerm NearLitter where
  smul π N := ⟨π • Nᴸ, π • Nᴬ, π.smul_near_smul Nᴬ Nᴸ N.atoms_near_litter⟩

theorem smul_atom_def (π : BasePerm) (a : Atom) :
    π • a = πᴬ a :=
  rfl

theorem smul_litter_def (π : BasePerm) (L : Litter) :
    π • L = πᴸ L :=
  rfl

@[simp]
theorem smul_nearLitter_atoms (π : BasePerm) (N : NearLitter) :
    (π • N)ᴬ = π • Nᴬ :=
  rfl

@[simp]
theorem smul_nearLitter_litter (π : BasePerm) (N : NearLitter) :
    (π • N)ᴸ = π • Nᴸ :=
  rfl

@[ext]
theorem ext {π₁ π₂ : BasePerm} (h : ∀ a : Atom, π₁ • a = π₂ • a) :
    π₁ = π₂ := by
  obtain ⟨πa₁, πl₁, h₁⟩ := π₁
  obtain ⟨πa₂, πl₂, h₂⟩ := π₂
  rw [mk.injEq]
  have : πa₁ = πa₂ := by ext a; exact h a
  refine ⟨this, ?_⟩
  ext L
  have h₁' := h₁ Lᴬ L near_rfl
  have h₂' := h₂ Lᴬ L near_rfl
  rw [this] at h₁'
  exact litter_eq_of_near <| near_trans (near_symm h₁') h₂'

instance : One BasePerm where
  one := ⟨1, 1, λ s L h ↦ by simpa only [Perm.coe_one, id_eq, Set.image_id']⟩

@[simp]
theorem one_atom :
    (1 : BasePerm)ᴬ = 1 :=
  rfl

@[simp]
theorem one_litter :
    (1 : BasePerm)ᴸ = 1 :=
  rfl

instance : Mul BasePerm where
  mul π₁ π₂ := ⟨π₁ᴬ * π₂ᴬ, π₁ᴸ * π₂ᴸ, λ s L h ↦ by
    have := π₁.smul_near_smul _ _ <| π₂.smul_near_smul s L h
    simpa only [Set.smul_set_def, Set.image_image] using this⟩

@[simp]
theorem mul_atom (π₁ π₂ : BasePerm) :
    (π₁ * π₂)ᴬ = π₁ᴬ * π₂ᴬ :=
  rfl

@[simp]
theorem mul_litter (π₁ π₂ : BasePerm) :
    (π₁ * π₂)ᴸ = π₁ᴸ * π₂ᴸ :=
  rfl

theorem inv_smul_near_inv_smul (π : BasePerm) (s : Set Atom) (L : Litter) :
    s ~ Lᴬ → πᴬ⁻¹ • s ~ (πᴸ⁻¹ • L)ᴬ := by
  intro h
  apply near_trans (near_image h ↑πᴬ⁻¹)
  have := π.smul_near_smul (πᴸ⁻¹ L)ᴬ (πᴸ⁻¹ L) near_rfl
  have := near_image this ↑πᴬ⁻¹
  simp only [smul_litter_def, smul_atom_def, Perm.apply_inv_self, Set.smul_set_def,
    Perm.image_inv, preimage_image] at this
  rw [Perm.image_inv]
  exact near_symm this

instance : Inv BasePerm where
  inv π := ⟨πᴬ⁻¹, πᴸ⁻¹, π.inv_smul_near_inv_smul⟩

@[simp]
theorem inv_atom (π : BasePerm) :
    π⁻¹ᴬ = πᴬ⁻¹ :=
  rfl

@[simp]
theorem inv_litter (π : BasePerm) :
    π⁻¹ᴸ = πᴸ⁻¹ :=
  rfl

instance : Group BasePerm where
  mul_assoc π₁ π₂ π₃ := by
    ext a
    simp only [smul_atom_def, mul_atom, mul_assoc]
  one_mul π := by
    ext a
    simp only [smul_atom_def, mul_atom, one_atom, one_mul]
  mul_one π := by
    ext a
    simp only [smul_atom_def, mul_atom, one_atom, mul_one]
  inv_mul_cancel π := by
    ext a
    simp only [smul_atom_def, mul_atom, inv_atom, inv_mul_cancel, Perm.coe_one, id_eq, one_atom]

instance : MulAction BasePerm Atom where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance : MulAction BasePerm Litter where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance : MulAction BasePerm NearLitter where
  one_smul N := by
    ext a
    simp only [smul_nearLitter_atoms, one_smul]
  mul_smul π₁ π₂ N := by
    ext a
    simp only [smul_nearLitter_atoms, mul_smul]

@[simp]
theorem smul_interference (π : BasePerm) (N₁ N₂ : NearLitter) :
    π • interference N₁ N₂ = interference (π • N₁) (π • N₂) := by
  by_cases h : N₁ᴸ = N₂ᴸ
  · rw [interference_eq_of_litter_eq h, interference_eq_of_litter_eq,
      Set.smul_set_symmDiff, smul_nearLitter_atoms, smul_nearLitter_atoms]
    rwa [smul_nearLitter_litter, smul_nearLitter_litter, smul_left_cancel_iff]
  · rw [interference_eq_of_litter_ne h, interference_eq_of_litter_ne,
      Set.smul_set_inter, smul_nearLitter_atoms, smul_nearLitter_atoms]
    rwa [smul_nearLitter_litter, smul_nearLitter_litter, ne_eq, smul_left_cancel_iff]

end BasePerm

end ConNF
