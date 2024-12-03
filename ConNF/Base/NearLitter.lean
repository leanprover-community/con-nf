import ConNF.Base.Atom

/-!
# Near-litters

In this file, we define near-litters.

## Main declarations

* `ConNF.NearLitter`: The type of near-litters.
* `ConNF.card_nearLitter`: There are precisely `μ` near-litters.
* `ConNF.Interference`: The interference of two near-litters, which is equal to their symmetric
    difference if the two near-litters are near, and equal to their intersection if they are not.
-/

universe u

open Cardinal Set
open scoped symmDiff

namespace ConNF

variable [Params.{u}]

structure NearLitter where
  litter : Litter
  atoms : Set Atom
  atoms_near_litter' : atoms ~ litterᴬ

variable {N₁ N₂ : NearLitter}

instance : SuperL NearLitter Litter where
  superL N := N.litter

instance : SuperA NearLitter (Set Atom) where
  superA N := N.atoms

instance : SuperN Litter NearLitter where
  superN L := ⟨L, Lᴬ, near_rfl⟩

@[simp]
theorem NearLitter.mk_litter (L : Litter) (s : Set Atom) (h : s ~ Lᴬ) :
    (⟨L, s, h⟩ : NearLitter)ᴸ = L :=
  rfl

@[simp]
theorem NearLitter.mk_atoms (L : Litter) (s : Set Atom) (h : s ~ Lᴬ) :
    (⟨L, s, h⟩ : NearLitter)ᴬ = s :=
  rfl

theorem NearLitter.atoms_near_litter (N : NearLitter) :
    Nᴬ ~ Nᴸᴬ :=
  N.atoms_near_litter'

theorem NearLitter.symmDiff_small (N : NearLitter) :
    Small (Nᴬ ∆ Nᴸᴬ) :=
  N.atoms_near_litter

theorem NearLitter.diff_small (N : NearLitter) :
    Small (Nᴬ \ Nᴸᴬ) :=
  N.atoms_near_litter.mono (λ _ ↦ Or.inl)

theorem NearLitter.diff_small' (N : NearLitter) :
    Small (Nᴸᴬ \ Nᴬ) :=
  N.atoms_near_litter.mono (λ _ ↦ Or.inr)

theorem NearLitter.card_atoms (N : NearLitter) :
    #Nᴬ = #κ :=
  (card_eq_of_near N.atoms_near_litter Nᴸ.card_atoms.not_lt).trans Nᴸ.card_atoms

theorem NearLitter.atoms_not_small (N : NearLitter) :
    ¬Small Nᴬ :=
  N.card_atoms.not_lt

theorem nearLitter_litter_eq_of_near (h : N₁ᴬ ~ N₂ᴬ) :
    N₁ᴸ = N₂ᴸ :=
  litter_eq_of_near <|
    near_trans (near_trans (near_symm N₁.atoms_near_litter) h) N₂.atoms_near_litter

theorem near_of_litter_eq (h : N₁ᴸ = N₂ᴸ) :
    N₁ᴬ ~ N₂ᴬ :=
  near_trans N₁.atoms_near_litter (h ▸ near_symm N₂.atoms_near_litter)

@[simp]
theorem nearLitter_near_iff (N₁ N₂ : NearLitter) :
    N₁ᴬ ~ N₂ᴬ ↔ N₁ᴸ = N₂ᴸ :=
  ⟨nearLitter_litter_eq_of_near, near_of_litter_eq⟩

@[ext]
theorem NearLitter.ext (h : N₁ᴬ = N₂ᴬ) :
    N₁ = N₂ := by
  obtain ⟨L₁, s₁, h₁⟩ := N₁
  obtain ⟨L₂, s₂, h₂⟩ := N₂
  cases nearLitter_litter_eq_of_near (near_of_eq h)
  subst h
  rfl

theorem card_near_litter (L : Litter) : #{s | s ~ Lᴬ} = #μ :=
  card_near_eq Lᴬ card_atom

def nearLitterEquiv : NearLitter ≃ (L : Litter) × {s | s ~ Lᴬ} where
  toFun N := ⟨Nᴸ, Nᴬ, N.atoms_near_litter⟩
  invFun N := ⟨N.1, N.2.1, N.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem card_nearLitter : #NearLitter = #μ := by
  simp only [Cardinal.eq.mpr ⟨nearLitterEquiv⟩, mk_sigma, card_near_litter, sum_const, card_litter,
    lift_id, mul_mk_eq_max, max_self]

/-!
## Interference of near-litters
-/

theorem litter_eq_iff_symmDiff_small (N₁ N₂ : NearLitter) : N₁ᴸ = N₂ᴸ ↔ Small (N₁ᴬ ∆ N₂ᴬ) :=
  (nearLitter_near_iff N₁ N₂).symm

theorem litter_ne_of_inter_small (h : Small (N₁ᴬ ∩ N₂ᴬ)) : N₁ᴸ ≠ N₂ᴸ := by
  intro h'
  rw [litter_eq_iff_symmDiff_small] at h'
  have := small_union h h'
  rw [inter_union_symmDiff] at this
  exact N₁.atoms_not_small <| this.mono subset_union_left

theorem inter_small_of_litter_ne (h : N₁ᴸ ≠ N₂ᴸ) : Small (N₁ᴬ ∩ N₂ᴬ) := by
  apply (small_union N₁.atoms_near_litter N₂.atoms_near_litter).mono
  apply Set.inter_subset_symmDiff_union_symmDiff
  exact litter_pairwise_disjoint h

theorem litter_ne_iff_inter_small (N₁ N₂ : NearLitter) : N₁ᴸ ≠ N₂ᴸ ↔ Small (N₁ᴬ ∩ N₂ᴬ) :=
  ⟨inter_small_of_litter_ne, litter_ne_of_inter_small⟩

def interference (N₁ N₂ : NearLitter) : Set Atom :=
  {a | N₁ᴸ = N₂ᴸ ↔ ¬(a ∈ N₁ᴬ ↔ a ∈ N₂ᴬ)} ∩ (N₁ᴬ ∪ N₂ᴬ)

theorem interference_eq_of_litter_eq (h : N₁ᴸ = N₂ᴸ) :
    interference N₁ N₂ = N₁ᴬ ∆ N₂ᴬ := by
  ext a
  simp only [interference, h, true_iff, mem_inter_iff, mem_setOf_eq, mem_union, mem_symmDiff]
  tauto

theorem interference_eq_of_litter_ne (h : N₁ᴸ ≠ N₂ᴸ) :
    interference N₁ N₂ = N₁ᴬ ∩ N₂ᴬ := by
  ext a
  simp only [interference, h, false_iff, not_not, mem_inter_iff, mem_setOf_eq, mem_union]
  tauto

theorem interference_small (N₁ N₂ : NearLitter) :
    Small (interference N₁ N₂) := by
  by_cases h : N₁ᴸ = N₂ᴸ
  · rwa [interference_eq_of_litter_eq h, ← litter_eq_iff_symmDiff_small]
  · rwa [interference_eq_of_litter_ne h, ← litter_ne_iff_inter_small]

end ConNF
