import ConNF.Base.Atom

/-!
# Near-litters

In this file, we define *near-litters*. A near-litter is a set of atoms that is near some litter
set. Large families of near-litters will be used to obscure certain information from the model.

Since there is exactly one litter near a given near-litter, we will store this litter as
extra data, which helps improve some definitional equalities.
-/

universe u

open Cardinal Set
open scoped symmDiff

namespace ConNF

variable [Params.{u}]

/-!
## Definition and basic results
-/

/-- A near-litter consists of a litter, a set of atoms, and a proof that those atoms
are near the litter set of that litter. -/
structure NearLitter where
  litter : Litter
  atoms : Set Atom
  atoms_near_litter' : atoms ~ litterᴬ

variable {N₁ N₂ : NearLitter}

/-- We write `Nᴸ` for the litter associated to a near-litter `N`. -/
instance : SuperL NearLitter Litter where
  superL N := N.litter

/-- We write `Nᴬ` for the set of atoms associated to a near-litter `N`. -/
instance : SuperA NearLitter (Set Atom) where
  superA N := N.atoms

/-- We write `Lᴺ` for the near-litter whose atoms are precisely the litter set of a litter `L`. -/
instance : SuperN Litter NearLitter where
  superN L := ⟨L, Lᴬ, near_rfl⟩

/-- A definitional simplification lemma for the `ᴸ` notation. -/
@[simp]
theorem NearLitter.mk_litter (L : Litter) (s : Set Atom) (h : s ~ Lᴬ) :
    (⟨L, s, h⟩ : NearLitter)ᴸ = L :=
  rfl

/-- A definitional simplification lemma for the `ᴬ` notation. -/
@[simp]
theorem NearLitter.mk_atoms (L : Litter) (s : Set Atom) (h : s ~ Lᴬ) :
    (⟨L, s, h⟩ : NearLitter)ᴬ = s :=
  rfl

/-- The set of atoms of a near-litter `N` is near the litter set of its associated litter. -/
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

/-- There are precisely `κ`-many atoms in each near-litter. -/
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

/-- Near-litters are near (treated as sets of atoms) precisely if they are near the same litter. -/
@[simp]
theorem nearLitter_near_iff (N₁ N₂ : NearLitter) :
    N₁ᴬ ~ N₂ᴬ ↔ N₁ᴸ = N₂ᴸ :=
  ⟨nearLitter_litter_eq_of_near, near_of_litter_eq⟩

/-- The extensionality principle for near-litters: if two near-litters contain the same atoms,
they are the same. This proves that the data of the litter near a given near-litter is redundant,
but as mentioned, its presence helps with certain definitional equalities. -/
@[ext]
theorem NearLitter.ext (h : N₁ᴬ = N₂ᴬ) :
    N₁ = N₂ := by
  obtain ⟨L₁, s₁, h₁⟩ := N₁
  obtain ⟨L₂, s₂, h₂⟩ := N₂
  cases nearLitter_litter_eq_of_near (near_of_eq h)
  subst h
  rfl

/-- There are `#μ` sets of atoms near a given litter set. -/
theorem card_near_litter (L : Litter) : #{s | s ~ Lᴬ} = #μ :=
  card_near_eq Lᴬ card_atom

/-- Strips away the name of the type of near-litters, converting it into a combination of types
well-known to mathlib. -/
def nearLitterEquiv : NearLitter ≃ (L : Litter) × {s | s ~ Lᴬ} where
  toFun N := ⟨Nᴸ, Nᴬ, N.atoms_near_litter⟩
  invFun N := ⟨N.1, N.2.1, N.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- There are exactly `#μ` near-litters. -/
@[simp]
theorem card_nearLitter : #NearLitter = #μ := by
  simp only [Cardinal.eq.mpr ⟨nearLitterEquiv⟩, mk_sigma, card_near_litter, sum_const, card_litter,
    lift_id, mul_mk_eq_max, max_self]

/-!
## Interference of near-litters

Later, we will prove some combinatorial results that relate to the ways that different near-litters
interact under certain permutations of our atoms. More precisely, we will need to calculate where
the images of atoms under a permutation can lie, given that we know the pointwise image of the
permutation on some near-litters. If we know the pointwise images of two near-litters under a
permutation of atoms, we know that (for example) atoms in the intersection of the two near-litters
must be mapped to the intersection of the pointwise images, and the same holds for other operations
on sets such as the symmetric difference.

This motivates the following definition: the *interference* of two near-litters `N₁` and `N₂` is
either their intersection or their symmetric difference, whichever is small. Note that precisely
one of these two sets will always be small. This is the set of atoms that is most tightly controlled
by the images of `N₁` and `N₂` under a permutation of atoms: an atom that was in the interference
of `N₁` and `N₂` must remain in the intersection or symmetric difference of their images, which
will still be a small set.

This definition will remain unused for quite some time; we will next revisit the interference of
near-litters when we begin to prove the freedom of action theorem.
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

/-- The *interference* of two near-litters `N₁` and `N₂` is their intersection if `N₁` and `N₂` are
near different litters, and their symmetric difference if `N₁` and `N₂` are near the same litter.
This will always be a small set. -/
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
