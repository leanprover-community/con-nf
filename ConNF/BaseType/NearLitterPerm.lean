import Mathlib.Data.Set.Pointwise.SMul
import ConNF.BaseType.NearLitter

/-!
# Near-litter permutations

In this file, we define near-litter permutations, their group structure, and their actions on
atoms, litters, and near-litters.

## Main declarations

* `ConNF.NearLitterPerm`: The type of near-litter permutations.
* `ConNF.NearLitterPerm.smul_nearLitter_coe`: The action of a near-litter permutation on a
    near-litter agrees with the pointwise action that treats it as a set of atoms.
* `ConNF.NearLitterPerm.smul_nearLitter_eq_smul_symmDiff_smul`: We can determine the action of a
    near-litter permutation on a near-litter by knowing its precise action on the relevant litter,
    as well as the action on all atoms in the symmetric difference between that near-litter and its
    corresponding litter.
-/

universe u

open Equiv Equiv.Perm Function Set

open scoped Pointwise symmDiff

namespace ConNF

variable [Params.{u}] {L : Litter}

/--
A near-litter permutation is a permutation of atoms which sends near-litters to near-litters.
It turns out that the images of near-litters near the same litter are themselves near
the same litter. Hence a near-litter permutation induces a permutation of litters, and we keep that
as data for simplicity.

This is sometimes called a -1-allowable permutation.
The proposition `near` can be interpreted as saying that if `s` is an `L`-near-litter, then its
image under the permutation (`atomPerm`) is near the litter that `L` is mapped to under the litter
permutation (`litterPerm`).

The definition `↑atomPerm⁻¹ ⁻¹' s` is used instead of `↑atomPerm '' s` because it has better
definitional properties. For instance, `x ∈ ↑atomPerm⁻¹ ⁻¹' s` is definitionally equal to
`atomPerm⁻¹ x ∈ s`.
-/
structure NearLitterPerm : Type u where
  atomPerm : Perm Atom
  litterPerm : Perm Litter
  near ⦃L : Litter⦄ ⦃s : Set Atom⦄ :
    IsNearLitter L s → IsNearLitter (litterPerm L) (↑atomPerm⁻¹ ⁻¹' s)

/-- This is the condition that relates the `atomPerm` and the `litterPerm`. This is essentially
the field `near` in the structure `NearLitterPerm`, but presented here as a lemma. -/
theorem IsNearLitter.map {π : NearLitterPerm} {s : Set Atom} (h : IsNearLitter L s) :
    IsNearLitter (π.litterPerm L) (π.atomPerm⁻¹.toFun ⁻¹' s) :=
  π.near h

namespace NearLitterPerm

variable {π π' : NearLitterPerm}

/-- The map from the type of near-litter permutations to the type of permutations of atoms is
injective. That is, if two near-litter permutations have the same action on atoms, they are
equal. -/
theorem atomPerm_injective : Injective NearLitterPerm.atomPerm := by
  rintro ⟨πa, πL, hπ⟩ ⟨πa', πL', hπ'⟩ (h : πa = πa')
  suffices πL = πL' by
    subst h
    subst this
    rfl
  ext i : 1
  exact isNearLitter_litterSet_iff.1
    (((hπ <| isNearLitter_litterSet _).trans <| by rw [h]).trans
      (hπ' <| isNearLitter_litterSet _).symm)

/-- An extensionality result for near-litter permutations.
If two near-litter permutations have the same action on atoms, they are equal. -/
@[ext]
theorem ext (h : π.atomPerm = π'.atomPerm) : π = π' :=
  atomPerm_injective h

/-!
We are going to show that the set of near-litter permutations forms a group.
To do this, we construct several instances, such as the existence of an identity
element or inverse elements.
-/

/-- The identity near-litter permutation. -/
instance : One NearLitterPerm :=
  ⟨⟨1, 1, fun _ _ => id⟩⟩

/-- Any near-litter permutation admits an inverse, which is also a near-litter permutation. -/
instance : Inv NearLitterPerm :=
  ⟨fun π =>
    ⟨π.atomPerm⁻¹, π.litterPerm⁻¹, fun L s h => by
      have : IsNear (π.atomPerm⁻¹.toFun ⁻¹' litterSet (π.litterPerm⁻¹ L)) s :=
        (π.near <| isNearLitter_litterSet _).near (by rwa [apply_inv_self])
      simpa only [Perm.image_inv, toFun_as_coe, preimage_inv, preimage_image,
        isNear_litterSet] using this.image π.atomPerm⁻¹.toFun⟩⟩

/-- Near-litter permutations can be composed. -/
instance : Mul NearLitterPerm :=
  ⟨fun π π' => ⟨π.atomPerm * π'.atomPerm, π.litterPerm * π'.litterPerm, fun _ _ h => h.map.map⟩⟩

/-- Dividing two permutations `π / π'` can be interpreted as `π * π'⁻¹`. -/
instance : Div NearLitterPerm :=
  ⟨fun π π' => ⟨π.atomPerm / π'.atomPerm, π.litterPerm / π'.litterPerm, (π * π'⁻¹).near⟩⟩

/-- We can raise near-litter permutations to a natural power since we can do this to
permutations of atoms and litters. -/
instance : Pow NearLitterPerm ℕ :=
  ⟨fun π n =>
    ⟨π.atomPerm ^ n, π.litterPerm ^ n, by
      induction n with
      | zero =>
          exact (1 : NearLitterPerm).near
      | succ n hn =>
          have := (⟨π.atomPerm ^ n, π.litterPerm ^ n, hn⟩ * π).near
          exact this⟩⟩

/-- We can raise near-litter permutations to an integer power since we can do this to
permutations of atoms and litters. -/
instance : Pow NearLitterPerm ℤ :=
  ⟨fun π n =>
    ⟨π.atomPerm ^ n, π.litterPerm ^ n, by
      obtain (n | n) := n
      · exact (π ^ n).near
      · exact (π ^ (n + 1))⁻¹.near⟩⟩

instance : Inhabited NearLitterPerm :=
  ⟨1⟩

/-!
The following lemmas describe how the group of near-litter permutations interacts with the group of
base type permutations and the group of litter permutations. In particular, many group operations,
such as taking the inverse, can be moved out of the near-litter context and into the (simpler) base
permutation or litter permutation context.

The `@[simp]` attribute teaches these results to the `simp` tactic. This means that `simp` will (for
example) prefer group operations to be applied after extracting the base permutation, not before.
-/

@[simp]
theorem atomPerm_one : (1 : NearLitterPerm).atomPerm = 1 :=
  rfl

@[simp]
theorem atomPerm_inv (π : NearLitterPerm) : π⁻¹.atomPerm = π.atomPerm⁻¹ :=
  rfl

@[simp]
theorem atomPerm_hMul (π π' : NearLitterPerm) : (π * π').atomPerm = π.atomPerm * π'.atomPerm :=
  rfl

@[simp]
theorem atomPerm_div (π π' : NearLitterPerm) : (π / π').atomPerm = π.atomPerm / π'.atomPerm :=
  rfl

@[simp]
theorem atomPerm_pow (π : NearLitterPerm) (n : ℕ) : (π ^ n).atomPerm = π.atomPerm ^ n :=
  rfl

@[simp]
theorem atomPerm_zpow (π : NearLitterPerm) (n : ℤ) : (π ^ n).atomPerm = π.atomPerm ^ n :=
  rfl

@[simp]
theorem litterPerm_one : (1 : NearLitterPerm).litterPerm = 1 :=
  rfl

@[simp]
theorem litterPerm_inv (π : NearLitterPerm) : π⁻¹.litterPerm = π.litterPerm⁻¹ :=
  rfl

@[simp]
theorem litterPerm_hMul (π π' : NearLitterPerm) : (π * π').litterPerm = π.litterPerm * π'.litterPerm :=
  rfl

@[simp]
theorem litterPerm_div (π π' : NearLitterPerm) : (π / π').litterPerm = π.litterPerm / π'.litterPerm :=
  rfl

@[simp]
theorem litterPerm_pow (π : NearLitterPerm) (n : ℕ) : (π ^ n).litterPerm = π.litterPerm ^ n :=
  rfl

@[simp]
theorem litterPerm_zpow (π : NearLitterPerm) (n : ℤ) : (π ^ n).litterPerm = π.litterPerm ^ n :=
  rfl

/-- Near-litter permutations form a group. -/
instance : Group NearLitterPerm :=
  atomPerm_injective.group _ atomPerm_one atomPerm_hMul atomPerm_inv atomPerm_div atomPerm_pow
    atomPerm_zpow

/-- Near-litter permutations act on atoms via the atom permutation. -/
instance : MulAction NearLitterPerm Atom
    where
  smul π := π.atomPerm
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Near-litter permutations act on litters via the litter permutation. -/
instance : MulAction NearLitterPerm Litter
    where
  smul π := π.litterPerm
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Near-litter permutations act on near-litters. -/
instance : MulAction NearLitterPerm NearLitter
    where
  smul π N := ⟨π • N.1, ↑π.atomPerm⁻¹ ⁻¹' N, π.near N.2.2⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem smul_nearLitter_def (π : NearLitterPerm) (N : NearLitter) :
    π • N = ⟨π • N.1, ↑π.atomPerm⁻¹ ⁻¹' N, π.near N.2.2⟩ :=
  rfl

@[simp]
theorem smul_nearLitter_fst (π : NearLitterPerm) (N : NearLitter) : (π • N).fst = π • N.fst :=
  rfl

theorem smul_nearLitter_coe_preimage (π : NearLitterPerm) (N : NearLitter) :
    (π • N : NearLitter) = ((π.atomPerm⁻¹ : Perm Atom) : Atom → Atom) ⁻¹' N :=
  rfl

/-- The action of a near-litter perm on a near-litter agrees with the pointwise action on its
atoms. -/
theorem smul_nearLitter_coe (π : NearLitterPerm) (N : NearLitter) :
    (π • N : NearLitter) = π • (N : Set Atom) := by
  rw [smul_nearLitter_coe_preimage, preimage_inv]
  rfl

theorem smul_nearLitter_snd (π : NearLitterPerm) (N : NearLitter) :
    ((π • N).2 : Set Atom) = π • (N.2 : Set Atom) :=
  smul_nearLitter_coe π N

@[simp]
theorem smul_localCardinal (π : NearLitterPerm) (L : Litter) :
    π • localCardinal L = localCardinal (π • L) := by
  ext N
  simp [mem_smul_set, ← eq_inv_smul_iff]

@[simp]
theorem NearLitter.mem_snd_iff (N : NearLitter) (a : Atom) : a ∈ (N.snd : Set Atom) ↔ a ∈ N :=
  Iff.rfl

@[simp]
theorem NearLitter.not_mem_snd_iff (N : NearLitter) (a : Atom) : a ∉ (N.snd : Set Atom) ↔ a ∉ N :=
  Iff.rfl

theorem smul_nearLitter_eq_smul_symmDiff_smul (π : NearLitterPerm) (N : NearLitter) :
    (π • N : NearLitter) =
      ((π • N.fst.toNearLitter : NearLitter) : Set Atom) ∆ (π • litterSet N.fst ∆ N.snd) := by
  ext a : 1
  simp only [mem_symmDiff, mem_smul_set_iff_inv_smul_mem, smul_nearLitter_coe]
  tauto

end NearLitterPerm

end ConNF
