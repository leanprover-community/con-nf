import ConNF.Atom.NearLitter

universe u

open Equiv Equiv.Perm Function Set

open scoped Pointwise

namespace ConNF

variable [Params.{u}] {α β : Type u} {i j : Litter} {s t : Set Atom}

/-- A near-litter permutation is a permutation of the base type which sends near-litters to
near-litters. It turns out that the images of near-litters near the same litter are themselves near
the same litter. Hence a near-litter permutation induces a permutation of litters, and we keep that
as data for simplicity.

In the paper, this is called a -1-allowable permutation.
The proposition `near` can be interpreted as saying that if `s` is an `i`-near-litter, then its
image under the permutation (`atom_perm`) is near the litter that `i` is mapped to under the litter
permutation (`litter_perm`).

The definition `⇑atom_perm⁻¹ ⁻¹' s` is used instead of `⇑atom_perm '' s` because it has better
definitional properties. For instance, `x ∈ atom_perm⁻¹ ⁻¹' s` is definitionally equal to
`atom_perm x ∈ s`.
-/
structure NearLitterPerm : Type u where
  atomPerm : Perm Atom
  litterPerm : Perm Litter
  near ⦃i : Litter⦄ ⦃s : Set Atom⦄ :
    IsNearLitter i s → IsNearLitter (litterPerm i) (atomPerm⁻¹.toFun ⁻¹' s)

/-- This is the condition that relates the `atom_perm` and the `litter_perm`. This is essentially
the field `near` in the structure `near_litter_perm`, but presented here as a lemma. -/
theorem IsNearLitter.map {f : NearLitterPerm} {s : Set Atom} (h : IsNearLitter i s) :
    IsNearLitter (f.litterPerm i) (f.atomPerm⁻¹.toFun ⁻¹' s) :=
  f.near h

namespace NearLitterPerm

variable {f g : NearLitterPerm}

/-- The map from the type of near-litter permutations to the type of permutations of `τ₋₁` is
injective. That is, if two near-litter permutations have the same action on the base type, they are
equal. -/
theorem atomPerm_injective : Injective NearLitterPerm.atomPerm := by
  rintro ⟨f, f', hf⟩ ⟨g, g', hg⟩ (h : f = g)
  suffices f' = g' by
    subst h
    subst this
    rfl
  ext i : 1
  exact isNearLitter_litterSet_iff.1
    (((hf <| isNearLitter_litterSet _).trans <| by rw [h]).trans
      (hg <| isNearLitter_litterSet _).symm)

/-- An extensionality result for near-litter permutations.
If two near-litter permutations have the same action on the base type, they are equal. -/
@[ext]
theorem ext (h : f.atomPerm = g.atomPerm) : f = g :=
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
  ⟨fun f =>
    ⟨f.atomPerm⁻¹, f.litterPerm⁻¹, fun i s h => by
      have : IsNear (f.atomPerm⁻¹.toFun ⁻¹' litterSet (f.litterPerm⁻¹ i)) s :=
        (f.near <| isNearLitter_litterSet _).near (by rwa [apply_inv_self])
      simpa only [toFun_as_coe_apply, Perm.image_inv, toFun_as_coe, preimage_inv, preimage_image,
        isNear_litterSet] using this.image f.atomPerm⁻¹.toFun⟩⟩

/-- Near-litter permutations can be composed. -/
instance : Mul NearLitterPerm :=
  ⟨fun f g => ⟨f.atomPerm * g.atomPerm, f.litterPerm * g.litterPerm, fun _ _ h => h.map.map⟩⟩

/-- Dividing two permutations `f / g` can be interpreted as `f * g⁻¹`. -/
instance : Div NearLitterPerm :=
  ⟨fun f g => ⟨f.atomPerm / g.atomPerm, f.litterPerm / g.litterPerm, (f * g⁻¹).near⟩⟩

/-- We can raise near-litter permutations to a natural power since we can do this to
permutations of the base type and the type of litters. -/
instance hasPow : Pow NearLitterPerm ℕ :=
  ⟨fun f n =>
    ⟨f.atomPerm ^ n, f.litterPerm ^ n, by
      induction n with
      | zero =>
          exact (1 : NearLitterPerm).near
      | succ d hd =>
          have := (f * ⟨f.atomPerm ^ d, f.litterPerm ^ d, hd⟩).near
          exact this⟩⟩

/-- We can raise near-litter permutations to an integer power since we can do this to
permutations of the base type and the type of litters. -/
instance hasZpow : Pow NearLitterPerm ℤ :=
  ⟨fun f n =>
    ⟨f.atomPerm ^ n, f.litterPerm ^ n, by
      obtain (n | n) := n
      · exact (f ^ n).near
      · exact (f ^ (n + 1))⁻¹.near⟩⟩

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
theorem atomPerm_inv (f : NearLitterPerm) : f⁻¹.atomPerm = f.atomPerm⁻¹ :=
  rfl

@[simp]
theorem atomPerm_hMul (f g : NearLitterPerm) : (f * g).atomPerm = f.atomPerm * g.atomPerm :=
  rfl

@[simp]
theorem atomPerm_div (f g : NearLitterPerm) : (f / g).atomPerm = f.atomPerm / g.atomPerm :=
  rfl

@[simp]
theorem atomPerm_pow (f : NearLitterPerm) (n : ℕ) : (f ^ n).atomPerm = f.atomPerm ^ n :=
  rfl

@[simp]
theorem atomPerm_zpow (f : NearLitterPerm) (n : ℤ) : (f ^ n).atomPerm = f.atomPerm ^ n :=
  rfl

@[simp]
theorem litterPerm_one : (1 : NearLitterPerm).litterPerm = 1 :=
  rfl

@[simp]
theorem litterPerm_inv (f : NearLitterPerm) : f⁻¹.litterPerm = f.litterPerm⁻¹ :=
  rfl

@[simp]
theorem litterPerm_hMul (f g : NearLitterPerm) : (f * g).litterPerm = f.litterPerm * g.litterPerm :=
  rfl

@[simp]
theorem litterPerm_div (f g : NearLitterPerm) : (f / g).litterPerm = f.litterPerm / g.litterPerm :=
  rfl

@[simp]
theorem litterPerm_pow (f : NearLitterPerm) (n : ℕ) : (f ^ n).litterPerm = f.litterPerm ^ n :=
  rfl

@[simp]
theorem litterPerm_zpow (f : NearLitterPerm) (n : ℤ) : (f ^ n).litterPerm = f.litterPerm ^ n :=
  rfl

/-- Near-litter permutations form a group. -/
instance : Group NearLitterPerm :=
  atomPerm_injective.group _ atomPerm_one atomPerm_hMul atomPerm_inv atomPerm_div atomPerm_pow
    atomPerm_zpow

/-- Near-litter permutations act on the base type via the base permutation. -/
instance : MulAction NearLitterPerm Atom
    where
  smul f := f.atomPerm
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Near-litter permutations act on litters via the litter permutation. -/
instance : MulAction NearLitterPerm Litter
    where
  smul f := f.litterPerm
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem near_smul (f : NearLitterPerm) (h : IsNearLitter i s) : IsNearLitter (f • i) (f • s) := by
  convert f.near h using 1
  exact (preimage_inv _ _).symm

instance : SMul NearLitterPerm NearLitter :=
  ⟨fun f N => ⟨f • N.1, f • (N : Set Atom), f.near_smul N.2.2⟩⟩

@[simp]
theorem toProd_smul (f : NearLitterPerm) (N : NearLitter) : (f • N).toProd = f • N.toProd :=
  rfl

/-- Near-litter permutations act on near-litters. -/
instance : MulAction NearLitterPerm NearLitter :=
  NearLitter.toProd_injective.mulAction _ toProd_smul

@[simp]
theorem smul_fst (π : NearLitterPerm) (N : NearLitter) : (π • N).fst = π • N.fst :=
  rfl

@[simp]
theorem coe_smul (π : NearLitterPerm) (N : NearLitter) : ((π • N) : Set Atom) = π • (N : Set Atom) :=
  rfl

@[simp]
theorem smul_localCardinal (π : NearLitterPerm) (i : Litter) :
    π • localCardinal i = localCardinal (π • i) := by ext N; simp [mem_smul_set, ← eq_inv_smul_iff]

@[simp]
theorem NearLitter.mem_snd_iff (N : NearLitter) (a : Atom) : a ∈ (N.snd : Set Atom) ↔ a ∈ N :=
  Iff.rfl

@[simp]
theorem NearLitter.not_mem_snd_iff (N : NearLitter) (a : Atom) : a ∉ (N.snd : Set Atom) ↔ a ∉ N :=
  Iff.rfl

theorem smul_nearLitter_eq_smul_symmDiff_smul (π : NearLitterPerm) (N : NearLitter) :
    (π • N : Set Atom) = (π • N.fst.toNearLitter : Set Atom) ∆ (π • litterSet N.fst ∆ N.snd) := by
  ext a : 1
  simp only [mem_symmDiff, mem_smul_set_iff_inv_smul_mem, coe_smul]
  tauto

end NearLitterPerm

end ConNF
