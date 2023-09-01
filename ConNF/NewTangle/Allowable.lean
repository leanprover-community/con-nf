import Mathlib.GroupTheory.GroupAction.Sigma
import ConNF.NewTangle.CodeEquiv

/-!
# Allowable permutations

In this file, we define the type of allowable permutations at level `α`, assuming that they
exist for all type indices `β < α`.

## Main declarations

* `ConNF.SemiallowablePerm`: A collection of allowable permutations at every level `β < α`.
* `ConNF.AllowablePerm`: A `SemiallowablePerm` that commutes with the `fuzz` map.
* `ConNF.Code.smul_code`: Allowable permutations preserve code equivalence.
-/

open Function Set WithBot

open scoped Pointwise

universe u

namespace ConNF

variable [Params.{u}] (α : Λ) [TangleDataIio α] (β : IioBot α) (γ : Iio α)

open Code

/-- A semi-allowable permutation is a collection of allowable permutations at every type index
`β < α`. The type of allowable permutations is a subtype of this type. Applying a one-step
derivative `α ⟶ β` to a given semi-allowable permutation yields the `β`-allowable permutation
stored inside it. -/
def SemiallowablePerm : Type u :=
  ∀ β : IioBot α, Allowable β

noncomputable instance : Group (SemiallowablePerm α) := Pi.group

namespace SemiallowablePerm

variable {α}
variable (ρ : SemiallowablePerm α) (c : Code α)

@[simp]
theorem one_apply :
    (1 : SemiallowablePerm α) β = 1 :=
  rfl

@[simp]
theorem mul_apply (ρ ρ' : SemiallowablePerm α) :
    (ρ * ρ') β = ρ β * ρ' β :=
  rfl

@[simp]
theorem inv_apply :
    ρ⁻¹ β = (ρ β)⁻¹ :=
  rfl

section PathTop

/-!
We introduce machinery for manipulating the opposite end of a path.
This allows us to convert semi-allowable permutations into structural permutations, whose
derivative maps are more naturally expressed in the other direction.
-/

variable {V : Type _} [Quiver V]

/-- If the path is nonempty, extract the second element of the path.
This requires induction over paths because paths in quivers are expressed with their `cons`
operation at the end, not the start. -/
def pathTop {x y : V} : Quiver.Path x y → V
| Quiver.Path.cons Quiver.Path.nil e => y
| Quiver.Path.cons (Quiver.Path.cons p e) _ => pathTop (Quiver.Path.cons p e)
| Quiver.Path.nil => y

theorem pathTop_toPath_comp {x y z : V} (e : x ⟶ y) (p : Quiver.Path y z) :
    pathTop ((e.toPath).comp p) = y := by
  induction p with
  | nil => rfl
  | cons p f ih =>
    cases p with
    | nil => rfl
    | cons p g => exact ih

def pathTop_hom {x y : V} (p : Quiver.Path x y) (h : p.length ≠ 0) : x ⟶ pathTop p :=
  Quiver.Path.rec
    (fun h => (h rfl).elim)
    (fun {y z} p e ih _ => Quiver.Path.rec
      (motive := fun {y} p =>
        (e : y ⟶ z) →
        (ih : Quiver.Path.length p ≠ 0 → (x ⟶ pathTop p)) →
        x ⟶ pathTop (Quiver.Path.cons p e))
      (fun e _ => e)
      (fun {v w} p _ _ _ ih => ih (by simp))
      p e ih)
    p h

/-- Extract the portion of the path after the first morphism. -/
def pathTail {x : V} : {y : V} → (p : Quiver.Path x y) → Quiver.Path (pathTop p) y
| _, Quiver.Path.cons Quiver.Path.nil _ => Quiver.Path.nil
| _, Quiver.Path.cons (Quiver.Path.cons p e) f => (pathTail (Quiver.Path.cons p e)).cons f
| _, Quiver.Path.nil => Quiver.Path.nil

/-- We can remove the first morphism from a path and compose it back to form the original path. -/
theorem pathTop_pathTail {x y : V} (p : Quiver.Path x y) (h : p.length ≠ 0) :
    (Quiver.Hom.toPath (pathTop_hom p h)).comp (pathTail p) = p := by
  induction p with
  | nil => cases h rfl
  | cons p e ih =>
    cases p with
    | nil => rfl
    | cons p e => simp_rw [← ih (by simp)]; rfl

theorem ExtendedIndex.pathTop_pathTail {α : Λ} (A : ExtendedIndex α) :
    (Quiver.Hom.toPath (pathTop_hom A A.length_ne_zero)).comp (pathTail A) = A :=
  SemiallowablePerm.pathTop_pathTail A A.length_ne_zero

end PathTop

/-- Convert a semi-allowable permutation to a structural permutation.
To work out the `A`-derivative, we extract the first morphism in the path `A` and use it to
determine which of the `β`-allowable permutations in `ρ` we will use. -/
noncomputable def toStructPerm' (ρ : SemiallowablePerm α) : StructPerm α :=
  fun A => Allowable.toStructPerm (ρ ⟨pathTop A, pathTop_hom A A.length_ne_zero⟩) (pathTail A)

theorem toStructPerm'_one : (toStructPerm' 1 : StructPerm α) = 1 := by
  funext A
  rw [toStructPerm', one_apply, map_one]
  rfl

/-- Convert a semi-allowable permutation to a structural permutation. -/
noncomputable def toStructPerm : SemiallowablePerm α →* StructPerm α
    where
  toFun := toStructPerm'
  map_one' := by
    funext A
    rw [toStructPerm', one_apply, map_one]
    rfl
  map_mul' ρ ρ' := by
    funext A
    simp only
    rw [toStructPerm', mul_apply, map_mul]
    rfl

section

variable {X : Type _} [MulAction (StructPerm α) X]

noncomputable instance : MulAction (SemiallowablePerm α) X :=
  MulAction.compHom _ toStructPerm

@[simp]
theorem toStructPerm_smul (ρ : SemiallowablePerm α) (x : X) :
    ρ • x = SemiallowablePerm.toStructPerm ρ • x :=
  rfl

end

/-- In the same way that structural permutations act on support conditions, semiallowable
permutations act on codes. -/
instance : MulAction (SemiallowablePerm α) (Code α)
    where
  smul ρ c := ⟨c.1, ρ c.1 • c.2⟩
  one_smul _ := Sigma.ext rfl (heq_of_eq (one_smul _ _))
  mul_smul _ _ _ := Sigma.ext rfl (heq_of_eq (mul_smul _ _ _))

@[simp]
theorem fst_smul : (ρ • c).1 = c.1 :=
  rfl

@[simp]
theorem snd_smul : (ρ • c).2 = ρ c.1 • c.2 :=
  rfl

@[simp]
theorem smul_mk (f : SemiallowablePerm α) (γ s) : f • (mk γ s : Code α) = mk γ (f γ • s) :=
  rfl

instance : SMul (SemiallowablePerm α) (NonemptyCode α) :=
  ⟨fun ρ c => ⟨ρ • (c : Code α), c.2.image _⟩⟩

@[simp, norm_cast]
theorem coe_smul (c : NonemptyCode α) : (↑(ρ • c) : Code α) = ρ • (c : Code α) :=
  rfl

instance : MulAction (SemiallowablePerm α) (NonemptyCode α) :=
  Subtype.coe_injective.mulAction _ coe_smul

end SemiallowablePerm

variable [BasePositions] [PositionedTanglesIio α] [TypedObjectsIio α] [TangleData α]

/-- We say that a semiallowable permutation is allowable if its one-step derivatives commute with
the `fuzz` maps. -/
def SemiallowablePerm.IsAllowable (ρ : SemiallowablePerm α) : Prop :=
  ∀ ⦃β : IioBot α⦄ ⦃γ : Iio α⦄ (hβγ : β ≠ γ) (t : Tangle β),
  Allowable.toStructPerm (ρ γ) (Quiver.Hom.toPath <| bot_lt_coe _) •
    fuzz (coe_ne hβγ) t =
  fuzz (coe_ne hβγ) (ρ β • t)

variable {ρ ρ' : SemiallowablePerm α}

theorem isAllowable_one : (1 : SemiallowablePerm α).IsAllowable := by
  intros β γ hβγ t
  simp only [SemiallowablePerm.one_apply, map_one, StructPerm.one_apply, one_smul]

theorem isAllowable_inv (h : ρ.IsAllowable) : ρ⁻¹.IsAllowable := by
  intros β γ hβγ t
  have := h hβγ (ρ⁻¹ β • t)
  simp only [SemiallowablePerm.inv_apply, smul_inv_smul] at this
  rw [← this]
  simp only [SemiallowablePerm.inv_apply, map_inv, StructPerm.inv_apply, inv_smul_smul]

theorem isAllowable_mul (h : ρ.IsAllowable) (h' : ρ'.IsAllowable) : (ρ * ρ').IsAllowable := by
  intros β γ hβγ t
  simp only [SemiallowablePerm.mul_apply, map_mul, StructPerm.mul_apply, mul_smul]
  rw [h' hβγ t, h hβγ (ρ' β • t)]

theorem isAllowable_div (h : ρ.IsAllowable) (h' : ρ'.IsAllowable) : (ρ / ρ').IsAllowable := by
  rw [div_eq_mul_inv]
  exact isAllowable_mul α h (isAllowable_inv α h')

theorem isAllowable_pow (h : ρ.IsAllowable) (n : ℕ) : (ρ ^ n).IsAllowable := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact isAllowable_one α
  | succ n ih =>
    rw [pow_succ]
    exact isAllowable_mul α h ih

theorem isAllowable_zpow (h : ρ.IsAllowable) (n : ℤ) : (ρ ^ n).IsAllowable := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_coe, zpow_coe_nat]
    exact isAllowable_pow α h n
  | negSucc n =>
    rw [zpow_negSucc]
    exact isAllowable_inv α (isAllowable_pow α h (n + 1))

/-- An allowable permutation is a semi-allowable permutation that commutes with the `fuzz` maps. -/
def AllowablePerm :=
  { ρ : SemiallowablePerm α // ρ.IsAllowable }

variable {α}
variable {ρ : AllowablePerm α} {c d : Code α}

namespace AllowablePerm

instance : CoeTC (AllowablePerm α) (SemiallowablePerm α)
    where
  coe := Subtype.val

theorem coe_injective : Injective (Subtype.val : AllowablePerm α → SemiallowablePerm α) :=
  Subtype.coe_injective

noncomputable instance : One (AllowablePerm α) :=
  ⟨⟨1, isAllowable_one α⟩⟩

noncomputable instance : Inv (AllowablePerm α) :=
  ⟨fun ρ => ⟨ρ⁻¹, isAllowable_inv α ρ.prop⟩⟩

noncomputable instance : Mul (AllowablePerm α) :=
  ⟨fun ρ ρ' => ⟨ρ * ρ', isAllowable_mul α ρ.prop ρ'.prop⟩⟩

noncomputable instance : Div (AllowablePerm α) :=
  ⟨fun ρ ρ' => ⟨ρ / ρ', isAllowable_div α ρ.prop ρ'.prop⟩⟩

noncomputable instance : Pow (AllowablePerm α) ℕ :=
  ⟨fun ρ n => ⟨ρ.val ^ n, isAllowable_pow α ρ.prop n⟩⟩

noncomputable instance : Pow (AllowablePerm α) ℤ :=
  ⟨fun ρ n => ⟨ρ.val ^ n, isAllowable_zpow α ρ.prop n⟩⟩

@[simp]
theorem coe_one : ((1 : AllowablePerm α) : SemiallowablePerm α) = 1 :=
  rfl

@[simp]
theorem coe_inv (ρ : AllowablePerm α) : ↑(ρ⁻¹) = (ρ : SemiallowablePerm α)⁻¹ :=
  rfl

@[simp]
theorem coe_mul (ρ ρ' : AllowablePerm α) : ↑(ρ * ρ') = (ρ : SemiallowablePerm α) * ρ' :=
  rfl

@[simp]
theorem coe_div (ρ ρ' : AllowablePerm α) : ↑(ρ / ρ') = (ρ : SemiallowablePerm α) / ρ' :=
  rfl

@[simp]
theorem coe_pow (ρ : AllowablePerm α) (n : ℕ) : ↑(ρ ^ n) = (ρ : SemiallowablePerm α) ^ n :=
  rfl

@[simp]
theorem coe_zpow (ρ : AllowablePerm α) (n : ℤ) : ↑(ρ ^ n) = (ρ : SemiallowablePerm α) ^ n :=
  rfl

noncomputable instance : Group (AllowablePerm α) :=
  coe_injective.group
    Subtype.val
    coe_one
    coe_mul
    coe_inv
    coe_div
    coe_pow
    coe_zpow

/-- The coercion from allowable to semi-allowable permutations as a monoid homomorphism. -/
@[simps]
noncomputable def coeHom : AllowablePerm α →* SemiallowablePerm α
    where
  toFun := Subtype.val
  map_one' := coe_one
  map_mul' := coe_mul

/-- Turn an allowable permutation into a structural permutation. -/
noncomputable def toStructPerm : AllowablePerm α →* StructPerm α :=
  SemiallowablePerm.toStructPerm.comp coeHom

section

variable {X : Type _} [MulAction (SemiallowablePerm α) X]

noncomputable instance : MulAction (AllowablePerm α) X :=
  MulAction.compHom _ coeHom

@[simp]
theorem coe_smul (ρ : AllowablePerm α) (x : X) : (ρ : SemiallowablePerm α) • x = ρ • x :=
  rfl

end

@[simp]
theorem smul_typedNearLitter (ρ : AllowablePerm α) (N : NearLitter) :
    ρ.val γ • (typedNearLitter N : Tangle (γ : Λ)) =
    typedNearLitter ((Allowable.toStructPerm ((ρ : SemiallowablePerm α) γ)
      (Quiver.Hom.toPath (bot_lt_coe _))) • N) :=
  Allowable.smul_typedNearLitter _ _

@[simp]
theorem fst_smul (ρ : AllowablePerm α) (c : Code α) : (ρ • c).1 = c.1 :=
  rfl

@[simp]
theorem snd_smul (ρ : AllowablePerm α) (c : Code α) : (ρ • c).2 = ρ.val c.1 • c.2 :=
  rfl

@[simp]
theorem smul_mk (ρ : AllowablePerm α) (γ s) : ρ • (mk γ s : Code α) = mk γ (ρ.val γ • s) :=
  rfl

end AllowablePerm

namespace AllowablePerm

variable {β γ}

/-- Allowable permutations commute with the `cloud` map. -/
theorem smul_cloud (ρ : AllowablePerm α) (s : Set (Tangle β)) (hβγ : β ≠ γ) :
    ρ.val γ • cloud hβγ s = cloud hβγ (ρ.val β • s) := by
  ext t
  simp only [cloud, mem_image, mem_iUnion, mem_localCardinal, exists_prop, ← image_smul]
  simp_rw [exists_exists_and_eq_and]
  constructor
  · rintro ⟨N, ⟨t, ht₁, ht₂⟩, rfl⟩
    refine ⟨Allowable.toStructPerm ((ρ : SemiallowablePerm α) γ)
        (Quiver.Hom.toPath <| bot_lt_coe _) • N, ⟨t, ht₁, ?_⟩, ?_⟩
    · rw [← ρ.prop hβγ, NearLitterPerm.smul_nearLitter_fst, ht₂]
    · rw [smul_typedNearLitter]
  · rintro ⟨N, ⟨t, ht₁, ht₂⟩, rfl⟩
    refine ⟨Allowable.toStructPerm ((ρ : SemiallowablePerm α) γ)⁻¹
        (Quiver.Hom.toPath <| bot_lt_coe _) • N, ⟨t, ht₁, ?_⟩, ?_⟩
    · rw [NearLitterPerm.smul_nearLitter_fst, ht₂, ← ρ.prop hβγ, map_inv,
        StructPerm.inv_apply, inv_smul_smul]
    · rw [smul_typedNearLitter, map_inv, StructPerm.inv_apply, smul_inv_smul]

/-- Allowable permutations commute with the `cloudCode` map. -/
theorem smul_cloudCode (ρ : AllowablePerm α) (hc : c.1 ≠ γ) :
    ρ • cloudCode γ c = cloudCode γ (ρ • c) := by
  simp only [cloudCode_ne γ c hc, smul_mk, cloudCode_ne γ (ρ • c) hc, fst_smul, snd_smul, mk_inj]
  rw [smul_cloud]

end AllowablePerm

theorem CloudRel.smul : c ↝₀ d → ρ • c ↝₀ ρ • d := by
  rintro ⟨γ, hγ⟩
  exact (CloudRel_iff _ _).2 ⟨_, hγ, ρ.smul_cloudCode hγ⟩

@[simp]
theorem smul_cloudRel : ρ • c ↝₀ ρ • d ↔ c ↝₀ d := by
  refine ⟨fun h => ?_, CloudRel.smul⟩
  rw [← inv_smul_smul ρ c, ← inv_smul_smul ρ d]
  exact h.smul

namespace Code

theorem isEven_smul_nonempty : ∀ c : NonemptyCode α, (ρ • c.val).IsEven ↔ c.val.IsEven
  | ⟨c, hc⟩ => by
    simp_rw [Code.IsEven_iff]
    constructor <;> intro h d hd
    · have := hd.nonempty_iff.2 hc
      have _ : ⟨d, this⟩ ↝ ⟨c, hc⟩ := cloudRel_coe_coe.1 hd
      exact Code.not_isEven.1 fun H =>
        (h _ hd.smul).not_isEven <| (isEven_smul_nonempty ⟨d, this⟩).2 H
    · rw [← smul_inv_smul ρ d] at hd ⊢
      rw [smul_cloudRel] at hd
      have := hd.nonempty_iff.2 hc
      have _ : ⟨_, this⟩ ↝ ⟨c, hc⟩ := cloudRel_coe_coe.1 hd
      exact Code.not_isEven.1 fun H =>
        (h _ hd).not_isEven <| (isEven_smul_nonempty ⟨_, this⟩).1 H
termination_by isEven_smul_nonempty c => c

@[simp]
theorem isEven_smul : (ρ • c).IsEven ↔ c.IsEven := by
  obtain (h | h) := c.2.eq_empty_or_nonempty
  · rw [IsEmpty.isEven_iff h, IsEmpty.isEven_iff]
    · rfl
    simpa [Code.IsEmpty]
  · exact isEven_smul_nonempty ⟨c, h⟩

@[simp]
theorem isOdd_smul : (ρ • c).IsOdd ↔ c.IsOdd := by simp_rw [← Code.not_isEven, isEven_smul]

alias ⟨_, isEven.smul⟩ := isEven_smul

alias ⟨_, isOdd.smul⟩ := isOdd_smul

theorem Equiv.smul : c ≡ d → ρ • c ≡ ρ • d := by
  intro h
  cases h with
  | refl => rfl
  | cloud_left _ h β hdβ =>
    rw [AllowablePerm.smul_cloudCode]
    refine cloud_left _ ?_ β hdβ
    rw [isEven_smul]
    exact h
    exact hdβ
  | cloud_right _ h β hdβ =>
    rw [AllowablePerm.smul_cloudCode]
    refine cloud_right _ ?_ β hdβ
    rw [isEven_smul]
    exact h
    exact hdβ
  | cloud_cloud c hc β hcβ γ hcγ =>
    rw [AllowablePerm.smul_cloudCode, AllowablePerm.smul_cloudCode]
    refine cloud_cloud (ρ • c) ?_ β hcβ γ hcγ
    rw [isEven_smul]
    exact hc
    exact hcγ
    exact hcβ

/-- Allowable permutations preserve code equivalence. -/
theorem smul_code : ρ • c ≡ ρ • d ↔ c ≡ d := by
  refine ⟨fun h => ?_, Equiv.smul⟩
  rw [← inv_smul_smul ρ c, ← inv_smul_smul ρ d]
  exact h.smul

end Code

end ConNF
