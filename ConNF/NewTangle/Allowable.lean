import Mathlib.GroupTheory.GroupAction.Sigma
import ConNF.NewTangle.CodeEquiv

/-!
# Allowable permutations
-/

-- Note to whoever fixes this file: We may want to use `type_index` instead of `Λ` in some places
-- now that supports are defined in these cases.
open Function Set WithBot

open scoped Pointwise

universe u

namespace ConNF

variable [Params.{u}] (α : Λ) [CoreTangleCumul α] (β : IioBot α) (γ : Iio α)

open Code

/-- A semi-allowable permutation is a `-1`-allowable permutation of atoms (a near-litter
permutation) together with allowable permutations on all `γ < β`. This forms a group structure
automatically. -/
def SemiallowablePerm : Type u :=
  ∀ β : IioBot α, Allowable β

noncomputable instance : Group (SemiallowablePerm α) := Pi.group

namespace SemiallowablePerm

variable {α}
variable (π : SemiallowablePerm α) (c : Code α)

/-- The allowable permutation at a lower level corresponding to a semi-allowable permutation. -/
def toAllowable : SemiallowablePerm α →* Allowable β
    where
  toFun f := f β
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem one_apply :
    (1 : SemiallowablePerm α) β = 1 :=
  rfl

@[simp]
theorem mul_apply (π π' : SemiallowablePerm α) :
    (π * π') β = π β * π' β :=
  rfl

@[simp]
theorem inv_apply :
    π⁻¹ β = (π β)⁻¹ :=
  rfl

section PathTop

variable {V : Type _} [Quiver V]

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

def pathTail {x : V} : {y : V} → (p : Quiver.Path x y) → Quiver.Path (pathTop p) y
| _, Quiver.Path.cons Quiver.Path.nil _ => Quiver.Path.nil
| _, Quiver.Path.cons (Quiver.Path.cons p e) f => (pathTail (Quiver.Path.cons p e)).cons f
| _, Quiver.Path.nil => Quiver.Path.nil

theorem pathTop_pathTail {x y : V} (p : Quiver.Path x y) (h : p.length ≠ 0) :
    p = (Quiver.Hom.toPath (pathTop_hom p h)).comp (pathTail p) := by
  induction p with
  | nil => cases h rfl
  | cons p e ih =>
    cases p with
    | nil => rfl
    | cons p e => simp_rw [ih (by simp)]; rfl

theorem ExtendedIndex.pathTop_pathTail {α : Λ} (A : ExtendedIndex α) :
    A = (Quiver.Hom.toPath (pathTop_hom A A.length_ne_zero)).comp (pathTail A) :=
  SemiallowablePerm.pathTop_pathTail A A.length_ne_zero

end PathTop

noncomputable def toStructPerm' (π : SemiallowablePerm α) : StructPerm α :=
  fun A => Allowable.toStructPerm (π ⟨pathTop A, pathTop_hom A A.length_ne_zero⟩) (pathTail A)

theorem toStructPerm'_one : (toStructPerm' 1 : StructPerm α) = 1 := by
  funext A
  rw [toStructPerm', one_apply, map_one]
  rfl

/-- Reinterpret a semi-allowable permutation as a structural permutation. -/
noncomputable def toStructPerm : SemiallowablePerm α →* StructPerm α
    where
  toFun := toStructPerm'
  map_one' := by
    funext A
    rw [toStructPerm', one_apply, map_one]
    rfl
  map_mul' f g := by
    funext A
    simp only
    rw [toStructPerm', mul_apply, map_mul]
    rfl

section

variable {X : Type _} [MulAction (StructPerm α) X]

noncomputable instance mulActionOfStructPerm : MulAction (SemiallowablePerm α) X :=
  MulAction.compHom _ toStructPerm

@[simp]
theorem toStructPerm_smul (f : SemiallowablePerm α) (x : X) :
    f • x = SemiallowablePerm.toStructPerm f • x :=
  rfl

end

instance : MulAction (SemiallowablePerm α) (Code α)
    where
  smul π c := ⟨c.1, π c.1 • c.2⟩
  one_smul _ := Sigma.ext rfl (heq_of_eq (one_smul _ _))
  mul_smul _ _ _ := Sigma.ext rfl (heq_of_eq (mul_smul _ _ _))

@[simp]
theorem fst_smul : (π • c).1 = c.1 :=
  rfl

@[simp]
theorem snd_smul : (π • c).2 = π c.1 • c.2 :=
  rfl

@[simp]
theorem smul_mk (f : SemiallowablePerm α) (γ s) : f • (mk γ s : Code α) = mk γ (f γ • s) :=
  rfl

instance hasSmulNonemptyCode : SMul (SemiallowablePerm α) (NonemptyCode α) :=
  ⟨fun π c => ⟨π • (c : Code α), c.2.image _⟩⟩

@[simp, norm_cast]
theorem coe_smul (c : NonemptyCode α) : (↑(π • c) : Code α) = π • (c : Code α) :=
  rfl

instance mulActionNonemptyCode : MulAction (SemiallowablePerm α) (NonemptyCode α) :=
  Subtype.coe_injective.mulAction _ coe_smul

end SemiallowablePerm

variable [PositionData] [PositionedTangleCumul α] [AlmostTangleCumul α] [CoreTangleData α]

def SemiallowablePerm.IsAllowable (π : SemiallowablePerm α) : Prop :=
  ∀ ⦃β : IioBot α⦄ ⦃γ : Iio α⦄ (hβγ : β ≠ γ) (t : Tangle β),
  Allowable.toStructPerm (π γ) (Quiver.Hom.toPath <| bot_lt_coe _) •
    fuzz (coe_ne hβγ) t =
  fuzz (coe_ne hβγ) (π β • t)

variable {π π' : SemiallowablePerm α}

theorem isAllowable_one : (1 : SemiallowablePerm α).IsAllowable := by
  intros β γ hβγ t
  simp only [SemiallowablePerm.one_apply, map_one, StructPerm.one_apply, one_smul]

theorem isAllowable_inv (h : π.IsAllowable) : π⁻¹.IsAllowable := by
  intros β γ hβγ t
  have := h hβγ (π⁻¹ β • t)
  simp only [SemiallowablePerm.inv_apply, smul_inv_smul] at this
  rw [← this]
  simp only [SemiallowablePerm.inv_apply, map_inv, StructPerm.inv_apply, inv_smul_smul]

theorem isAllowable_mul (h : π.IsAllowable) (h' : π'.IsAllowable) : (π * π').IsAllowable := by
  intros β γ hβγ t
  simp only [SemiallowablePerm.mul_apply, map_mul, StructPerm.mul_apply, mul_smul]
  rw [h' hβγ t, h hβγ (π' β • t)]

theorem isAllowable_div (h : π.IsAllowable) (h' : π'.IsAllowable) : (π / π').IsAllowable := by
  rw [div_eq_mul_inv]
  exact isAllowable_mul α h (isAllowable_inv α h')

theorem isAllowable_pow (h : π.IsAllowable) (n : ℕ) : (π ^ n).IsAllowable := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact isAllowable_one α
  | succ n ih =>
    rw [pow_succ]
    exact isAllowable_mul α h ih

theorem isAllowable_zpow (h : π.IsAllowable) (n : ℤ) : (π ^ n).IsAllowable := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_coe, zpow_coe_nat]
    exact isAllowable_pow α h n
  | negSucc n =>
    rw [zpow_negSucc]
    exact isAllowable_inv α (isAllowable_pow α h (n + 1))

/-- An allowable permutation is a semi-allowable permutation whose action on codes preserves
equivalence. -/
def AllowablePerm :=
  { π : SemiallowablePerm α // π.IsAllowable }

variable {α}
variable {f : AllowablePerm α} {c d : Code α}

namespace AllowablePerm

instance : CoeTC (AllowablePerm α) (SemiallowablePerm α)
    where
  coe := Subtype.val

theorem coe_injective : Injective (Subtype.val : AllowablePerm α → SemiallowablePerm α) :=
  Subtype.coe_injective

noncomputable instance : One (AllowablePerm α) :=
  ⟨⟨1, isAllowable_one α⟩⟩

noncomputable instance : Inv (AllowablePerm α) :=
  ⟨fun f => ⟨f⁻¹, isAllowable_inv α f.prop⟩⟩

noncomputable instance : Mul (AllowablePerm α) :=
  ⟨fun f g => ⟨f * g, isAllowable_mul α f.prop g.prop⟩⟩

noncomputable instance : Div (AllowablePerm α) :=
  ⟨fun f g => ⟨f / g, isAllowable_div α f.prop g.prop⟩⟩

noncomputable instance : Pow (AllowablePerm α) ℕ :=
  ⟨fun f n => ⟨(f : SemiallowablePerm α) ^ n, isAllowable_pow α f.prop n⟩⟩

noncomputable instance : Pow (AllowablePerm α) ℤ :=
  ⟨fun f n => ⟨(f : SemiallowablePerm α) ^ n, isAllowable_zpow α f.prop n⟩⟩

@[simp]
theorem coe_one : ((1 : AllowablePerm α) : SemiallowablePerm α) = 1 :=
  rfl

@[simp]
theorem coe_inv (f : AllowablePerm α) : ↑(f⁻¹) = (f : SemiallowablePerm α)⁻¹ :=
  rfl

@[simp]
theorem coe_mul (f g : AllowablePerm α) : ↑(f * g) = (f : SemiallowablePerm α) * g :=
  rfl

@[simp]
theorem coe_div (f g : AllowablePerm α) : ↑(f / g) = (f : SemiallowablePerm α) / g :=
  rfl

@[simp]
theorem coe_pow (f : AllowablePerm α) (n : ℕ) : ↑(f ^ n) = (f : SemiallowablePerm α) ^ n :=
  rfl

@[simp]
theorem coe_zpow (f : AllowablePerm α) (n : ℤ) : ↑(f ^ n) = (f : SemiallowablePerm α) ^ n :=
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

/-- The coercion from allowable to semi-allowable permutation as a monoid homomorphism. -/
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

noncomputable instance mulActionOfSemiallowablePerm : MulAction (AllowablePerm α) X :=
  MulAction.compHom _ coeHom

@[simp]
theorem coe_smul (f : AllowablePerm α) (x : X) : (f : SemiallowablePerm α) • x = f • x :=
  rfl

end

@[simp]
theorem smul_typedNearLitter (f : AllowablePerm α) (N : NearLitter) :
    f.val γ • (typedNearLitter N : Tangle (γ : Λ)) =
    typedNearLitter ((Allowable.toStructPerm ((f : SemiallowablePerm α) γ)
      (Quiver.Hom.toPath (bot_lt_coe _))) • N) :=
  Allowable.smul_typedNearLitter _ _

@[simp]
theorem fst_smul (f : AllowablePerm α) (c : Code α) : (f • c).1 = c.1 :=
  rfl

@[simp]
theorem snd_smul (f : AllowablePerm α) (c : Code α) : (f • c).2 = f.val c.1 • c.2 :=
  rfl

@[simp]
theorem smul_mk (f : AllowablePerm α) (γ s) : f • (mk γ s : Code α) = mk γ (f.val γ • s) :=
  rfl

end AllowablePerm

namespace AllowablePerm

variable {β γ}

theorem smul_cloud (π : AllowablePerm α) (s : Set (Tangle β)) (hβγ : β ≠ γ) :
    π.val γ • cloud hβγ s = cloud hβγ (π.val β • s) := by
  ext t
  simp only [cloud, mem_image, mem_iUnion, mem_localCardinal, exists_prop, ← image_smul]
  simp_rw [exists_exists_and_eq_and]
  constructor
  · rintro ⟨N, ⟨t, ht₁, ht₂⟩, rfl⟩
    refine ⟨Allowable.toStructPerm ((π : SemiallowablePerm α) γ)
        (Quiver.Hom.toPath <| bot_lt_coe _) • N, ⟨t, ht₁, ?_⟩, ?_⟩
    · rw [← π.prop hβγ, NearLitterPerm.smul_nearLitter_fst, ht₂]
    · rw [smul_typedNearLitter]
  · rintro ⟨N, ⟨t, ht₁, ht₂⟩, rfl⟩
    refine ⟨Allowable.toStructPerm ((π : SemiallowablePerm α) γ)⁻¹
        (Quiver.Hom.toPath <| bot_lt_coe _) • N, ⟨t, ht₁, ?_⟩, ?_⟩
    · rw [NearLitterPerm.smul_nearLitter_fst, ht₂, ← π.prop hβγ, map_inv,
        StructPerm.inv_apply, inv_smul_smul]
    · rw [smul_typedNearLitter, map_inv, StructPerm.inv_apply, smul_inv_smul]

theorem smul_cloudCode (π : AllowablePerm α) (hc : c.1 ≠ γ) :
    π • cloudCode γ c = cloudCode γ (π • c) := by
  simp only [cloudCode_ne γ c hc, smul_mk, cloudCode_ne γ (π • c) hc, fst_smul, snd_smul, mk_inj]
  rw [smul_cloud]

end AllowablePerm

theorem CloudRel.smul : c ↝ d → f • c ↝ f • d := by
  rintro ⟨γ, hγ⟩
  exact (CloudRel_iff _ _).2 ⟨_, hγ, f.smul_cloudCode hγ⟩

@[simp]
theorem smul_cloudRel : f • c ↝ f • d ↔ c ↝ d := by
  refine ⟨fun h => ?_, CloudRel.smul⟩
  rw [← inv_smul_smul f c, ← inv_smul_smul f d]
  exact h.smul

namespace Code

theorem isEven_smul_nonempty : ∀ c : NonemptyCode α, (f • c.val).IsEven ↔ c.val.IsEven
  | ⟨c, hc⟩ => by
    simp_rw [Code.IsEven_iff]
    constructor <;> intro h d hd
    · have := hd.nonempty_iff.2 hc
      have _ : CloudRel' ⟨d, this⟩ ⟨c, hc⟩ := cloudRel_coe_coe.1 hd
      exact Code.not_isEven.1 fun H =>
        (h _ hd.smul).not_isEven <| (isEven_smul_nonempty ⟨d, this⟩).2 H
    · rw [← smul_inv_smul f d] at hd ⊢
      rw [smul_cloudRel] at hd
      have := hd.nonempty_iff.2 hc
      have _ : CloudRel' ⟨_, this⟩ ⟨c, hc⟩ := cloudRel_coe_coe.1 hd
      exact Code.not_isEven.1 fun H =>
        (h _ hd).not_isEven <| (isEven_smul_nonempty ⟨_, this⟩).1 H
termination_by isEven_smul_nonempty c => c

@[simp]
theorem isEven_smul : (f • c).IsEven ↔ c.IsEven := by
  obtain (h | h) := c.2.eq_empty_or_nonempty
  · rw [IsEmpty.isEven_iff h, IsEmpty.isEven_iff]
    · rfl
    simpa [Code.IsEmpty]
  · exact isEven_smul_nonempty ⟨c, h⟩

@[simp]
theorem isOdd_smul : (f • c).IsOdd ↔ c.IsOdd := by simp_rw [← Code.not_isEven, isEven_smul]

alias ⟨_, isEven.smul⟩ := isEven_smul

alias ⟨_, isOdd.smul⟩ := isOdd_smul

theorem Equiv.smul : c ≡ d → f • c ≡ f • d := by
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
    refine cloud_cloud (f • c) ?_ β hcβ γ hcγ
    rw [isEven_smul]
    exact hc
    exact hcγ
    exact hcβ

theorem smul_code : f • c ≡ f • d ↔ c ≡ d := by
  refine ⟨fun h => ?_, Equiv.smul⟩
  rw [← inv_smul_smul f c, ← inv_smul_smul f d]
  exact h.smul

end Code

end ConNF
