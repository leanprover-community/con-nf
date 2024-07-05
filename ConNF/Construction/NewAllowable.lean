import ConNF.Mathlib.Group
import ConNF.Construction.CodeEquiv

/-!
# Allowable permutations

In this file, we define the type of allowable permutations at level `α`, assuming that they
exist for all type indices `β < α`.

## Main declarations

* `ConNF.Derivatives`: A collection of allowable permutations at every level `β < α`, which are
    the one-step derivatives of the newly defined allowable permutations at level `α`.
* `ConNF.NewAllowable`: A collection of `Derivatives` that commutes with the `fuzz` map.
* `ConNF.Code.smul_code`: Allowable permutations preserve code equivalence.
-/

open Function Set WithBot

open scoped Pointwise

universe u

namespace ConNF

variable [Params.{u}] [Level] [ModelDataLt] (β : TypeIndex) [LtLevel β] (γ : Λ) [LtLevel γ]

open Code

/-- A collection of *derivatives* is a collection of allowable permutations at every type index
`β < α`. The type of allowable permutations is a subtype of this type. -/
def Derivatives : Type u :=
  ∀ β : TypeIndex, [LtLevel β] → Allowable β

instance : Group Derivatives := Pi.group

namespace Derivatives

variable (ρ : Derivatives) (c : Code)

@[simp]
theorem one_apply :
    (1 : Derivatives) β = 1 :=
  rfl

@[simp]
theorem mul_apply (ρ ρ' : Derivatives) :
    (ρ * ρ') β = ρ β * ρ' β :=
  rfl

@[simp]
theorem inv_apply :
    ρ⁻¹ β = (ρ β)⁻¹ :=
  rfl

section PathTop

/-!
The bottom of a path can be easily manipulated with operations such as `cons`.
We now need to introduce machinery for manipulating the top of a path.
This allows us to convert collections of derivatives structural permutations, whose
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
    | cons p' e' => simp_rw [← ih (by simp)]; rfl

theorem ExtendedIndex.pathTop_pathTail {α : Λ} (A : ExtendedIndex α) :
    (Quiver.Hom.toPath (pathTop_hom A A.length_ne_zero)).comp (pathTail A) = A :=
  Derivatives.pathTop_pathTail A A.length_ne_zero

theorem cons_heq {x₁ x₂ y z : V} (p₁ : Quiver.Path x₁ y) (p₂ : Quiver.Path x₂ y) (hx : x₁ = x₂)
    (hp : HEq p₁ p₂) (e : y ⟶ z) : HEq (p₁.cons e) (p₂.cons e) := by
  cases hx
  cases eq_of_heq hp
  rfl

/-- Adding and removing a morphism from the top of a path doesn't change anything. -/
theorem pathTail_comp {x y z : V} (f : x ⟶ y) (p : Quiver.Path y z) :
    HEq (pathTail ((Quiver.Hom.toPath f).comp p)) p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    cases p with
    | nil => rfl
    | cons p' e' =>
        rw [Quiver.Path.comp_cons, Quiver.Path.comp_cons, pathTail]
        rw [Quiver.Path.comp_cons] at ih
        refine cons_heq _ _ ?_ ih _
        rw [← Quiver.Path.comp_cons, pathTop_toPath_comp]

end PathTop

instance (A : ExtendedIndex α) : LtLevel (pathTop A) where
  elim := pathTop_hom A A.length_ne_zero

/-- Convert a collection of derivatives to a structural permutation.
To work out the `A`-derivative, we extract the first morphism in the path `A` and use it to
determine which of the `β`-allowable permutations in `ρ` we will use. -/
def toStructPerm' (ρ : Derivatives) : StructPerm α :=
  fun A => Allowable.toStructPerm (ρ (pathTop A)) (pathTail A)

/-- Convert a collection of derivatives to a structural permutation. -/
def toStructPerm : Derivatives →* StructPerm α
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

theorem toStructPerm_congr (ρ : Derivatives) {β₁ β₂ : TypeIndex} [LtLevel β₁] [LtLevel β₂]
    (hβ : β₁ = β₂) {A₁ : ExtendedIndex β₁} {A₂ : ExtendedIndex β₂} (hA : HEq A₁ A₂) :
    Allowable.toStructPerm (ρ β₁) A₁ = Allowable.toStructPerm (ρ β₂) A₂ := by
  cases hβ
  cases eq_of_heq hA
  rfl

theorem toStructPerm'_injective : Function.Injective toStructPerm' := by
  intro ρ₁ ρ₂ hρ
  funext β iβ
  refine Allowable.toStructPerm_injective β ?_
  funext A
  have hβ : (β : TypeIndex) < α := iβ.elim
  have := congr_fun hρ ((Quiver.Hom.toPath hβ).comp A)
  simp only [toStructPerm',
    toStructPerm_congr _ (pathTop_toPath_comp hβ A) (pathTail_comp _ _)] at this
  exact this

theorem toStructPerm_injective : Function.Injective toStructPerm :=
  toStructPerm'_injective

theorem comp_toPath_toStructPerm
    (ρ : Derivatives) (β : TypeIndex) [i : LtLevel β] :
    Tree.comp (Quiver.Hom.toPath i.elim) (toStructPerm ρ) = Allowable.toStructPerm (ρ β) := by
  ext A : 1
  exact toStructPerm_congr ρ (pathTop_toPath_comp i.elim A) (pathTail_comp _ _)

theorem coe_apply_bot (ρ : Derivatives) :
    (ρ : Derivatives) ⊥ =
      Derivatives.toStructPerm ρ (Quiver.Hom.toPath (bot_lt_coe _)) := by
  rfl

section

variable {X : Type _} [MulAction (StructPerm α) X]

instance : MulAction (Derivatives) X :=
  MulAction.compHom _ toStructPerm

@[simp]
theorem toStructPerm_smul (ρ : Derivatives) (x : X) :
    ρ • x = Derivatives.toStructPerm ρ • x :=
  rfl

end

/-- In the same way that structural permutations act on addresses, collections of derivatives act
on codes. -/
instance : MulAction Derivatives Code
    where
  smul ρ c := ⟨c.β, ρ c.β • c.members⟩
  one_smul _ := Code.ext _ _ rfl (heq_of_eq (one_smul _ _))
  mul_smul _ _ _ := Code.ext _ _ rfl (heq_of_eq (mul_smul _ _ _))

@[simp]
theorem β_smul : (ρ • c).β = c.β :=
  rfl

@[simp]
theorem members_smul : (ρ • c).members = ρ c.1 • c.members :=
  rfl

@[simp]
theorem smul_mk (f : Derivatives) (γ : TypeIndex) [LtLevel γ] (s : Set (TSet γ)) :
    f • (mk γ s : Code) = mk γ (f γ • s) :=
  rfl

instance : SMul Derivatives NonemptyCode :=
  ⟨fun ρ c => ⟨ρ • (c : Code), c.2.image _⟩⟩

@[simp, norm_cast]
theorem coe_smul (c : NonemptyCode) : (↑(ρ • c) : Code) = ρ • (c : Code) :=
  rfl

instance : MulAction Derivatives NonemptyCode :=
  Subtype.coe_injective.mulAction _ coe_smul

end Derivatives

variable [BasePositions] [PositionedTanglesLt] [TypedObjectsLt] [PositionedObjectsLt] [ModelData α]

/-- We say that a collection of derivatives is *allowable* if its one-step derivatives commute with
the `fuzz` maps. -/
def Derivatives.IsAllowable (ρ : Derivatives) : Prop :=
  ∀ ⦃β : TypeIndex⦄ [LtLevel β] ⦃γ : Λ⦄ [LtLevel γ] (hβγ : β ≠ γ) (t : Tangle β),
  Allowable.toStructPerm (ρ γ) (Quiver.Hom.toPath <| bot_lt_coe _) • fuzz hβγ t = fuzz hβγ (ρ β • t)

variable {ρ ρ' : Derivatives}

theorem isAllowable_one : (1 : Derivatives).IsAllowable := by
  intro
  simp only [ne_eq, Derivatives.one_apply, map_one, Tree.one_apply, one_smul, implies_true]

theorem isAllowable_inv (h : ρ.IsAllowable) : ρ⁻¹.IsAllowable := by
  intros β _ γ _ hβγ t
  have := h hβγ (ρ⁻¹ β • t)
  simp only [Derivatives.inv_apply, smul_inv_smul] at this
  rw [← this]
  simp only [Derivatives.inv_apply, map_inv, Tree.inv_apply, inv_smul_smul]

theorem isAllowable_mul (h : ρ.IsAllowable) (h' : ρ'.IsAllowable) : (ρ * ρ').IsAllowable := by
  intros β _ γ _ hβγ t
  simp only [Derivatives.mul_apply, map_mul, Tree.mul_apply, mul_smul]
  rw [h' hβγ t, h hβγ (ρ' β • t)]

theorem isAllowable_div (h : ρ.IsAllowable) (h' : ρ'.IsAllowable) : (ρ / ρ').IsAllowable := by
  rw [div_eq_mul_inv]
  exact isAllowable_mul h (isAllowable_inv h')

theorem isAllowable_pow (h : ρ.IsAllowable) (n : ℕ) : (ρ ^ n).IsAllowable := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact isAllowable_one
  | succ n ih =>
    rw [pow_succ]
    exact isAllowable_mul ih h

theorem isAllowable_zpow (h : ρ.IsAllowable) (n : ℤ) : (ρ ^ n).IsAllowable := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_coe, zpow_natCast]
    exact isAllowable_pow h n
  | negSucc n =>
    rw [zpow_negSucc]
    exact isAllowable_inv (isAllowable_pow h (n + 1))

/-- An allowable permutation is a collection of derivatives that commutes with the `fuzz` maps. -/
def NewAllowable :=
  { ρ : Derivatives // ρ.IsAllowable }

variable {ρ : NewAllowable} {c d : Code}

namespace NewAllowable

instance : CoeTC NewAllowable Derivatives
    where
  coe := Subtype.val

theorem coe_injective : Injective (Subtype.val : NewAllowable → Derivatives) :=
  Subtype.coe_injective

instance : One NewAllowable :=
  ⟨⟨1, isAllowable_one⟩⟩

instance : Inv NewAllowable :=
  ⟨fun ρ => ⟨ρ⁻¹, isAllowable_inv ρ.prop⟩⟩

instance : Mul NewAllowable :=
  ⟨fun ρ ρ' => ⟨ρ * ρ', isAllowable_mul ρ.prop ρ'.prop⟩⟩

instance : Div NewAllowable :=
  ⟨fun ρ ρ' => ⟨ρ / ρ', isAllowable_div ρ.prop ρ'.prop⟩⟩

instance : Pow NewAllowable ℕ :=
  ⟨fun ρ n => ⟨ρ.val ^ n, isAllowable_pow ρ.prop n⟩⟩

instance : Pow NewAllowable ℤ :=
  ⟨fun ρ n => ⟨ρ.val ^ n, isAllowable_zpow ρ.prop n⟩⟩

@[simp]
theorem coe_one : ((1 : NewAllowable) : Derivatives) = 1 :=
  rfl

@[simp]
theorem coe_inv (ρ : NewAllowable) : ↑(ρ⁻¹) = (ρ : Derivatives)⁻¹ :=
  rfl

@[simp]
theorem coe_mul (ρ ρ' : NewAllowable) : ↑(ρ * ρ') = (ρ : Derivatives) * ρ' :=
  rfl

@[simp]
theorem coe_div (ρ ρ' : NewAllowable) : ↑(ρ / ρ') = (ρ : Derivatives) / ρ' :=
  rfl

@[simp]
theorem coe_pow (ρ : NewAllowable) (n : ℕ) : ↑(ρ ^ n) = (ρ : Derivatives) ^ n :=
  rfl

@[simp]
theorem coe_zpow (ρ : NewAllowable) (n : ℤ) : ↑(ρ ^ n) = (ρ : Derivatives) ^ n :=
  rfl

instance : Group NewAllowable :=
  coe_injective.group
    Subtype.val
    coe_one
    coe_mul
    coe_inv
    coe_div
    coe_pow
    coe_zpow

/-- The coercion from allowable permutations to their derivatives as a monoid homomorphism. -/
@[simps]
def coeHom : NewAllowable →* Derivatives
    where
  toFun := Subtype.val
  map_one' := coe_one
  map_mul' := coe_mul

/-- Turn an allowable permutation into a structural permutation. -/
def toStructPerm : NewAllowable →* StructPerm α :=
  Derivatives.toStructPerm.comp coeHom

theorem toStructPerm_injective : Function.Injective toStructPerm := by
  intro ρ₁ ρ₂ hρ
  have := Derivatives.toStructPerm_injective hρ
  simp only [coeHom_apply, Subtype.coe_inj] at this
  exact this

theorem comp_toPath_toStructPerm
    (ρ : NewAllowable) (β : TypeIndex) [i : LtLevel β] :
    Tree.comp (Quiver.Hom.toPath i.elim) (toStructPerm ρ) = Allowable.toStructPerm (ρ.val β) :=
  Derivatives.comp_toPath_toStructPerm _ _

section

variable {X : Type _} [MulAction (Derivatives) X]

instance : MulAction NewAllowable X :=
  MulAction.compHom _ coeHom

@[simp]
theorem coe_smul (ρ : NewAllowable) (x : X) : (ρ : Derivatives) • x = ρ • x :=
  rfl

end

@[simp]
theorem smul_typedNearLitter (ρ : NewAllowable) (N : NearLitter) :
    ρ.val γ • (typedNearLitter N : TSet (γ : Λ)) =
    typedNearLitter ((Allowable.toStructPerm ((ρ : Derivatives) γ)
      (Quiver.Hom.toPath (bot_lt_coe _))) • N) :=
  Allowable.smul_typedNearLitter _ _

@[simp]
theorem β_smul (ρ : NewAllowable) (c : Code) : (ρ • c).β = c.β :=
  rfl

@[simp]
theorem members_smul (ρ : NewAllowable) (c : Code) : (ρ • c).members = ρ.val c.β • c.members :=
  rfl

@[simp]
theorem smul_mk (ρ : NewAllowable) (γ : TypeIndex) [LtLevel γ] (s : Set (TSet γ)) :
    ρ • (mk γ s : Code) = mk γ (ρ.val γ • s) :=
  rfl

end NewAllowable

namespace NewAllowable

variable {β γ}

/-- Allowable permutations commute with the `cloud` map. -/
theorem smul_cloud (ρ : NewAllowable) (s : Set (TSet β)) (hβγ : β ≠ γ) :
    ρ.val γ • cloud hβγ s = cloud hβγ (ρ.val β • s) := by
  ext t
  constructor
  · rintro ⟨_, ⟨t, ht, N, hN, rfl⟩, rfl⟩
    refine ⟨ρ.val β • t, ?_,
        Allowable.toStructPerm ((ρ : Derivatives) γ)
          (Quiver.Hom.toPath (bot_lt_coe _)) • N, ?_, ?_⟩
    · rw [Tangle.smul_set_lt, smul_mem_smul_set_iff]
      exact ht
    · rw [← ρ.prop hβγ, BasePerm.smul_nearLitter_fst, hN]
    · dsimp only
      rw [smul_typedNearLitter]
  · rintro ⟨t, ht, N, hN, rfl⟩
    refine ⟨typedNearLitter ((Allowable.toStructPerm ((ρ : Derivatives) γ)
          (Quiver.Hom.toPath (bot_lt_coe _)))⁻¹ • N),
        ⟨(ρ.val β)⁻¹ • t, ?_, ?_⟩, ?_⟩
    · rw [Tangle.smul_set_lt, ← mem_smul_set_iff_inv_smul_mem]
      exact ht
    · refine ⟨(Allowable.toStructPerm ((ρ : Derivatives) γ)
        (Quiver.Hom.toPath (bot_lt_coe _)))⁻¹ • N, ?_, rfl⟩
      refine Eq.trans ?_ (ρ⁻¹.prop hβγ t)
      simp only [BasePerm.smul_nearLitter_fst, coe_inv, Derivatives.inv_apply,
        map_inv, Tree.inv_apply, smul_left_cancel_iff]
      exact hN
    · dsimp only
      rw [smul_typedNearLitter, smul_inv_smul]

/-- Allowable permutations commute with the `cloudCode` map. -/
theorem smul_cloudCode (ρ : NewAllowable) (hc : c.1 ≠ γ) :
    ρ • cloudCode γ c = cloudCode γ (ρ • c) := by
  simp only [cloudCode_ne γ c hc, smul_mk, cloudCode_ne γ (ρ • c) hc, β_smul, members_smul, mk_inj]
  rw [smul_cloud]

end NewAllowable

theorem CloudRel.smul : c ↝₀ d → ρ • c ↝₀ ρ • d := by
  rintro ⟨γ, hγ⟩
  exact (cloudRel_iff _ _).2 ⟨_, inferInstance, hγ, ρ.smul_cloudCode hγ⟩

@[simp]
theorem smul_cloudRel : ρ • c ↝₀ ρ • d ↔ c ↝₀ d := by
  refine ⟨fun h => ?_, CloudRel.smul⟩
  rw [← inv_smul_smul ρ c, ← inv_smul_smul ρ d]
  exact h.smul

namespace Code

theorem isEven_smul_nonempty : ∀ c : NonemptyCode, (ρ • c.val).IsEven ↔ c.val.IsEven
  | ⟨c, hc⟩ => by
    simp_rw [Code.isEven_iff]
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
termination_by c => c

@[simp]
theorem isEven_smul : (ρ • c).IsEven ↔ c.IsEven := by
  obtain (h | h) := c.members.eq_empty_or_nonempty
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
    rw [NewAllowable.smul_cloudCode]
    refine cloud_left _ ?_ β hdβ
    rw [isEven_smul]
    exact h
    exact hdβ
  | cloud_right _ h β hdβ =>
    rw [NewAllowable.smul_cloudCode]
    refine cloud_right _ ?_ β hdβ
    rw [isEven_smul]
    exact h
    exact hdβ
  | cloud_cloud c hc β hcβ γ hcγ =>
    rw [NewAllowable.smul_cloudCode, NewAllowable.smul_cloudCode]
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
