import Mathlib.GroupTheory.GroupAction.Sigma
import ConNF.Phase1.CodeEquiv

/-!
# Allowable permutations
-/

-- Note to whoever fixes this file: We may want to use `type_index` instead of `Λ` in some places
-- now that supports are defined in these cases.
open Function Set WithBot

open scoped Pointwise

noncomputable section

universe u

namespace ConNF

variable [Params.{u}] (α : Λ) [CoreTangleCumul α] (β : IioBot α) (γ : Iio α)

open Code

/-- A semi-allowable permutation is a `-1`-allowable permutation of atoms (a near-litter
permutation) together with allowable permutations on all `γ < β`. This forms a group structure
automatically. -/
def SemiallowablePerm : Type u :=
  ∀ β : IioBot α, Allowable β

instance : Group (SemiallowablePerm α) := Pi.group

namespace SemiallowablePerm

variable {α}
variable (π : SemiallowablePerm α) (c : Code α)

/-- The allowable permutation at a lower level corresponding to a semi-allowable permutation. -/
noncomputable def toAllowable : SemiallowablePerm α →* Allowable β
    where
  toFun f := f β
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Reinterpret a semi-allowable permutation as a structural permutation. -/
noncomputable def toStructPerm : SemiallowablePerm α →* StructPerm α
    where
  toFun f := StructPerm.toCoe fun β hβ => Allowable.toStructPerm (f ⟨β, hβ⟩)
  map_one' :=
    StructPerm.ofCoe.injective <|
      funext fun β =>
        funext fun hβ =>
          match β, hβ with
          | ⊥, _ => by
            simp only [StructPerm.ofCoe_toCoe, StructPerm.ofCoe_one, Pi.one_apply]
            exact StructPerm.toBot_one
          | (β : Λ), (hβ : (β : TypeIndex) < α) => by
            simp only [StructPerm.ofCoe_toCoe, StructPerm.ofCoe_one, Pi.one_apply]
            exact (Allowable.toStructPerm (α := show IioBot α from ⟨β, hβ⟩)).map_one
  map_mul' f g :=
    StructPerm.ofCoe.injective <|
      funext fun β =>
        funext fun hβ =>
          match β, hβ with
          | ⊥, _ => by
            simp only [StructPerm.ofCoe_toCoe, StructPerm.ofCoe_mul, Pi.mul_apply]
            exact StructPerm.toBot_mul _ _
          | (β : Λ), (hβ : (β : TypeIndex) < α) => by
            simp only [StructPerm.ofCoe_toCoe, StructPerm.ofCoe_mul, Pi.mul_apply]
            exact (Allowable.toStructPerm (α := show IioBot α from ⟨β, hβ⟩)).map_mul _ _

section

variable {X : Type _} [MulAction (StructPerm α) X]

instance mulActionOfStructPerm : MulAction (SemiallowablePerm α) X :=
  MulAction.compHom _ toStructPerm

@[simp]
theorem toStructPerm_smul (f : SemiallowablePerm α) (x : X) :
    SemiallowablePerm.toStructPerm f • x = f • x :=
  rfl

end

instance mulActionTangle : MulAction (SemiallowablePerm α) (Tangle β) :=
  MulAction.compHom _ <| toAllowable β

instance mulActionTangle' {β : Iio α} : MulAction (SemiallowablePerm α) (Tangle β) :=
  show MulAction (SemiallowablePerm α) (Tangle <| iioCoe β) from inferInstance

instance mulActionTangle'' : MulAction (SemiallowablePerm α) (Tangle (γ : Λ)) :=
  show MulAction (SemiallowablePerm α) (Tangle <| iioCoe γ) from inferInstance

@[simp]
theorem toAllowable_smul (f : SemiallowablePerm α) (t : Tangle β) : toAllowable β f • t = f • t :=
  rfl

instance : MulAction (SemiallowablePerm α) (Code α)
    where
  smul π c := ⟨c.1, π • c.2⟩
  one_smul _ := Sigma.ext rfl (heq_of_eq (one_smul _ _))
  mul_smul _ _ _ := Sigma.ext rfl (heq_of_eq (mul_smul _ _ _))

@[simp]
theorem fst_smul_nearLitter (π : SemiallowablePerm α) (N : NearLitter) : (π • N).1 = π • N.1 :=
  rfl

@[simp]
theorem snd_smul_nearLitter (π : SemiallowablePerm α) (N : NearLitter) :
    ((π • N).2 : Set Atom) = π • (N.2 : Set Atom) :=
  rfl

@[simp]
theorem fst_smul : (π • c).1 = c.1 :=
  rfl

@[simp]
theorem snd_smul : (π • c).2 = π • c.2 :=
  rfl

@[simp]
theorem smul_mk (f : SemiallowablePerm α) (γ s) : f • (mk γ s : Code α) = mk γ (f • s) :=
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

/-- An allowable permutation is a semi-allowable permutation whose action on codes preserves
equivalence. -/
def AllowablePerm :=
  { π : SemiallowablePerm α // ∀ X Y : Code α, π • X ≡ π • Y ↔ X ≡ Y }

variable {α}
variable {f : AllowablePerm α} {c d : Code α}

namespace AllowablePerm

instance : CoeTC (AllowablePerm α) (SemiallowablePerm α)
    where
  coe := Subtype.val

theorem coe_injective : Injective (Subtype.val : AllowablePerm α → SemiallowablePerm α) :=
  Subtype.coe_injective

instance : One (AllowablePerm α) :=
  ⟨⟨1, fun _ _ => by simp_rw [one_smul]⟩⟩

instance : Inv (AllowablePerm α) :=
  ⟨fun f => ⟨f⁻¹, fun c d => by rw [← f.prop, smul_inv_smul, smul_inv_smul]⟩⟩

instance : Mul (AllowablePerm α) :=
  ⟨fun f g => ⟨f * g, fun c d => by simp_rw [mul_smul, f.prop, g.prop]⟩⟩

instance : Div (AllowablePerm α) :=
  ⟨fun f g => ⟨f / g, by simp_rw [div_eq_mul_inv]; exact (f * g⁻¹).2⟩⟩

instance : Pow (AllowablePerm α) ℕ :=
  ⟨fun f n =>
    ⟨(f : SemiallowablePerm α) ^ n, by
      induction' n with d hd
      · simp_rw [pow_zero]
        exact (1 : AllowablePerm α).2
      · simp_rw [pow_succ]
        exact (f * ⟨(f : SemiallowablePerm α) ^ d, hd⟩).2⟩⟩

instance : Pow (AllowablePerm α) ℤ :=
  ⟨fun f n =>
    ⟨(f : SemiallowablePerm α) ^ n, by
      obtain (n | n) := n
      · simp_rw [Int.ofNat_eq_coe, zpow_coe_nat]
        exact (f ^ n).2
      · simp_rw [zpow_negSucc]
        exact (f ^ (n + 1))⁻¹.2⟩⟩

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

instance : Group (AllowablePerm α) :=
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
def toStructPerm : AllowablePerm α →* StructPerm α :=
  SemiallowablePerm.toStructPerm.comp coeHom

section

variable {X : Type _} [MulAction (SemiallowablePerm α) X]

instance mulActionOfSemiallowablePerm : MulAction (AllowablePerm α) X :=
  MulAction.compHom _ coeHom

@[simp]
theorem coe_smul (f : AllowablePerm α) (x : X) : (f : SemiallowablePerm α) • x = f • x :=
  rfl

end

@[simp]
theorem fst_smul_nearLitter (f : AllowablePerm α) (N : NearLitter) : (f • N).1 = f • N.1 :=
  rfl

@[simp]
theorem snd_smul_nearLitter (f : AllowablePerm α) (N : NearLitter) :
    ((f • N).2 : Set Atom) = f • (N.2 : Set Atom) :=
  rfl

@[simp]
theorem smul_typedNearLitter (f : AllowablePerm α) (N : NearLitter) :
    f • (typedNearLitter N : Tangle (γ : Λ)) = typedNearLitter ((f : SemiallowablePerm α) γ • N) :=
  Allowable.smul_typedNearLitter _ _

@[simp]
theorem fst_smul (f : AllowablePerm α) (c : Code α) : (f • c).1 = c.1 :=
  rfl

@[simp]
theorem snd_smul (f : AllowablePerm α) (c : Code α) : (f • c).2 = f • c.2 :=
  rfl

@[simp]
theorem smul_mk (f : AllowablePerm α) (γ s) : f • (mk γ s : Code α) = mk γ (f • s) :=
  rfl

theorem ConNF.Code.Equiv.smul : c ≡ d → f • c ≡ f • d :=
  (f.2 _ _).2

end AllowablePerm

namespace AllowablePerm

variable {β γ}

theorem smul_fMap (hβγ : β ≠ γ) (π : AllowablePerm α) (t : Tangle β) :
    (π : SemiallowablePerm α) γ • fMap (coe_ne hβγ) t = fMap (coe_ne hβγ) (π • t) := by
  classical
  have h := Code.Equiv.singleton hβγ t
  rw [← π.prop] at h
  simp only [recBotCoe_coe, image_smul, smul_set_singleton] at h
  simp only [Code.Equiv_iff] at h
  obtain a | ⟨_, ε, _, hA⟩ | ⟨_, ε, hε, hA⟩ | ⟨c, _, ε, hε, ζ, _, h₁, h₂⟩ := h
  · cases hβγ.symm (congr_arg Sigma.fst a)
  · simp_rw [SemiallowablePerm.smul_mk, smul_set_singleton] at hA
    exfalso
    refine aMapCode_ne_singleton ?_ hA.symm
    exact hβγ.symm
  · have := congr_arg Sigma.fst hA
    simp only [coe_smul, smul_mk, fst_mk, smul_set_singleton, ne_eq, fst_aMapCode, Subtype.mk.injEq,
      coe_inj, Subtype.coe_inj] at this
    cases this
    simp only [SemiallowablePerm.smul_mk, aMapCode_ne _ (mk β _) hβγ, mk_inj] at hA
    simp only [coe_smul, snd_mk, smul_set_singleton, aMap_singleton] at hA
    simp only [← image_smul, image_image, smul_typedNearLitter] at hA
    rw [← image_image] at hA
    rw [image_eq_image typedNearLitter.injective] at hA
    have := Litter.toNearLitter_mem_localCardinal (fMap (coe_ne hβγ) (π • t))
    rw [← hA] at this
    obtain ⟨N, hN₁, hN₂⟩ := this
    have := congr_arg Sigma.fst hN₂
    simp only [Litter.toNearLitter_fst] at this
    rw [← Allowable.toStructPerm_smul, StructPerm.smul_nearLitter_fst,
      Allowable.toStructPerm_smul] at this
    rw [mem_localCardinal] at hN₁
    rw [hN₁] at this
    exact this
  · have := congr_arg Sigma.fst h₁
    simp only [coe_smul, smul_mk, fst_mk, fst_aMapCode] at this
    subst this
    simp only [coe_smul, smul_mk, smul_set_singleton] at h₁
    cases aMapCode_ne_singleton hε h₁.symm

theorem smul_aMap (π : AllowablePerm α) (s : Set (Tangle β)) (hβγ : β ≠ γ) :
    π • aMap hβγ s = aMap hβγ (π • s) := by
  ext t
  simp only [aMap, mem_image, mem_iUnion, mem_localCardinal, exists_prop, ← image_smul]
  simp_rw [exists_exists_and_eq_and]
  constructor
  · rintro ⟨N, ⟨t, ht₁, ht₂⟩, rfl⟩
    refine ⟨(π : SemiallowablePerm α) γ • N, ⟨t, ht₁, ?_⟩, ?_⟩
    · rw [← smul_fMap hβγ, Allowable.smul_fst, ht₂]
    · rw [smul_typedNearLitter]
  · rintro ⟨N, ⟨t, ht₁, ht₂⟩, rfl⟩
    refine ⟨((π : SemiallowablePerm α) γ)⁻¹ • N, ⟨t, ht₁, ?_⟩, ?_⟩
    · rw [Allowable.smul_fst, ht₂, ← smul_fMap hβγ, inv_smul_smul]
    · rw [smul_typedNearLitter, smul_inv_smul]

theorem smul_aMapCode (π : AllowablePerm α) (hc : c.1 ≠ γ) :
    π • aMapCode γ c = aMapCode γ (π • c) := by
  simp only [aMapCode_ne γ c hc, smul_mk, aMapCode_ne γ (π • c) hc, fst_smul, snd_smul, mk_inj]
  rw [smul_aMap]

end AllowablePerm

theorem AMapRel.smul : c ↝ d → f • c ↝ f • d := by
  rintro ⟨γ, hγ⟩
  exact (AMapRel_iff _ _).2 ⟨_, hγ, f.smul_aMapCode hγ⟩

@[simp]
theorem smul_aMapRel : f • c ↝ f • d ↔ c ↝ d := by
  refine ⟨fun h => ?_, AMapRel.smul⟩
  rw [← inv_smul_smul f c, ← inv_smul_smul f d]
  exact h.smul

namespace Code

theorem isEven_smul_nonempty : ∀ c : NonemptyCode α, (f • c.val).IsEven ↔ c.val.IsEven
  | ⟨c, hc⟩ => by
    simp_rw [Code.IsEven_iff]
    constructor <;> intro h d hd
    · have := hd.nonempty_iff.2 hc
      have _ : AMapRel' ⟨d, this⟩ ⟨c, hc⟩ := aMapRel_coe_coe.1 hd
      exact Code.not_isEven.1 fun H =>
        (h _ hd.smul).not_isEven <| (isEven_smul_nonempty ⟨d, this⟩).2 H
    · rw [← smul_inv_smul f d] at hd ⊢
      rw [smul_aMapRel] at hd
      have := hd.nonempty_iff.2 hc
      have _ : AMapRel' ⟨_, this⟩ ⟨c, hc⟩ := aMapRel_coe_coe.1 hd
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

alias isEven_smul ↔ _ isEven.smul

alias isOdd_smul ↔ _ isOdd.smul

end Code

end ConNF
