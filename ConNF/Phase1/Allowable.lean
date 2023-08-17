import ConNF.Mathlib.Prod
import Mathlib.GroupTheory.GroupAction.Sigma
import ConNF.Phase1.CodeEquiv

#align_import phase1.allowable

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

variable [Params.{u}] (α : Λ) [CoreTangleCumul α] (β : iioIndex α) (γ : Iio α)

open Code

/-- A semi-allowable permutation is a `-1`-allowable permutation of atoms (a near-litter
permutation) together with allowable permutations on all `γ < β`. This forms a group structure
automatically. -/
def SemiallowablePerm : Type u :=
  ∀ β : iioIndex α, Allowable β
deriving Group

namespace SemiallowablePerm

variable {α} (π : SemiallowablePerm α) (c : Code α)

/-- The allowable permutation at a lower level corresponding to a semi-allowable permutation. -/
noncomputable def toAllowable : SemiallowablePerm α →* Allowable β :=
  ⟨fun f => f β, rfl, fun _ _ => rfl⟩

/-- Reinterpret a semi-allowable permutation as a structural permutation. -/
noncomputable def toStructPerm : SemiallowablePerm α →* StructPerm α
    where
  toFun f := StructPerm.toCoe fun β hβ => (f ⟨β, hβ⟩).toStructPerm
  map_one' :=
    StructPerm.ofCoe.Injective <|
      funext fun β =>
        funext fun hβ =>
          match β, hβ with
          | ⊥, _ =>
            by
            simp only [struct_perm.of_coe_to_coe, struct_perm.of_coe_one, Pi.one_apply]
            exact struct_perm.to_bot_one
          | (β : Λ), (hβ : ↑β < ↑α) =>
            by
            simp only [struct_perm.of_coe_to_coe, struct_perm.of_coe_one, Pi.one_apply]
            exact allowable.to_struct_perm.map_one
  map_mul' f g :=
    StructPerm.ofCoe.Injective <|
      funext fun β =>
        funext fun hβ =>
          match β, hβ with
          | ⊥, _ =>
            by
            simp only [struct_perm.of_coe_to_coe, struct_perm.of_coe_mul, Pi.mul_apply]
            exact struct_perm.to_bot_mul _ _
          | (β : Λ), (hβ : ↑β < ↑α) =>
            by
            simp only [struct_perm.of_coe_to_coe, struct_perm.of_coe_mul, Pi.mul_apply]
            exact allowable.to_struct_perm.map_mul _ _

section

variable {X : Type _} [MulAction (StructPerm α) X]

instance mulActionOfStructPerm : MulAction (SemiallowablePerm α) X :=
  MulAction.compHom _ toStructPerm

@[simp]
theorem toStructPerm_smul (f : SemiallowablePerm α) (x : X) : f.toStructPerm • x = f • x :=
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

/- ./././Mathport/Syntax/Translate/Command.lean:43:9: unsupported derive handler mul_action[mul_action] (semiallowable_perm[con_nf.semiallowable_perm] α) -/
deriving instance
  «./././Mathport/Syntax/Translate/Command.lean:43:9: unsupported derive handler mul_action[mul_action] (semiallowable_perm[con_nf.semiallowable_perm] α)» for
  code

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
  ⟨fun π c => ⟨π • c, c.2.image _⟩⟩

@[simp, norm_cast]
theorem coe_smul (c : NonemptyCode α) : (↑(π • c) : Code α) = π • c :=
  rfl

instance mulActionNonemptyCode : MulAction (SemiallowablePerm α) (NonemptyCode α) :=
  Subtype.coe_injective.MulAction _ coe_smul

end SemiallowablePerm

variable [PositionData] [PositionedTangleCumul α] [AlmostTangleCumul α] [CoreTangleData α]

/-- An allowable permutation is a semi-allowable permutation whose action on codes preserves
equivalence. -/
def AllowablePerm :=
  { π : SemiallowablePerm α // ∀ X Y : Code α, π • X ≡ π • Y ↔ X ≡ Y }

variable {α} {f : AllowablePerm α} {c d : Code α}

namespace AllowablePerm

instance : CoeTC (AllowablePerm α) (SemiallowablePerm α) :=
  @coeBase _ _ coeSubtype

theorem coe_injective : Injective (coe : AllowablePerm α → SemiallowablePerm α) :=
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
    ⟨f ^ n, by
      induction' n with d hd
      · simp_rw [pow_zero]
        exact (1 : allowable_perm α).2
      · simp_rw [pow_succ]
        exact (f * ⟨f ^ d, hd⟩).2⟩⟩

instance : Pow (AllowablePerm α) ℤ :=
  ⟨fun f n =>
    ⟨f ^ n, by
      cases n
      · simp_rw [zpow_ofNat]
        exact (f ^ n).2
      · simp_rw [zpow_negSucc]
        exact (f ^ (n + 1))⁻¹.2⟩⟩

@[simp]
theorem coe_one : ((1 : AllowablePerm α) : SemiallowablePerm α) = 1 :=
  rfl

@[simp]
theorem coe_inv (f : AllowablePerm α) : (↑f⁻¹ : SemiallowablePerm α) = f⁻¹ :=
  rfl

@[simp]
theorem coe_hMul (f g : AllowablePerm α) : (↑(f * g) : SemiallowablePerm α) = f * g :=
  rfl

@[simp]
theorem coe_div (f g : AllowablePerm α) : (↑(f / g) : SemiallowablePerm α) = f / g :=
  rfl

@[simp]
theorem coe_pow (f : AllowablePerm α) (n : ℕ) : (↑(f ^ n) : SemiallowablePerm α) = f ^ n :=
  rfl

@[simp]
theorem coe_zpow (f : AllowablePerm α) (n : ℤ) : (↑(f ^ n) : SemiallowablePerm α) = f ^ n :=
  rfl

instance : Group (AllowablePerm α) :=
  coe_injective.Group _ coe_one coe_hMul coe_inv coe_div coe_pow coe_zpow

/-- The coercion from allowable to semi-allowable permutation as a monoid homomorphism. -/
@[simps]
noncomputable def coeHom : AllowablePerm α →* SemiallowablePerm α :=
  ⟨coe, coe_one, coe_hMul⟩

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
    ((f • N).2 : Set Atom) = f • ↑N.2 :=
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
  have equiv := code.equiv.singleton hβγ t
  rw [← π.prop] at equiv
  simp only [Subtype.val_eq_coe, rec_bot_coe_coe, image_smul, smul_set_singleton] at equiv
  simp only [code.equiv_iff] at equiv
  obtain a | ⟨heven, ε, hε, hA⟩ | ⟨heven, ε, hε, hA⟩ | ⟨c, heven, ε, hε, ζ, hζ, h₁, h₂⟩ := Equiv
  · cases hβγ.symm (congr_arg Sigma.fst a)
  · simp_rw [semiallowable_perm.smul_mk, smul_set_singleton] at hA
    cases A_map_code_ne_singleton _ hA.symm
    exact hβγ.symm
  · have := congr_arg Sigma.fst hA
    simp only [semiallowable_perm.smul_mk, fst_A_map_code, fst_mk, Iio.coe_inj] at this
    subst this
    simp only [semiallowable_perm.smul_mk, A_map_code_ne _ (mk β _) hβγ, mk_inj] at hA
    simp only [coe_smul, snd_mk, smul_set_singleton, A_map_singleton] at hA
    simp only [← image_smul, image_image, smul_typed_near_litter] at hA
    rw [← image_image] at hA
    rw [image_eq_image typed_near_litter.injective] at hA
    have := litter.to_near_litter_mem_local_cardinal (f_map (coe_ne hβγ) (π • t))
    rw [← hA] at this
    obtain ⟨N, hN₁, hN₂⟩ := this
    have := congr_arg Sigma.fst hN₂
    simp only [litter.to_near_litter_fst] at this
    rw [← allowable.to_struct_perm_smul, struct_perm.smul_near_litter_fst,
      allowable.to_struct_perm_smul] at this
    rw [mem_local_cardinal] at hN₁
    rw [hN₁] at this
    exact this
  · have := congr_arg Sigma.fst h₁
    simp only [coe_smul, smul_mk, fst_mk, fst_A_map_code] at this
    subst this
    simp only [coe_smul, smul_mk, smul_set_singleton] at h₁
    cases A_map_code_ne_singleton hε h₁.symm

theorem smul_aMap (π : AllowablePerm α) (s : Set (Tangle β)) (hβγ : β ≠ γ) :
    π • aMap hβγ s = aMap hβγ (π • s) := by
  ext
  simp only [A_map, mem_image, mem_Union, mem_local_cardinal, exists_prop, ← image_smul]
  simp only [exists_exists_and_eq_and, smul_typed_near_litter, ← smul_f_map hβγ]
  constructor
  · rintro ⟨N, ⟨y, y_mem, y_fmap⟩, rfl⟩
    refine' ⟨(π : semiallowable_perm α) γ • N, ⟨y, y_mem, _⟩, rfl⟩
    rw [← y_fmap]
    rfl
  · rintro ⟨N, ⟨y, y_mem, y_fmap⟩, rfl⟩
    refine' ⟨((π : semiallowable_perm α) γ)⁻¹ • N, ⟨y, y_mem, _⟩, _⟩
    · change _ • N.fst = _
      simp only [y_fmap, map_inv, inv_smul_eq_iff]
      rfl
    · simp only [smul_inv_smul]

theorem smul_aMapCode (π : AllowablePerm α) (hc : c.1 ≠ γ) :
    π • aMapCode γ c = aMapCode γ (π • c) := by
  simp only [A_map_code_ne γ c hc, A_map_code_ne γ (π • c) hc, smul_A_map, snd_smul, smul_mk]

end AllowablePerm

theorem AMapRel.smul : c ↝ d → f • c ↝ f • d := by rintro ⟨γ, hγ⟩;
  exact (A_map_rel_iff _ _).2 ⟨_, hγ, f.smul_A_map_code hγ⟩

@[simp]
theorem smul_aMapRel : f • c ↝ f • d ↔ c ↝ d := by refine' ⟨fun h => _, A_map_rel.smul⟩;
  rw [← inv_smul_smul f c, ← inv_smul_smul f d]; exact h.smul

namespace Code

theorem isEven_smul_nonempty : ∀ c : NonemptyCode α, (f • c.val).IsEven ↔ c.val.IsEven
  | ⟨c, hc⟩ => by
    simp_rw [code.is_even_iff]
    constructor <;> intro h d hd
    · have := hd.nonempty_iff.2 hc
      let rec : A_map_rel' ⟨d, this⟩ ⟨c, hc⟩ := A_map_rel_coe_coe.1 hd
      exact
        code.not_is_even.1 fun H =>
          (h _ hd.smul).not_isEven <| (is_even_smul_nonempty ⟨d, this⟩).2 H
    · rw [← smul_inv_smul f d] at hd ⊢
      rw [smul_A_map_rel] at hd
      have := hd.nonempty_iff.2 hc
      let rec : A_map_rel' ⟨_, this⟩ ⟨c, hc⟩ := A_map_rel_coe_coe.1 hd
      exact code.not_is_even.1 fun H => (h _ hd).not_isEven <| (is_even_smul_nonempty ⟨_, this⟩).1 H

@[simp]
theorem isEven_smul : (f • c).IsEven ↔ c.IsEven :=
  by
  cases c.2.eq_empty_or_nonempty
  · rw [is_empty.is_even_iff h, is_empty.is_even_iff]
    · rfl
    simpa [code.is_empty]
  · exact is_even_smul_nonempty ⟨c, h⟩

@[simp]
theorem isOdd_smul : (f • c).IsOdd ↔ c.IsOdd := by simp_rw [← code.not_is_even, is_even_smul]

alias is_even_smul ↔ _ is_even.smul

alias is_odd_smul ↔ _ is_odd.smul

end Code

end ConNF
