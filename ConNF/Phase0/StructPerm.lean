import Mathlib.GroupTheory.GroupAction.Sum
import Mathlib.Logic.Equiv.TransferInstance
import ConNF.Mathlib.GroupAction
import ConNF.Mathlib.Logic
import ConNF.Phase0.Index
import ConNF.Phase0.NearLitterPerm
import ConNF.Phase0.Pretangle

/-!
# Structural permutations

In this file, we define the ambient groups of *structural permutations*.  These will later have
recursively-constructed subgroups of *semi-allowable* and *allowable permutations* which will act on
tangles; we define these larger ambient groups in advance in order to set up their infrastructure of
derivatives and so on independently of the recursion.
-/


open Cardinal Equiv Quiver Quiver.Path Set WithBot

open scoped Cardinal Pointwise

noncomputable section

universe u

namespace ConNF

variable [Params.{u}]

-- Note: perhaps should be constructed directly as *groups*, not just types.
/-- A *structural permutation* on a proper type index is defined by its derivatives,
as well as its permutation on atoms. -/
def StructPerm : TypeIndex → Type u
  | ⊥ => NearLitterPerm
  | (α : Λ) => ∀ β : TypeIndex, β < α → StructPerm β
termination_by StructPerm α => α

namespace StructPerm

section

variable {α β : Λ} {γ : TypeIndex}

noncomputable instance instInhabitedStructPerm : ∀ α, Inhabited (StructPerm α)
  | ⊥ => NearLitterPerm.instInhabitedNearLitterPerm
  | (α : Λ) => by
    unfold StructPerm
    exact ⟨fun β (_ : β < ↑α) => (instInhabitedStructPerm β).default⟩
termination_by instInhabitedStructPerm α => α

theorem coe_def (α : Λ) : StructPerm ↑α = ∀ β : TypeIndex, β < α → StructPerm β := by
  unfold StructPerm
  rfl

/-- The "identity" equivalence between `near_litter_perm` and `StructPerm ⊥`. -/
def toBot : NearLitterPerm ≃ StructPerm ⊥ :=
  Equiv.cast <| by unfold StructPerm; rfl

/-- The "identity" equivalence between `StructPerm ⊥` and `near_litter_perm`. -/
def ofBot : StructPerm ⊥ ≃ NearLitterPerm :=
  Equiv.cast <| by unfold StructPerm; rfl

/-- The "identity" equivalence between `Π β < α, StructPerm β` and `StructPerm α`. -/
def toCoe : (∀ β : TypeIndex, β < α → StructPerm β) ≃ StructPerm α :=
  Equiv.cast <| by unfold StructPerm; rfl

/-- The "identity" equivalence between `StructPerm α` and `Π β < α, StructPerm β`. -/
def ofCoe : StructPerm α ≃ ∀ β : TypeIndex, β < α → StructPerm β :=
  Equiv.cast <| by unfold StructPerm; rfl

@[simp]
theorem toBot_symm : toBot.symm = ofBot :=
  rfl

@[simp]
theorem ofBot_symm : ofBot.symm = toBot :=
  rfl

@[simp]
theorem toCoe_symm : toCoe.symm = (ofCoe : StructPerm α ≃ _) :=
  rfl

@[simp]
theorem ofCoe_symm : ofCoe.symm = (toCoe : _ ≃ StructPerm α) :=
  rfl

@[simp]
theorem toBot_ofBot (a) : toBot (ofBot a) = a := by simp [toBot, ofBot]

@[simp]
theorem ofBot_toBot (a) : ofBot (toBot a) = a := by simp [toBot, ofBot]

@[simp]
theorem toCoe_ofCoe (a : StructPerm α) : toCoe (ofCoe a) = a := by simp [toCoe, ofCoe]

@[simp]
theorem ofCoe_toCoe (a) : ofCoe (toCoe a : StructPerm α) = a := by simp [toCoe, ofCoe]

@[simp]
theorem toBot_inj {a b} : toBot a = toBot b ↔ a = b :=
  toBot.injective.eq_iff

@[simp]
theorem ofBot_inj {a b} : ofBot a = ofBot b ↔ a = b :=
  ofBot.injective.eq_iff

@[simp]
theorem toCoe_inj {a b} : (toCoe a : StructPerm α) = toCoe b ↔ a = b :=
  toCoe.injective.eq_iff

@[simp]
theorem ofCoe_inj {a b : StructPerm α} : ofCoe a = ofCoe b ↔ a = b :=
  ofCoe.injective.eq_iff

noncomputable instance group : ∀ α, Group (StructPerm α)
  | ⊥ => ofBot.group
  | (α : Λ) =>
    @Equiv.group _ _ ofCoe <| @Pi.group _ _ fun β => @PiProp.group _ _ fun _ : β < ↑α => group _
termination_by group α => α

/-- The isomorphism between near-litter permutations and bottom structural permutations. This holds
by definition of `StructPerm`. -/
def toBotIso : NearLitterPerm ≃* StructPerm ⊥
    where
  __ := toBot
  map_mul' := fun _ _ => rfl

@[simp]
theorem coe_toBotIso : ⇑toBotIso = toBot :=
  rfl

@[simp]
theorem coe_toBotIso_symm : ⇑toBotIso.symm = ofBot :=
  rfl

/-- The isomorphism between the product of structural permutations under `α` and `α`-structural
permutations. This holds by definition of `StructPerm`. -/
def toCoeIso (α : Λ) : (∀ β : TypeIndex, β < α → StructPerm β) ≃* StructPerm α
    where
  __ := toCoe
  map_mul' := fun a b => by
    have : StructPerm.group α = (@Equiv.group _ _ ofCoe <|
      @Pi.group _ _ fun β => @PiProp.group _ _ fun _ : β < ↑α => group _)
    · conv_lhs => unfold group
    rw [this]
    congr <;> simp

@[simp]
theorem coe_toCoeIso (α : Λ) : ⇑(toCoeIso α) = toCoe :=
  rfl

@[simp]
theorem coe_toCoeIso_symm (α : Λ) : ⇑(toCoeIso α).symm = ofCoe :=
  rfl

@[simp]
theorem toBot_one : toBot 1 = 1 :=
  toBotIso.map_one

@[simp]
theorem ofBot_one : ofBot 1 = 1 :=
  toBotIso.symm.map_one

@[simp]
theorem toBot_mul (a b) : toBot (a * b) = toBot a * toBot b :=
  toBotIso.map_mul _ _

@[simp]
theorem ofBot_mul (a b) : ofBot (a * b) = ofBot a * ofBot b :=
  toBotIso.symm.map_mul _ _

@[simp]
theorem toBot_inv (a) : toBot a⁻¹ = (toBot a)⁻¹ :=
  toBotIso.map_inv _

@[simp]
theorem ofBot_inv (a) : ofBot a⁻¹ = (ofBot a)⁻¹ :=
  toBotIso.symm.map_inv _

@[simp]
theorem toCoe_one : (toCoe 1 : StructPerm α) = 1 :=
  (toCoeIso α).map_one

@[simp]
theorem ofCoe_one : ofCoe (1 : StructPerm α) = 1 :=
  (toCoeIso α).symm.map_one

@[simp]
theorem toCoe_mul (a b) : (toCoe (a * b) : StructPerm α) = toCoe a * toCoe b :=
  (toCoeIso α).map_mul _ _

@[simp]
theorem ofCoe_mul (a b : StructPerm α) : ofCoe (a * b) = ofCoe a * ofCoe b :=
  (toCoeIso α).symm.map_mul _ _

end

variable {α β γ : TypeIndex}

/-- Obtains the permutations on lower types induced by a structural permutation. -/
def lower : ∀ {α β : TypeIndex}, β ≤ α → StructPerm α →* StructPerm β
  | ⊥, ⊥, _ => MonoidHom.id _
  | ⊥, (β : Λ), hβ => (not_coe_le_bot _ hβ).elim
  | (α : Λ), β, hβ =>
    if h : β = α then by subst h; exact MonoidHom.id _
    else
      { toFun := fun f => ofCoe f _ <| hβ.lt_of_ne h
        map_one' := congr_fun₂ ofCoe_one _ _
        map_mul' := fun _ _ => congr_fun₂ (ofCoe_mul _ _) _ _ }

@[simp]
theorem lower_self : lower le_rfl = MonoidHom.id (StructPerm α) := by
  cases α
  · rfl
  · exact dif_pos rfl

/-- The near-litter permutation associated to a structural permutation. -/
def toNearLitterPerm : StructPerm α →* NearLitterPerm :=
  toBotIso.symm.toMonoidHom.comp <| lower bot_le

theorem coe_toNearLitterPerm : (toNearLitterPerm : StructPerm ⊥ → NearLitterPerm) = ofBot := by
  simp [toNearLitterPerm]

/-- The derivative of a structural permutation at any lower level. -/
noncomputable def derivative : ∀ {β}, Path α β → StructPerm α →* StructPerm β
  | _, nil => MonoidHom.id _
  | _, cons p_αγ hβγ => (lower <| le_of_lt hβγ).comp <| derivative p_αγ

/-- The derivative along the empty path does nothing. -/
@[simp]
theorem derivative_nil (π : StructPerm α) : derivative nil π = π :=
  rfl

theorem derivative_cons (π : StructPerm α) (p : Path α β) {γ : TypeIndex} (h : γ < β) :
    derivative (p.cons h) π = (derivative (Path.nil.cons h)) (derivative p π) := by
  simp only [derivative]
  rfl

/-- The derivative map is functorial. -/
theorem derivative_derivative (π : StructPerm α) (p : Path α β) :
    ∀ {γ : TypeIndex} (q : Path β γ), derivative q (derivative p π) = derivative (p.comp q) π
  | _, nil => by simp only [derivative_nil, comp_nil]
  | γ, cons q f => by
    simp only [comp_cons, derivative, MonoidHom.coe_comp, Function.comp_apply,
      derivative_derivative]

/-- The derivative map preserves multiplication. -/
theorem derivative_mul {β} (π₁ π₂ : StructPerm α) (A : Path (α : TypeIndex) β) :
    derivative A (π₁ * π₂) = derivative A π₁ * derivative A π₂ := by simp only [map_mul]

section

variable {X : Type _} [MulAction NearLitterPerm X]

/-- Structural permutations act on atoms. -/
instance mulActionOfNearLitterPerm : MulAction (StructPerm α) X :=
  MulAction.compHom _ toNearLitterPerm

@[simp]
theorem toNearLitterPerm_smul (f : StructPerm α) (x : X) : toNearLitterPerm f • x = f • x :=
  rfl

/-- Needed as the previous lemma requires a `mul_action` and here we only have `has_smul`.
We could generify instances but this might cause loops. -/
@[simp]
theorem toNearLitterPerm_smul_set (f : StructPerm α) (s : Set X) : toNearLitterPerm f • s = f • s :=
  rfl

@[simp]
theorem toBot_smul (f : NearLitterPerm) (x : X) : toBot f • x = f • x := by
  rfl

@[simp]
theorem ofBot_smul (f : StructPerm ⊥) (x : X) : ofBot f • x = f • x := by
  rfl

@[simp]
theorem toBot_inv_smul (f : NearLitterPerm) (x : X) : (toBot f)⁻¹ • x = f⁻¹ • x := by
  rfl

@[simp]
theorem ofBot_inv_smul (f : StructPerm ⊥) (x : X) : (ofBot f)⁻¹ • x = f⁻¹ • x := by
  rfl

@[simp]
theorem derivative_bot_smul {α : Λ} (f : StructPerm α) (x : X) :
    StructPerm.derivative (nil.cons (bot_lt_coe α)) f • x = f • x :=
  rfl

theorem smul_nearLitter_fst (π : StructPerm α) (N : NearLitter) : (π • N).fst = π • N.fst :=
  rfl

end

def protoSmul : ∀ α : TypeIndex, StructPerm α → Pretangle α → Pretangle α
  | ⊥ => fun π t => Pretangle.toBot <| ofBot π • Pretangle.ofBot t
  | (α : Λ) => fun π t =>
    Pretangle.toCoe fun β (hβ : β < α) => protoSmul β (ofCoe π β hβ) '' Pretangle.ofCoe t β hβ
termination_by protoSmul α => α

instance hasSmulPretangle : ∀ α : TypeIndex, SMul (StructPerm α) (Pretangle α)
  | α => ⟨protoSmul α⟩

@[simp]
theorem ofBot_smul_pretangle (π : StructPerm ⊥) (t : Pretangle ⊥) :
    Pretangle.ofBot (π • t) = ofBot π • Pretangle.ofBot t := by
  rfl

@[simp]
theorem toBot_smul_pretangle (π : NearLitterPerm) (t : Atom) :
    Pretangle.toBot (π • t) = toBot π • Pretangle.toBot t :=
  rfl

@[simp]
theorem ofCoe_smul_pretangle {α : Λ} (π : StructPerm α) (t : Pretangle α) :
    Pretangle.ofCoe (π • t) = ofCoe π • Pretangle.ofCoe t := by
  change Pretangle.ofCoe (protoSmul α π t) = ofCoe π • Pretangle.ofCoe t
  ext β hβ : 2
  simp only [Pi.smul_apply', PiProp.smul_apply']
  unfold protoSmul
  rw [Pretangle.ofCoe_toCoe]
  rfl

@[simp]
theorem toCoe_smul_pretangle {α : Λ} (π : ∀ β : TypeIndex, β < α → StructPerm β)
    (t : ∀ β : TypeIndex, β < α → Set (Pretangle β)) :
    Pretangle.toCoe (π • t) = toCoe π • Pretangle.toCoe t :=
  Pretangle.ofCoe.injective <| by
    simp_rw [ofCoe_smul_pretangle, ofCoe_toCoe, Pretangle.ofCoe_toCoe]

protected theorem one_smul : ∀ (α) (t : Pretangle α), (1 : StructPerm α) • t = t
  | ⊥ => fun t => Pretangle.ofBot.injective <| by simp
  | (α : Λ) => fun t =>
    Pretangle.ofCoe.injective <| by
      ext β hβ : 2
      simp [← image_smul, StructPerm.one_smul β, image_id']
termination_by one_smul α => α

protected theorem mul_smul :
    ∀ (α) (π₁ π₂ : StructPerm α) (t : Pretangle α), (π₁ * π₂) • t = π₁ • π₂ • t
  | ⊥ => fun π₁ π₂ t => Pretangle.ofBot.injective <| by simp [mul_smul]
  | (α : Λ) => fun π₁ π₂ t =>
    Pretangle.ofCoe.injective <| by
      ext β hβ : 2
      simp only [ofCoe_smul_pretangle, ofCoe_mul, Pi.smul_apply', Pi.mul_apply,
        PiProp.smul_apply', ← image_smul, image_image, ← StructPerm.mul_smul β]
      rfl
termination_by mul_smul α => α

instance mulActionPretangle : MulAction (StructPerm α) (Pretangle α)
    where
  smul := (· • ·)
  one_smul := StructPerm.one_smul _
  mul_smul := StructPerm.mul_smul _

theorem derivative_cons_nil (α : Λ) (f : StructPerm α) (β : TypeIndex) (hβ : β < α) :
    derivative (cons nil hβ) f = ofCoe f β hβ := by
      unfold derivative lower
      dsimp only
      rw [dif_neg hβ.ne]
      rfl

theorem ext (α : Λ) (a b : StructPerm α)
    (h : ∀ (β : TypeIndex) (hβ : β < α), derivative (cons nil hβ) a = derivative (cons nil hβ) b) :
    a = b :=
  ofCoe.injective <| by
    ext β hβ
    simp_rw [← derivative_cons_nil]
    exact h _ _

instance : FaithfulSMul (StructPerm ⊥) Atom :=
  ⟨fun h => ofBot.injective <| NearLitterPerm.ext <| eq_of_smul_eq_smul h⟩

end StructPerm

end ConNF
