import Mathbin.GroupTheory.GroupAction.Sum
import Mathbin.Logic.Equiv.TransferInstance
import Project.Mathlib.GroupAction
import Project.Mathlib.Logic
import Project.Phase0.Index
import Project.Phase0.Litter
import Project.Phase0.Pretangle

#align_import phase0.struct_perm

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

namespace ConNf

variable [Params.{u}]

-- Note: perhaps should be constructed directly as *groups*, not just types.
/-- A *structural permutation* on a proper type index is defined by its derivatives,
as well as its permutation on atoms. -/
def StructPerm : ∀ α : TypeIndex, Type u
  | ⊥ => NearLitterPerm
  | (α : Λ) => ∀ β : TypeIndex, β < α → struct_perm β

namespace StructPerm

section

variable {α β : Λ} {γ : TypeIndex}

noncomputable instance : ∀ α, Inhabited (StructPerm α)
  | ⊥ => by unfold struct_perm; exact near_litter_perm.inhabited
  | (α : Λ) => by
    unfold struct_perm
    exact @Pi.inhabited _ _ fun β => @Pi.inhabited _ _ fun _ : β < ↑α => Inhabited β

theorem coe_def (α : Λ) : StructPerm ↑α = ∀ β : TypeIndex, β < α → StructPerm β := by
  unfold struct_perm

/-- The "identity" equivalence between `near_litter_perm` and `struct_perm ⊥`. -/
def toBot : NearLitterPerm ≃ StructPerm ⊥ :=
  Equiv.cast <| by unfold struct_perm

/-- The "identity" equivalence between `struct_perm ⊥` and `near_litter_perm`. -/
def ofBot : StructPerm ⊥ ≃ NearLitterPerm :=
  Equiv.cast <| by unfold struct_perm

/-- The "identity" equivalence between `Π β < α, struct_perm β` and `struct_perm α`. -/
def toCoe : (∀ β : TypeIndex, β < α → StructPerm β) ≃ StructPerm α :=
  Equiv.cast <| by unfold struct_perm

/-- The "identity" equivalence between `struct_perm α` and `Π β < α, struct_perm β`. -/
def ofCoe : StructPerm α ≃ ∀ β : TypeIndex, β < α → StructPerm β :=
  Equiv.cast <| by unfold struct_perm

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
theorem toBot_ofBot (a) : toBot (ofBot a) = a := by simp [to_bot, of_bot]

@[simp]
theorem ofBot_toBot (a) : ofBot (toBot a) = a := by simp [to_bot, of_bot]

@[simp]
theorem toCoe_ofCoe (a : StructPerm α) : toCoe (ofCoe a) = a := by simp [to_coe, of_coe]

@[simp]
theorem ofCoe_toCoe (a) : ofCoe (toCoe a : StructPerm α) = a := by simp [to_coe, of_coe]

@[simp]
theorem toBot_inj {a b} : toBot a = toBot b ↔ a = b :=
  toBot.Injective.eq_iff

@[simp]
theorem ofBot_inj {a b} : ofBot a = ofBot b ↔ a = b :=
  ofBot.Injective.eq_iff

@[simp]
theorem toCoe_inj {a b} : (toCoe a : StructPerm α) = toCoe b ↔ a = b :=
  toCoe.Injective.eq_iff

@[simp]
theorem ofCoe_inj {a b : StructPerm α} : ofCoe a = ofCoe b ↔ a = b :=
  ofCoe.Injective.eq_iff

noncomputable instance group : ∀ α, Group (StructPerm α)
  | ⊥ => ofBot.Group
  | (α : Λ) =>
    @Equiv.group _ _ ofCoe <| @Pi.group _ _ fun β => @PiProp.group _ _ fun _ : β < ↑α => Group β

/-- The isomorphism between near-litter permutations and bottom structural permutations. This holds
by definition of `struct_perm`. -/
def toBotIso : NearLitterPerm ≃* StructPerm ⊥ :=
  { toBot with
    map_mul' := fun a b => by rw [show struct_perm.group ⊥ = _ by unfold struct_perm.group];
      congr <;> simp }

@[simp]
theorem coe_toBotIso : ⇑toBotIso = toBot :=
  rfl

@[simp]
theorem coe_toBotIso_symm : ⇑toBotIso.symm = ofBot :=
  rfl

/-- The isomorphism between the product of structural permutations under `α` and `α`-structural
permutations. This holds by definition of `struct_perm`. -/
def toCoeIso (α : Λ) : (∀ β : TypeIndex, β < α → StructPerm β) ≃* StructPerm α :=
  { toCoe with
    map_mul' := fun a b => by rw [show struct_perm.group α = _ by unfold struct_perm.group];
      congr <;> simp }

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
theorem toBot_hMul (a b) : toBot (a * b) = toBot a * toBot b :=
  toBotIso.map_hMul _ _

@[simp]
theorem ofBot_hMul (a b) : ofBot (a * b) = ofBot a * ofBot b :=
  toBotIso.symm.map_hMul _ _

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
theorem toCoe_hMul (a b) : (toCoe (a * b) : StructPerm α) = toCoe a * toCoe b :=
  (toCoeIso α).map_hMul _ _

@[simp]
theorem ofCoe_hMul (a b : StructPerm α) : ofCoe (a * b) = ofCoe a * ofCoe b :=
  (toCoeIso α).symm.map_hMul _ _

end

variable {α β γ : TypeIndex}

/-- Obtains the permutations on lower types induced by a structural permutation. -/
def lower : ∀ {α β : TypeIndex}, β ≤ α → StructPerm α →* StructPerm β
  | ⊥, ⊥, hβ => MonoidHom.id _
  | ⊥, (β : Λ), hβ => (not_coe_le_bot _ hβ).elim
  | (α : Λ), β, hβ =>
    if h : β = α then by subst h; exact MonoidHom.id _
    else
      { toFun := fun f => ofCoe f _ <| hβ.lt_of_ne h
        map_one' := congr_fun₂ ofCoe_one _ _
        map_mul' := fun _ _ => congr_fun₂ (ofCoe_hMul _ _) _ _ }

@[simp]
theorem lower_self : lower le_rfl = MonoidHom.id (StructPerm α) := by cases α; · rfl;
  · exact dif_pos rfl

/-- The near-litter permutation associated to a structural permutation. -/
def toNearLitterPerm : StructPerm α →* NearLitterPerm :=
  toBotIso.symm.toMonoidHom.comp <| lower bot_le

theorem coe_toNearLitterPerm : (toNearLitterPerm : StructPerm ⊥ → NearLitterPerm) = ofBot := by
  simp [to_near_litter_perm]

/-- The derivative of a structural permutation at any lower level. -/
noncomputable def derivative : ∀ {β}, Path α β → StructPerm α →* StructPerm β
  | _, nil => MonoidHom.id _
  | γ, cons p_αγ hβγ => (lower <| le_of_lt hβγ).comp <| derivative p_αγ

/-- The derivative along the empty path does nothing. -/
@[simp]
theorem derivative_nil (π : StructPerm α) : derivative nil π = π :=
  rfl

theorem derivative_cons (π : StructPerm α) (p : Path α β) {γ : TypeIndex} (h : γ < β) :
    derivative (p.cons h) π = (derivative (Path.nil.cons h)) (derivative p π) := by
  simp only [derivative] <;> rfl

/-- The derivative map is functorial. -/
theorem derivative_derivative (π : StructPerm α) (p : Path α β) :
    ∀ {γ : TypeIndex} (q : Path β γ), derivative q (derivative p π) = derivative (p.comp q) π
  | _, nil => by simp only [derivative_nil, comp_nil]
  | γ, cons q f => by
    simp only [comp_cons, derivative, MonoidHom.coe_comp, Function.comp_apply,
      derivative_derivative]

/-- The derivative map preserves multiplication. -/
theorem derivative_hMul {β} (π₁ π₂ : StructPerm α) (A : Path (α : TypeIndex) β) :
    derivative A (π₁ * π₂) = derivative A π₁ * derivative A π₂ := by simp only [map_mul]

section

variable {X : Type _} [MulAction NearLitterPerm X]

/-- Structural permutations act on atoms. -/
instance mulActionOfNearLitterPerm : MulAction (StructPerm α) X :=
  MulAction.compHom _ toNearLitterPerm

@[simp]
theorem toNearLitterPerm_smul (f : StructPerm α) (x : X) : f.toNearLitterPerm • x = f • x :=
  rfl

/-- Needed as the previous lemma requires a `mul_action` and here we only have `has_smul`.
We could generify instances but this might cause loops. -/
@[simp]
theorem toNearLitterPerm_smul_set (f : StructPerm α) (s : Set X) : f.toNearLitterPerm • s = f • s :=
  rfl

@[simp]
theorem toBot_smul (f : NearLitterPerm) (x : X) : toBot f • x = f • x := by
  change to_near_litter_perm _ • _ = _ • _; rw [coe_to_near_litter_perm, of_bot_to_bot]

@[simp]
theorem ofBot_smul (f : StructPerm ⊥) (x : X) : ofBot f • x = f • x := by
  rw [← to_bot_smul, to_bot_of_bot]

@[simp]
theorem toBot_inv_smul (f : NearLitterPerm) (x : X) : (toBot f)⁻¹ • x = f⁻¹ • x := by
  rw [inv_smul_eq_iff, to_bot_smul, smul_inv_smul]

@[simp]
theorem ofBot_inv_smul (f : StructPerm ⊥) (x : X) : (ofBot f)⁻¹ • x = f⁻¹ • x := by
  rw [inv_smul_eq_iff, of_bot_smul, smul_inv_smul]

@[simp]
theorem derivative_bot_smul {α : Λ} (f : StructPerm α) (x : X) :
    StructPerm.derivative (nil.cons (bot_lt_coe α)) f • x = f • x :=
  rfl

theorem smul_nearLitter_fst (π : StructPerm α) (N : NearLitter) : (π • N).fst = π • N.fst :=
  rfl

end

def protoSmul : ∀ α : TypeIndex, StructPerm α → Pretangle α → Pretangle α
  | ⊥ => fun π t => Pretangle.toBot <| ofBot π • t.ofBot
  | (α : Λ) => fun π t =>
    Pretangle.toCoe fun β (hβ : β < α) => proto_smul β (ofCoe π β hβ) '' Pretangle.ofCoe t β hβ

instance hasSmulPretangle : ∀ α : TypeIndex, SMul (StructPerm α) (Pretangle α)
  | α => ⟨protoSmul α⟩

@[simp]
theorem ofBot_smul_pretangle (π : StructPerm ⊥) (t : Pretangle ⊥) :
    (π • t).ofBot = ofBot π • t.ofBot :=
  by
  dsimp [struct_perm.has_smul_pretangle]
  have : proto_smul ⊥ = fun π t => pretangle.to_bot <| of_bot π • t.ofBot
  unfold proto_smul
  rw [this]
  simp only [pretangle.of_bot_to_bot]

@[simp]
theorem toBot_smul_pretangle (π : NearLitterPerm) (t : Atom) :
    Pretangle.toBot (π • t) = toBot π • Pretangle.toBot t :=
  Pretangle.ofBot.Injective <| by
    simp_rw [of_bot_smul_pretangle, of_bot_to_bot, pretangle.of_bot_to_bot]

@[simp]
theorem ofCoe_smul_pretangle {α : Λ} (π : StructPerm α) (t : Pretangle α) :
    (π • t).ofCoe = ofCoe π • t.ofCoe :=
  by
  dsimp [struct_perm.has_smul_pretangle]
  unfold proto_smul
  simp only [pretangle.of_coe_to_coe]
  rfl

@[simp]
theorem toCoe_smul_pretangle {α : Λ} (π : ∀ β : TypeIndex, β < α → StructPerm β)
    (t : ∀ β : TypeIndex, β < α → Set (Pretangle β)) :
    Pretangle.toCoe (π • t) = toCoe π • Pretangle.toCoe t :=
  Pretangle.ofCoe.Injective <| by
    simp_rw [of_coe_smul_pretangle, of_coe_to_coe, pretangle.of_coe_to_coe]

protected theorem one_smul : ∀ (α) (t : Pretangle α), (1 : StructPerm α) • t = t
  | ⊥ => fun t => Pretangle.ofBot.Injective <| by simp
  | (α : Λ) => fun t =>
    Pretangle.ofCoe.Injective <| by ext β hβ : 2; simp [← image_smul, one_smul β, image_id']

protected theorem hMul_smul :
    ∀ (α) (π₁ π₂ : StructPerm α) (t : Pretangle α), (π₁ * π₂) • t = π₁ • π₂ • t
  | ⊥ => fun π₁ π₂ t => Pretangle.ofBot.Injective <| by simp [MulAction.hMul_smul]
  | (α : Λ) => fun π₁ π₂ t =>
    Pretangle.ofCoe.Injective <| by
      ext β hβ : 2;
      simp only [of_coe_smul_pretangle, of_coe_mul, Pi.smul_apply', Pi.mul_apply,
        PiProp.smul_apply', ← image_smul, image_image, ← mul_smul β]
      rfl

instance mulActionPretangle : MulAction (StructPerm α) (Pretangle α)
    where
  smul := (· • ·)
  one_smul := StructPerm.one_smul _
  hMul_smul := StructPerm.hMul_smul _

theorem derivative_cons_nil (α : Λ) (f : StructPerm α) (β : TypeIndex) (hβ : β < α) :
    derivative (cons nil hβ) f = ofCoe f β hβ := by unfold derivative lower; rw [dif_neg hβ.ne]; rfl

theorem ext (α : Λ) (a b : StructPerm α)
    (h : ∀ (β : TypeIndex) (hβ : β < α), derivative (cons nil hβ) a = derivative (cons nil hβ) b) :
    a = b :=
  ofCoe.Injective <| by ext β hβ; simp_rw [← derivative_cons_nil]; exact h _ _

instance : FaithfulSMul (StructPerm ⊥) Atom :=
  ⟨fun f g h => ofBot.Injective <| NearLitterPerm.ext <| eq_of_smul_eq_smul h⟩

end StructPerm

end ConNf

