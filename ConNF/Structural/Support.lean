import Mathlib.GroupTheory.GroupAction.Support
import ConNF.Structural.StructPerm

/-!
# Supports

In this file, we define support conditions and supports.

## Main declarations

* `ConNF.SupportCondition`: The type of support conditions.
* `ConNF.Support`: The type of small supports made of support conditions.
-/

open Cardinal Equiv MulAction Quiver

open scoped Cardinal

universe u

namespace ConNF

variable [Params.{u}] {α : TypeIndex}

-- TODO: Make this a structure to try to make it easier to use lemmas with.
/-- A *support condition* is an extended type index together with an atom or a near-litter.
This represents an object in the base type (the atom or near-litter) together with the path
detailing how we descend from type `α` to type `⊥` by looking at elements of elements and so on
in the model. -/
@[ext]
structure SupportCondition (α : TypeIndex) : Type u
    where
  path : ExtendedIndex α
  value : Atom ⊕ NearLitter

noncomputable instance : Inhabited (SupportCondition α) :=
⟨default, Sum.inl default⟩

def supportCondition_equiv : SupportCondition α ≃ ExtendedIndex α × (Atom ⊕ NearLitter)
    where
  toFun c := ⟨c.path, c.value⟩
  invFun c := ⟨c.1, c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- There are `μ` support conditions. -/
@[simp]
theorem mk_supportCondition (α : TypeIndex) : #(SupportCondition α) = #μ := by
  rw [mk_congr supportCondition_equiv]
  simp only [SupportCondition, mk_prod, mk_sum, mk_atom, lift_id, mk_nearLitter]
  rw [add_eq_left (κ_isRegular.aleph0_le.trans κ_le_μ) le_rfl]
  exact mul_eq_right (κ_isRegular.aleph0_le.trans κ_le_μ)
    (le_trans (mk_extendedIndex α) <| le_of_lt <| lt_trans Λ_lt_κ κ_lt_μ) (mk_ne_zero _)

namespace StructPerm

variable {π π' : StructPerm α} {c : SupportCondition α}

/-- Structural permutations act on support conditions by following the derivative given in the
condition. -/
instance : MulAction (StructPerm α) (SupportCondition α)
    where
  smul π c := ⟨c.path, π c.path • c.value⟩
  one_smul := by rintro ⟨A, a | N⟩ <;> rfl
  mul_smul _ _ := by rintro ⟨A, a | N⟩ <;> rfl

/-!
We have a form of the next three lemmas for `StructPerm`, `NearLitterPerm`,
`Allowable`, and `AllowablePerm`.
-/

theorem smul_supportCondition :
    π • c = ⟨c.path, π c.path • c.value⟩ :=
  rfl

@[simp]
theorem smul_supportCondition_eq_iff :
    π • c = c ↔ π c.path • c.value = c.value := by
  obtain ⟨A, x⟩ := c
  simp only [smul_supportCondition, SupportCondition.mk.injEq, true_and]

@[simp]
theorem smul_supportCondition_eq_smul_iff :
    π • c = π' • c ↔ π c.path • c.value = π' c.path • c.value := by
  obtain ⟨A, x⟩ := c
  simp only [smul_supportCondition, SupportCondition.mk.injEq, true_and]

end StructPerm

namespace NearLitterPerm

variable {π π' : NearLitterPerm} {c : SupportCondition ⊥}

instance : MulAction NearLitterPerm (SupportCondition ⊥)
    where
  smul π c := ⟨c.path, π • c.value⟩
  one_smul := by rintro ⟨A, a | N⟩ <;> rfl
  mul_smul _ _ := by rintro ⟨A, a | N⟩ <;> rfl

theorem smul_supportCondition :
    π • c = ⟨c.path, π • c.value⟩ :=
  rfl

@[simp]
theorem smul_supportCondition_eq_iff :
    π • c = c ↔ π • c.value = c.value := by
  obtain ⟨A, x⟩ := c
  simp only [smul_supportCondition, SupportCondition.mk.injEq, true_and]

@[simp]
theorem smul_supportCondition_eq_smul_iff :
    π • c = π' • c ↔ π • c.value = π' • c.value := by
  obtain ⟨A, x⟩ := c
  simp only [smul_supportCondition, SupportCondition.mk.injEq, true_and]

end NearLitterPerm

variable (G : Type _) (α) {τ : Type _} [SMul G (SupportCondition α)] [SMul G τ]

/-- A (small) support of an object is a small set of support conditions that support it. -/
structure Support (x : τ) where
  carrier : Set (SupportCondition α)
  small : Small carrier
  supports : Supports G carrier x

/-- An element of `τ` is *supported* if it has some support. -/
def Supported (x : τ) : Prop :=
  Nonempty <| Support α G x

instance Support.setLike (x : τ) : SetLike (Support α G x) (SupportCondition α)
    where
  coe := Support.carrier
  coe_injective' s t h := by
    cases s
    cases t
    congr

@[simp]
theorem Support.carrier_eq_coe {x : τ} {s : Support α G x} : s.carrier = s :=
  rfl

/-- There are at most `μ` supports for a given `x : τ`. -/
theorem mk_support_le (x : τ) : #(Support α G x) ≤ #μ := by
  trans #{ s : Set μ // Small s }
  trans #{ S : Set (SupportCondition α) // Small S }
  · refine ⟨⟨fun s => ⟨s.carrier, s.small⟩, fun s t h => ?_⟩⟩
    simpa only [Subtype.mk_eq_mk, Support.carrier_eq_coe, SetLike.coe_set_eq] using h
  · rw [← mk_subtype_of_equiv Small (Equiv.Set.congr (Cardinal.eq.mp (mk_supportCondition α)).some)]
    exact ⟨⟨fun s => ⟨s, Small.image s.prop⟩, fun s h => by simp⟩⟩
  · rw [← mk_subset_mk_lt_cof μ_isStrongLimit.2]
    exact mk_subtype_mono fun s hs => lt_of_lt_of_le hs κ_le_μ_ord_cof

end ConNF
