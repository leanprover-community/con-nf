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

/-- A *support condition* is an extended type index together with an atom or a near-litter.
This represents an object in the base type (the atom or near-litter) together with the path
detailing how we descend from type `α` to type `⊥` by looking at elements of elements and so on
in the model. -/
def SupportCondition (α : TypeIndex) : Type u :=
  ExtendedIndex α × (Atom ⊕ NearLitter)

noncomputable instance : Inhabited (SupportCondition α) :=
⟨default, Sum.inl default⟩

/-- There are `μ` support conditions. -/
@[simp]
theorem mk_supportCondition (α : TypeIndex) : #(SupportCondition α) = #μ := by
  simp only [SupportCondition, mk_prod, mk_sum, mk_atom, lift_id, mk_nearLitter]
  rw [add_eq_left (κ_isRegular.aleph0_le.trans κ_le_μ) le_rfl]
  exact mul_eq_right (κ_isRegular.aleph0_le.trans κ_le_μ)
    (le_trans (mk_extendedIndex α) <| le_of_lt <| lt_trans Λ_lt_κ κ_lt_μ) (mk_ne_zero _)

namespace StructPerm

/-- Structural permutations act on support conditions by following the derivative given in the
condition. -/
instance : MulAction (StructPerm α) (SupportCondition α)
    where
  smul π c := (c.fst, π c.fst • c.snd)
  one_smul := by rintro ⟨A, a | N⟩ <;> rfl
  mul_smul _ _ := by rintro ⟨A, a | N⟩ <;> rfl

instance : MulAction NearLitterPerm (SupportCondition ⊥)
    where
  smul π c := (c.fst, π • c.snd)
  one_smul := by rintro ⟨A, a | N⟩ <;> rfl
  mul_smul _ _ := by rintro ⟨A, a | N⟩ <;> rfl

theorem smul_supportCondition {π : StructPerm α} {c : SupportCondition α} :
    π • c = (c.fst, π c.fst • c.snd) :=
  rfl

@[simp]
theorem smul_supportCondition_eq_iff {π π' : StructPerm α} {c : SupportCondition α} :
    π • c = π' • c ↔ π c.fst • c.snd = π' c.fst • c.snd := by
  rw [Prod.ext_iff]
  simp only [smul_supportCondition, true_and]

@[simp]
theorem smul_supportCondition_eq_iff' {π π' : StructPerm α}
    {x y : Atom ⊕ NearLitter} {A : ExtendedIndex α} :
    π • (show SupportCondition α from (A, x)) = π' • (show SupportCondition α from (A, y)) ↔
    π A • x = π' A • y := by
  rw [Prod.ext_iff]
  simp only [smul_supportCondition, true_and]

-- The following attributes help with simplifications involving support conditions.
attribute [simp] Sum.inl.injEq
attribute [simp] Sum.inr.injEq

end StructPerm

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
