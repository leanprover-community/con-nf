import Mathbin.GroupTheory.GroupAction.Support
import Project.Phase0.StructPerm

#align_import phase0.support

/-!
# Supports
-/


open Cardinal Equiv MulAction Quiver

open scoped Cardinal

noncomputable section

universe u

namespace ConNf

variable [Params.{u}] {α : TypeIndex}

/-- A support condition is an atom or a near-litter together with an extended type index. -/
def SupportCondition (α : TypeIndex) : Type u :=
  Sum Atom NearLitter × ExtendedIndex α
deriving Inhabited

/-- The "identity" equivalence between `(atom ⊕ near_litter) × extended_index α` and
`support_condition α`. -/
def toCondition : Sum Atom NearLitter × ExtendedIndex α ≃ SupportCondition α :=
  Equiv.refl _

/-- The "identity" equivalence between `support_condition α` and
`(atom ⊕ near_litter) × extended_index α`. -/
def ofCondition : SupportCondition α ≃ Sum Atom NearLitter × ExtendedIndex α :=
  Equiv.refl _

/-- There are `μ` support conditions. -/
@[simp]
theorem mk_supportCondition (α : TypeIndex) : (#SupportCondition α) = (#μ) :=
  by
  simp only [support_condition, mk_prod, mk_sum, mk_atom, lift_id, mk_near_litter]
  rw [add_eq_left (κ_regular.aleph_0_le.trans κ_le_μ) le_rfl]
  exact
    mul_eq_left (κ_regular.aleph_0_le.trans κ_le_μ)
      (le_trans (mk_extended_index α) <| le_of_lt <| lt_trans Λ_lt_κ κ_lt_μ) (mk_ne_zero _)

namespace StructPerm

instance mulActionSupportCondition : MulAction (StructPerm α) (SupportCondition α)
    where
  smul π c := ⟨derivative c.snd π • c.fst, c.snd⟩
  one_smul := by rintro ⟨atoms | Ns, A⟩ <;> unfold SMul.smul <;> simp
  hMul_smul := by
    rintro π₁ π₂ ⟨atoms | Ns, A⟩ <;> unfold SMul.smul <;> rw [derivative_mul] <;> dsimp <;>
      rw [mul_smul]

instance mulActionSupportCondition' {B : LeIndex α} {β : TypeIndex} {γ : TypeIndex} {hγ : γ < β}
    (A : Path (B : TypeIndex) β) :
    MulAction (StructPerm (LtIndex.mk' hγ (B.Path.comp A) : LeIndex α).index)
      (SupportCondition γ) :=
  StructPerm.mulActionSupportCondition

instance mulActionSupportConditionLtIndex {β γ : TypeIndex} {hγ : γ < β} (A : Path α β) :
    MulAction (StructPerm (LtIndex.mk' hγ A)) (SupportCondition γ) :=
  StructPerm.mulActionSupportCondition

instance mulActionSupportConditionLtIndex' {β γ : TypeIndex} {hγ : γ < β} (A : Path α β) :
    MulAction (StructPerm (LtIndex.mk' hγ A : LeIndex α).index) (SupportCondition γ) :=
  StructPerm.mulActionSupportCondition

@[simp]
theorem smul_toCondition (π : StructPerm α) (x : Sum Atom NearLitter × ExtendedIndex α) :
    π • toCondition x = toCondition ⟨derivative x.2 π • x.1, x.2⟩ :=
  rfl

end StructPerm

variable (G : Type _) (α) {τ : Type _} [SMul G (SupportCondition α)] [SMul G τ]

structure Support (x : τ) where
  carrier : Set (SupportCondition α)
  Small : Small carrier
  Supports : Supports G carrier x

/-- An element of `τ` is *supported* if it has some support. -/
def Supported (x : τ) : Prop :=
  Nonempty <| Support α G x

instance Support.setLike (x : τ) : SetLike (Support α G x) (SupportCondition α)
    where
  coe := Support.carrier
  coe_injective' s t h := by cases s; cases t; congr

@[simp]
theorem Support.carrier_eq_coe {x : τ} {s : Support α G x} : s.carrier = s :=
  rfl

/-- There are at most `μ` supports for a given `x : τ`. -/
theorem mk_support_le (x : τ) : (#Support α G x) ≤ (#μ) :=
  by
  trans #{ s : Set μ // Small s }
  trans #{ S : Set (support_condition α) // Small S }
  · refine' ⟨⟨fun s => ⟨s.carrier, s.Small⟩, fun s t h => _⟩⟩
    simpa only [Subtype.mk_eq_mk, support.carrier_eq_coe, SetLike.coe_set_eq] using h
  · convert
      le_of_eq
        (mk_subtype_of_equiv _ (Equiv.Set.congr (cardinal.eq.mp (mk_support_condition α)).some))
    ext s
    refine' ⟨small.image, fun h => _⟩
    rw [← symm_apply_apply (Equiv.Set.congr (cardinal.eq.mp <| mk_support_condition α).some) s]
    exact h.image
  · rw [← mk_subset_mk_lt_cof μ_strong_limit.2]
    exact mk_subtype_mono fun s hs => lt_of_lt_of_le hs κ_le_μ_cof

end ConNf

