import Mathbin.Data.Set.Pointwise.Smul
import Project.Mathlib.Order

#align_import mathlib.pointwise

open scoped Pointwise

namespace Set

variable {α β : Type _}

section InvolutiveInv

variable [InvolutiveInv α] {s t : Set α}

@[simp, to_additive]
theorem inv_sUnion (S : Set (Set α)) : (⋃₀ S)⁻¹ = ⋃ s ∈ S, s⁻¹ := by
  simp_rw [← image_inv, image_sUnion]

end InvolutiveInv

section SMul

variable [SMul α β]

/-- The dilation of nonempty set `x • s` is defined as `{x • y | y ∈ s}` in locale `pointwise`. -/
@[to_additive
      "The translation of nonempty set `x +ᵥ s` is defined as `{x +ᵥ y | y ∈ s}` in\nlocale `pointwise`."]
protected def hasSmulNonempty : SMul α { s : Set β // s.Nonempty } :=
  ⟨fun a s => ⟨a • s, s.2.smul_set⟩⟩

scoped[Pointwise] attribute [instance] Set.hasVaddNonempty Set.hasSmulNonempty

@[simp, norm_cast, to_additive]
theorem coe_smul_nonempty (a : α) (s : { s : Set β // s.Nonempty }) : (↑(a • s) : Set β) = a • s :=
  rfl

@[simp, to_additive]
theorem smul_nonempty_mk (a : α) (s hs) :
    a • (⟨s, hs⟩ : { s : Set β // s.Nonempty }) = ⟨a • s, hs.smul_set⟩ :=
  rfl

end SMul

open scoped Pointwise

/-- A multiplicative action on a type `β` gives a multiplicative action on its nonempty sets. -/
@[to_additive "An additive action on a type gives an additive action on its nonempty sets."]
protected def mulActionNonempty [Monoid α] [MulAction α β] :
    MulAction α { s : Set β // s.Nonempty } :=
  Subtype.coe_injective.MulAction _ coe_smul_nonempty

scoped[Pointwise] attribute [instance] Set.addActionNonempty Set.mulActionNonempty

end Set

