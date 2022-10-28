import data.set.pointwise.basic
import mathlib.order

open_locale pointwise

namespace set
variables {α β : Type*}

section has_involutive_inv
variables [has_involutive_inv α]  {s t : set α}

@[simp, to_additive] lemma inv_sUnion (S : set (set α)) : (⋃₀ S)⁻¹ = ⋃ s ∈ S, s⁻¹ :=
by simp_rw [←image_inv, image_sUnion]

end has_involutive_inv

section has_smul
variables [has_smul α β]

/-- The dilation of nonempty set `x • s` is defined as `{x • y | y ∈ s}` in locale `pointwise`. -/
@[to_additive "The translation of nonempty set `x +ᵥ s` is defined as `{x +ᵥ y | y ∈ s}` in
locale `pointwise`."]
protected def has_smul_nonempty : has_smul α {s : set β // s.nonempty} :=
⟨λ a s, ⟨a • s, s.2.smul_set⟩⟩

localized "attribute [instance] set.has_vadd_nonempty set.has_smul_nonempty" in pointwise

@[simp, norm_cast, to_additive] lemma coe_smul_nonempty (a : α) (s : {s : set β // s.nonempty}) :
  (↑(a • s) : set β) = a • s := rfl

@[simp, to_additive] lemma smul_nonempty_mk (a : α) (s hs) :
  a • (⟨s, hs⟩ : {s : set β // s.nonempty}) = ⟨a • s, hs.smul_set⟩ := rfl

end has_smul

open_locale pointwise

/-- A multiplicative action on a type `β` gives a multiplicative action on its nonempty sets. -/
@[to_additive "An additive action on a type gives an additive action on its nonempty sets."]
protected def mul_action_nonempty [monoid α] [mul_action α β] :
  mul_action α {s : set β // s.nonempty} :=
subtype.coe_injective.mul_action _ coe_smul_nonempty

localized "attribute [instance] set.add_action_nonempty set.mul_action_nonempty" in pointwise

end set
