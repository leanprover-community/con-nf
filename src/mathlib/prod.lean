import algebra.group.prod

variables {α β : Type*} [mul_one_class α] [mul_one_class β]

/-- `prod.fst` as a monoid homomorphism. -/
@[to_additive, simps] def monoid_hom.prod_fst : α × β →* α := ⟨prod.fst, rfl, λ _ _, rfl⟩

/-- `prod.snd` as a monoid homomorphism. -/
@[to_additive, simps] def monoid_hom.prod_snd : α × β →* β := ⟨prod.snd, rfl, λ _ _, rfl⟩
