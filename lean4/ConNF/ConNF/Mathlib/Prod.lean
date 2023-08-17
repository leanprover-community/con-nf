import Mathlib.Algebra.Group.Prod

#align_import mathlib.prod

variable {α β : Type _} [MulOneClass α] [MulOneClass β]

/-- `prod.fst` as a monoid homomorphism. -/
@[to_additive, simps]
def MonoidHom.prodFst : α × β →* α :=
  ⟨Prod.fst, rfl, fun _ _ => rfl⟩

/-- `prod.snd` as a monoid homomorphism. -/
@[to_additive, simps]
def MonoidHom.prodSnd : α × β →* β :=
  ⟨Prod.snd, rfl, fun _ _ => rfl⟩
