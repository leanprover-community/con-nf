import algebra.group.defs

variables {α β γ δ : Type*} [has_smul α γ] [has_smul β δ]

/-- A set `s` supports `c` if `a • c = c` whenever `f a • d = d` for all `d ∈ s`. -/
def supports (f : α → β) (s : set δ) (c : γ) := ∀ a, (∀ d ∈ s, f a • d = d) → a • c = c
