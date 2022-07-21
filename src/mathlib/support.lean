import algebra.group.defs
import data.set.basic

variables {α β γ δ : Type*} [has_smul α γ] [has_smul β δ]

/-- A set `s` supports `c` if `a • c = c` whenever `f a • d = d` for all `d ∈ s`. -/
def supports (f : α → β) (s : set δ) (c : γ) := ∀ a, (∀ d ∈ s, f a • d = d) → a • c = c

lemma supports_mono {f : α → β} {s t : set δ} (hst : s ⊆ t) {c : γ} (hc : supports f s c) :
  supports f t c := λ a h, hc a (λ d hd, h d (hst hd))
