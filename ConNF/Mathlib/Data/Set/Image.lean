module

public import Mathlib.Data.Set.Image
public import Mathlib.Order.SymmDiff

public section

open scoped symmDiff

namespace Set

lemma subset_image_symmDiff {α β : Type*} {f : α → β} {s t : Set α} :
    (f '' s) ∆ (f '' t) ⊆ f '' (s ∆ t) := by
  rintro _ (⟨⟨x, hx, rfl⟩, h⟩ | ⟨⟨x, hx, rfl⟩, h⟩)
  · exact ⟨x, Or.inl ⟨hx, fun ht ↦ h ⟨x, ht, rfl⟩⟩, rfl⟩
  · exact ⟨x, Or.inr ⟨hx, fun hs ↦ h ⟨x, hs, rfl⟩⟩, rfl⟩

end Set
