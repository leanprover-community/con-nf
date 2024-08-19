import Mathlib.Data.Set.Basic

namespace Relation

variable {α β : Type _} (r : α → β → Prop)

def image : Set β :=
  {y | ∃ x, r x y}

def coimage : Set α :=
  {x | ∃ y, r x y}

def imageOn (s : Set α) : Set β :=
  {y | ∃ x ∈ s, r x y}

def coimageOn (s : Set β) : Set α :=
  {x | ∃ y ∈ s, r x y}

class Injective : Prop where
  inj : ∀ ⦃x₁ x₂ y⦄, r x₁ y → r x₂ y → x₁ = x₂

class Coinjective : Prop where
  coinj : ∀ ⦃x y₁ y₂⦄, r x y₁ → r x y₂ → y₁ = y₂

class OneOne extends Injective r, Coinjective r : Prop

instance [Injective r] [Coinjective r] : OneOne r := ⟨⟩

class Permutative (r : α → α → Prop) extends OneOne r : Prop where
  image_eq_coimage : image r = coimage r

theorem coimageOn_eq_inter_coimage_iff {r : α → α → Prop} [OneOne r] (s t : Set α) :
    coimageOn r s = t ∩ coimage r ↔ s ∩ image r = imageOn r t := by
  rw [coimageOn, imageOn, coimage, image]
  simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h x
    constructor
    · rintro ⟨hx, y, hr⟩
      exact ⟨y, ((h y).mp ⟨x, hx, hr⟩).1, hr⟩
    · rintro ⟨y, hy, hr⟩
      obtain ⟨z, hz, hr'⟩ := (h y).mpr ⟨hy, x, hr⟩
      cases Coinjective.coinj hr hr'
      exact ⟨hz, y, hr⟩
  · intro h x
    constructor
    · rintro ⟨y, hy, hr⟩
      obtain ⟨z, hz, hr'⟩ := (h y).mp ⟨hy, x, hr⟩
      cases Injective.inj hr hr'
      exact ⟨hz, y, hr⟩
    · rintro ⟨hx, y, hr⟩
      exact ⟨y, ((h y).mpr ⟨x, hx, hr⟩).1, hr⟩

end Relation
