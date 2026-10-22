module

public import ConNF.Background.Cardinal
public import ConNF.Mathlib.Basic.Rel

@[expose] public section

universe u

noncomputable section
open Cardinal

namespace Relation

variable {α : Type u} {r : α → α → Prop} {κ : Cardinal}

def reflTransGen₁ (r : α → α → Prop) (s : Set α) : Set α :=
  ⋃ x ∈ s, {y | r y x}

theorem card_reflTransGen₁_lt (hr : ∀ y, #{x | r x y} < κ) (hκ : κ.IsRegular)
    (s : Set α) (hs : #s < κ) :
    #(reflTransGen₁ r s) < κ := by
  rw [reflTransGen₁, card_biUnion_lt_iff_forall_of_isRegular hκ hs]
  intro x _
  exact hr x

def reflTransGenₙ (r : α → α → Prop) : ℕ → Set α → Set α :=
  Nat.iterate (reflTransGen₁ r)

theorem card_reflTransGenₙ_lt (hr : ∀ y, #{x | r x y} < κ) (hκ : κ.IsRegular)
    (s : Set α) (hs : #s < κ) (n : ℕ) :
    #(reflTransGenₙ r n s) < κ := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [reflTransGenₙ, Function.iterate_succ']
    exact card_reflTransGen₁_lt hr hκ _ ih

def reflTransGen' (r : α → α → Prop) : α → α → Prop :=
  λ x y ↦ x ∈ ⋃ n, {x | reflTransGenₙ r n {y} x}

theorem reflTransGen'_iff (r : α → α → Prop) (x y : α) :
    reflTransGen' r x y ↔ ReflTransGen r x y := by
  rw [reflTransGen', reflTransGenₙ, Set.mem_iUnion]
  unfold reflTransGen₁
  constructor
  · rintro ⟨n, hx⟩
    induction n generalizing x with
    | zero =>
      cases hx
      exact ReflTransGen.refl
    | succ n ih =>
      rw [Function.iterate_succ'] at hx
      obtain ⟨s, ⟨z, _, rfl⟩, _, ⟨hz, rfl⟩, hx⟩ := hx
      exact ReflTransGen.head hx (ih z hz)
  · intro h
    induction h using ReflTransGen.head_induction_on with
    | refl => exact ⟨0, rfl⟩
    | head hx _ ih =>
      obtain ⟨n, h⟩ := ih
      use n + 1
      rw [Function.iterate_succ']
      refine ⟨_, ⟨_, rfl⟩, _, ⟨h, rfl⟩, hx⟩

theorem card_reflTransGen_lt (hr : ∀ y, #{x | r x y} < κ)
    (hκ₁ : κ.IsRegular) (hκ₂ : ℵ₀ < κ) (y : α) :
    #{x | ReflTransGen r x y} < κ := by
  simp only [← reflTransGen'_iff, reflTransGen']
  change #(⋃ n, {x | reflTransGenₙ r n {y} x}) < κ
  suffices #(⋃ n : ULift.{u} ℕ, {x | reflTransGenₙ r n.down {y} x}) < κ by
    convert this using 3
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, ULift.exists]
  rw [card_iUnion_lt_iff_forall_of_isRegular hκ₁]
  · simp only [ULift.forall]
    apply card_reflTransGenₙ_lt hr hκ₁
    grw [mk_singleton, ← hκ₂]
    exact one_lt_aleph0
  · rw [mk_eq_aleph0]
    exact hκ₂

theorem card_transGen_lt (hr : ∀ y, #{x | r x y} < κ) (hκ₁ : κ.IsRegular) (hκ₂ : ℵ₀ < κ) (y : α) :
    #{x | TransGen r x y} < κ :=
  (mk_le_mk_of_subset (λ _ ↦ TransGen.to_reflTransGen)).trans_lt (card_reflTransGen_lt hr hκ₁ hκ₂ y)

theorem card_reflTransGen_le (hr : ∀ y, #{x | r x y} ≤ κ) (hκ : ℵ₀ ≤ κ) (y : α) :
    #{x | ReflTransGen r x y} ≤ κ := by
  have := card_reflTransGen_lt (r := r) (κ := Order.succ κ) ?_ ?_ ?_ y
  · rwa [Order.lt_succ_iff] at this
  · intro x
    rw [Order.lt_succ_iff]
    exact hr x
  · exact isRegular_succ hκ
  · rwa [Order.lt_succ_iff]

theorem card_transGen_le (hr : ∀ y, #{x | r x y} ≤ κ) (hκ : ℵ₀ ≤ κ) (y : α) :
    #{x | TransGen r x y} ≤ κ :=
  (mk_le_mk_of_subset (λ _ ↦ TransGen.to_reflTransGen)).trans (card_reflTransGen_le hr hκ y)

end Relation
