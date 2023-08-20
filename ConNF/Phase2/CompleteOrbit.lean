import Mathlib.SetTheory.Cardinal.Ordinal
import ConNF.Mathlib.Logic.Equiv.LocalPerm

namespace LocalPerm

/-!
Utilities to complete orbits of functions into local permutations.

Suppose we have a function `f : α → α`, and a set `s` on which `f` is injective.
We will construct a pair of functions `to_fun` and `inv_fun` that agree with `f` and its inverse
on `s`, in such a way that forms a local permutation of `α`. In particular, consider the diagram
```
... → l 2 → l 1 → l 0 → s \ f '' s → ... → f '' s \ s → r 0 → r 1 → r 2 → ...
```
To fill in orbits of `f`, we construct a sequence of disjoint subsets of `α` called `l i` and `r i`
for each `i : ℕ`, where `#(l i) = #(s \ f '' s)` and `#(r i) = #(f '' s \ s)`.
There are natural bijections along this diagram, mapping `l (n + 1)` to `l n` and `r n` to
`r (n + 1)`, and there are also bijections `f '' s \ s → r 0` and `l 0 → s \ f '' s`.
This yields a local permutation defined on `s`, `f '' s \ s`, the `l i`, and the `r i`.
-/


open Cardinal Function Set

open scoped Cardinal Classical

variable {α : Type _} {f : α → α} {s : Set α} {t : Set α} (hs : (#(s ∆ (f '' s) : Set α)) ≤ (#t))
  (ht : ℵ₀ ≤ (#t))

theorem exists_sandbox_subset (hs : (#(s ∆ (f '' s) : Set α)) ≤ (#t)) (ht : ℵ₀ ≤ (#t)) :
    #(Sum (ℕ × (s \ f '' s : Set α)) (ℕ × (f '' s \ s : Set α))) ≤ (#t) := by
  rw [Set.symmDiff_def, mk_union_of_disjoint] at hs
  simp only [mk_sum, mk_prod, mk_denumerable, lift_aleph0, lift_uzero, lift_id, ← mul_add] at hs ⊢
  exact le_trans (mul_le_max_of_aleph0_le_left le_rfl) (max_le ht hs)
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem]
  exact fun x hx => hx.1.2 hx.2.1

/-- Creates a "sandbox" subset of `t` on which we will define an extension of `f`. -/
def sandboxSubset : Set α :=
  (le_mk_iff_exists_subset.mp <| exists_sandbox_subset hs ht).choose

theorem sandboxSubset_subset : sandboxSubset hs ht ⊆ t :=
  (le_mk_iff_exists_subset.mp <| exists_sandbox_subset hs ht).choose_spec.1

noncomputable def sandboxSubsetEquiv :
    sandboxSubset hs ht ≃ Sum (ℕ × (s \ f '' s : Set α)) (ℕ × (f '' s \ s : Set α)) :=
  (Cardinal.eq.mp (le_mk_iff_exists_subset.mp <| exists_sandbox_subset hs ht).choose_spec.2).some

/-- Considered an implementation detail; use lemmas about `complete` instead. -/
noncomputable def shiftRight : Sum (ℕ × (s \ f '' s : Set α)) (ℕ × (f '' s \ s : Set α)) → α
  | Sum.inl ⟨0, a⟩ => a
  | Sum.inl ⟨n + 1, a⟩ => (sandboxSubsetEquiv hs ht).symm (Sum.inl ⟨n, a⟩)
  | Sum.inr ⟨n, a⟩ => (sandboxSubsetEquiv hs ht).symm (Sum.inr ⟨n + 1, a⟩)

/-- Considered an implementation detail; use lemmas about `complete` instead. -/
noncomputable def completeToFun (a : α) : α :=
  if h : a ∈ sandboxSubset hs ht then shiftRight hs ht (sandboxSubsetEquiv hs ht ⟨a, h⟩)
  else if h : a ∈ f '' s \ s then (sandboxSubsetEquiv hs ht).symm (Sum.inr ⟨0, a, h⟩) else f a

/-- Considered an implementation detail; use lemmas about `complete` instead. -/
noncomputable def shiftLeft : Sum (ℕ × (s \ f '' s : Set α)) (ℕ × (f '' s \ s : Set α)) → α
  | Sum.inl ⟨n, a⟩ => (sandboxSubsetEquiv hs ht).symm (Sum.inl ⟨n + 1, a⟩)
  | Sum.inr ⟨0, a⟩ => a.1
  | Sum.inr ⟨n + 1, a⟩ => (sandboxSubsetEquiv hs ht).symm (Sum.inr ⟨n, a⟩)

/-- Considered an implementation detail; use lemmas about `complete` instead. -/
noncomputable def completeInvFun [Nonempty α] (a : α) : α :=
  if h : a ∈ sandboxSubset hs ht then shiftLeft hs ht (sandboxSubsetEquiv hs ht ⟨a, h⟩)
  else
    if h : a ∈ s \ f '' s then (sandboxSubsetEquiv hs ht).symm (Sum.inl ⟨0, a, h⟩)
    else invFunOn f s a

/-- The domain on which we will define the completion of a function to a local permutation. -/
def completeDomain : Set α :=
  s ∪ f '' s ∪ sandboxSubset hs ht

theorem completeToFun_domain (x : α) (h : x ∈ completeDomain hs ht) :
    completeToFun hs ht x ∈ completeDomain hs ht := by
  unfold completeToFun completeDomain
  split_ifs with h₁ h₂
  case pos =>
    cases sandboxSubsetEquiv hs ht ⟨x, h₁⟩ with
    | inl val =>
      obtain ⟨_ | n, x⟩ := val
      · exact Or.inl (Or.inl x.prop.1)
      · exact Or.inr ((sandboxSubsetEquiv hs ht).symm _).prop
    | inr val =>
      obtain ⟨n, x⟩ := val
      exact Or.inr ((sandboxSubsetEquiv hs ht).symm _).prop
  case pos =>
    exact Or.inr ((sandboxSubsetEquiv hs ht).symm _).prop
  case neg =>
    rw [mem_diff, not_and_or, Classical.not_not] at h₂
    refine Or.inl (Or.inr ⟨x, ?_, rfl⟩)
    obtain (h₂ | h₂) := h₂
    · obtain (h | h) | h := h
      exact h
      cases h₂ h
      cases h₁ h
    · exact h₂

theorem completeInvFun_domain [Nonempty α] (x : α) (h : x ∈ completeDomain hs ht) :
    completeInvFun hs ht x ∈ completeDomain hs ht := by
  unfold completeInvFun completeDomain
  split_ifs with h₁ h₂
  case pos =>
    cases sandboxSubsetEquiv hs ht ⟨x, h₁⟩ with
    | inl val =>
      obtain ⟨n, x⟩ := val
      exact Or.inr ((sandboxSubsetEquiv hs ht).symm _).prop
    | inr val =>
      obtain ⟨_ | n, x⟩ := val
      · exact Or.inl (Or.inr x.prop.1)
      · exact Or.inr ((sandboxSubsetEquiv hs ht).symm _).prop
  case pos =>
    exact Or.inr ((sandboxSubsetEquiv hs ht).symm _).prop
  case neg =>
    rw [mem_diff, not_and_or, Classical.not_not] at h₂
    obtain (h₂ | h₂) := h₂
    · rw [completeDomain] at h
      obtain (h | h) | h := h
      cases h₂ h
      · refine Or.inl (Or.inl ?_)
        simp only [mem_image] at h
        exact invFunOn_mem h
      cases h₁ h
    simp only [mem_image] at h₂
    exact Or.inl (Or.inl (invFunOn_mem h₂))

theorem complete_left_inv [Nonempty α] (hst : Disjoint (s ∪ f '' s) t) (hf : InjOn f s) (x : α)
    (h : x ∈ completeDomain hs ht) : completeInvFun hs ht (completeToFun hs ht x) = x := by
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem] at hst
  by_cases h₁ : x ∈ s
  · rw [completeToFun, dif_neg, dif_neg, completeInvFun, dif_neg, dif_neg]
    · exact hf (invFunOn_apply_mem h₁) h₁
          (show f (invFunOn f s (f x)) = f x from invFunOn_apply_eq h₁)
    · exact fun h' => h'.2 ⟨x, h₁, rfl⟩
    · exact fun hx => hst (f x) ⟨Or.inr ⟨x, h₁, rfl⟩, sandboxSubset_subset hs ht hx⟩
    · exact fun h' => h'.2 h₁
    · exact fun hx => hst x ⟨Or.inl h₁, sandboxSubset_subset hs ht hx⟩
  by_cases h₂ : x ∈ f '' s
  · rw [completeToFun, dif_neg, dif_pos, completeInvFun, dif_pos]
    simp only [Subtype.coe_prop, Subtype.coe_eta, Equiv.apply_symm_apply]
    rfl
    · exact ((sandboxSubsetEquiv hs ht).symm _).prop
    · exact ⟨h₂, h₁⟩
    · exact fun h => hst x ⟨Or.inr h₂, sandboxSubset_subset hs ht h⟩
  obtain (h | h) | h := h
  · cases h₁ h
  · cases h₂ h
  rw [completeToFun, dif_pos h, completeInvFun]
  by_cases h₃ : ∃ a, sandboxSubsetEquiv hs ht ⟨x, h⟩ = Sum.inl ⟨0, a⟩
  · obtain ⟨a, ha⟩ := h₃
    rw [dif_neg, dif_pos, Subtype.coe_eq_iff]
    refine' ⟨h, _⟩
    simp only [ha]
    exact a.prop
    · rw [Equiv.symm_apply_eq]
      simp only [ha, Sum.inl.injEq, Prod.mk.injEq, true_and]
      ext
      rfl
    · rw [ha]
      exact fun h => hst _ ⟨Or.inl a.prop.1, sandboxSubset_subset hs ht h⟩
  have h₄ :
    (∃ n a, sandboxSubsetEquiv hs ht ⟨x, h⟩ = Sum.inl ⟨n + 1, a⟩) ∨
      ∃ n a, sandboxSubsetEquiv hs ht ⟨x, h⟩ = Sum.inr ⟨n, a⟩
  · set val := sandboxSubsetEquiv hs ht ⟨x, h⟩
    clear_value val
    obtain ⟨_ | n, b⟩ | ⟨n, b⟩ := val
    cases h₃ ⟨b, rfl⟩
    exact Or.inl ⟨n, b, rfl⟩
    exact Or.inr ⟨n, b, rfl⟩
  obtain (h₄ | h₄) := h₄ <;>
    · obtain ⟨n, a, ha⟩ := h₄
      rw [dif_pos]
      simp only [ha]
      unfold shiftRight
      simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
      exact Subtype.coe_inj.mpr ((Equiv.symm_apply_eq _).mpr ha.symm)
      rw [ha]
      exact ((sandboxSubsetEquiv hs ht).symm _).prop

theorem complete_right_inv [Nonempty α] (hst : Disjoint (s ∪ f '' s) t) (hf : InjOn f s) (x : α)
    (h : x ∈ completeDomain hs ht) : completeToFun hs ht (completeInvFun hs ht x) = x := by
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem] at hst
  by_cases h₁ : x ∈ f '' s
  · rw [completeInvFun, dif_neg, dif_neg, completeToFun, dif_neg, dif_neg]
    · exact invFunOn_eq h₁
    · exact fun h' => h'.2 (invFunOn_mem h₁)
    · exact fun hx => hst _ ⟨Or.inl (invFunOn_mem h₁), sandboxSubset_subset hs ht hx⟩
    · exact fun h' => h'.2 h₁
    · exact fun hx => hst x ⟨Or.inr h₁, sandboxSubset_subset hs ht hx⟩
  by_cases h₂ : x ∈ s
  · rw [completeInvFun, dif_neg, dif_pos, completeToFun, dif_pos]
    simp only [Subtype.coe_prop, Subtype.coe_eta, Equiv.apply_symm_apply]
    rfl
    · exact ((sandboxSubsetEquiv hs ht).symm _).prop
    · exact ⟨h₂, h₁⟩
    · exact fun h => hst x ⟨Or.inl h₂, sandboxSubset_subset hs ht h⟩
  obtain (h | h) | h := h
  · cases h₂ h
  · cases h₁ h
  rw [completeInvFun, dif_pos h, completeToFun]
  by_cases h₃ : ∃ a, sandboxSubsetEquiv hs ht ⟨x, h⟩ = Sum.inr ⟨0, a⟩
  · obtain ⟨a, ha⟩ := h₃
    rw [dif_neg, dif_pos, Subtype.coe_eq_iff]
    refine' ⟨h, _⟩
    simp only [ha]
    exact a.prop
    · rw [Equiv.symm_apply_eq]
      simp only [ha, Sum.inr.injEq, Prod.mk.injEq, true_and]
      ext
      rfl
    · rw [ha]
      exact fun h => hst _ ⟨Or.inr a.prop.1, sandboxSubset_subset hs ht h⟩
  have h₄ :
    (∃ n a, sandboxSubsetEquiv hs ht ⟨x, h⟩ = Sum.inr ⟨n + 1, a⟩) ∨
      ∃ n a, sandboxSubsetEquiv hs ht ⟨x, h⟩ = Sum.inl ⟨n, a⟩
  · set val := sandboxSubsetEquiv hs ht ⟨x, h⟩
    clear_value val
    obtain ⟨n, b⟩ | ⟨_ | n, b⟩ := val
    exact Or.inr ⟨n, b, rfl⟩
    cases h₃ ⟨b, rfl⟩
    exact Or.inl ⟨n, b, rfl⟩
  obtain (h₄ | h₄) := h₄ <;>
    · obtain ⟨n, a, ha⟩ := h₄
      rw [dif_pos]
      simp only [ha]
      unfold shiftLeft
      simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
      exact Subtype.coe_inj.mpr ((Equiv.symm_apply_eq _).mpr ha.symm)
      rw [ha]
      exact ((sandboxSubsetEquiv hs ht).symm _).prop

/-- Completes a function `f` on a domain `s` into a local permutation that agrees with `f` on `s`,
with domain contained in `s ∪ (f '' s) ∪ t`. -/
noncomputable def complete [Nonempty α] (f : α → α) (s : Set α) (t : Set α)
    (hs : (#(s ∆ (f '' s) : Set α)) ≤ (#t)) (ht : ℵ₀ ≤ (#t)) (hst : Disjoint (s ∪ f '' s) t)
    (hf : InjOn f s) : LocalPerm α
    where
  toFun := completeToFun hs ht
  invFun := completeInvFun hs ht
  domain := completeDomain hs ht
  toFun_domain' := completeToFun_domain hs ht
  invFun_domain' := completeInvFun_domain hs ht
  left_inv' := complete_left_inv hs ht hst hf
  right_inv' := complete_right_inv hs ht hst hf

variable [Nonempty α] {hst : Disjoint (s ∪ f '' s) t} {hf : InjOn f s}

@[simp]
theorem completeDomain_eq : (complete f s t hs ht hst hf).domain = completeDomain hs ht :=
  rfl

theorem mem_completeDomain_of_mem (x : α) (hx : x ∈ s) : x ∈ completeDomain hs ht :=
  Or.inl (Or.inl hx)

theorem mem_completeDomain_of_mem_image (x : α) (hx : x ∈ f '' s) : x ∈ completeDomain hs ht :=
  Or.inl (Or.inr hx)

theorem not_mem_sandbox_of_mem (hst : Disjoint (s ∪ f '' s) t) (x : α) (hx : x ∈ s) :
    x ∉ sandboxSubset hs ht := by
  intro h
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem] at hst
  exact hst x ⟨Or.inl hx, sandboxSubset_subset hs ht h⟩

theorem not_mem_sandbox_of_mem_image (hst : Disjoint (s ∪ f '' s) t) (x : α) (hx : x ∈ f '' s) :
    x ∉ sandboxSubset hs ht := by
  intro h
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem] at hst
  exact hst x ⟨Or.inr hx, sandboxSubset_subset hs ht h⟩

@[simp]
theorem complete_apply_eq (x : α) (hx : x ∈ s) : complete f s t hs ht hst hf x = f x := by
  rw [complete, coe_mk, completeToFun, dif_neg, dif_neg]
  exact fun h' => h'.2 hx
  exact not_mem_sandbox_of_mem hs ht hst x hx

end LocalPerm
