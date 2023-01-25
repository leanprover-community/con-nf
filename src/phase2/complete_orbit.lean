import set_theory.cardinal.ordinal
import phase2.local_perm

namespace local_perm

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

open cardinal function set
open_locale cardinal classical

variables {α : Type*} {f : α → α} {s : set α} {t : set α}
  (hs : #(s ∆ (f '' s) : set α) ≤ #t) (ht : ℵ₀ ≤ #t)

lemma exists_sandbox_subset (hs : #(s ∆ (f '' s) : set α) ≤ #t) (ht : ℵ₀ ≤ #t) :
  #((ℕ × (s \ f '' s : set α)) ⊕ (ℕ × (f '' s \ s : set α))) ≤ #t :=
begin
  rw [set.symm_diff_def, mk_union_of_disjoint] at hs,
  simp only [mk_sum, mk_prod, mk_denumerable, lift_aleph_0, lift_uzero, lift_id, ← mul_add] at hs ⊢,
  exact le_trans (mul_le_max_of_aleph_0_le_left le_rfl) (max_le ht hs),
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem],
  exact λ x hx, hx.1.2 hx.2.1,
end

/-- Creates a "sandbox" subset of `t` on which we will define an extension of `f`. -/
def sandbox_subset : set α :=
(le_mk_iff_exists_subset.mp $ exists_sandbox_subset hs ht).some

lemma sandbox_subset_subset : sandbox_subset hs ht ⊆ t :=
(le_mk_iff_exists_subset.mp $ exists_sandbox_subset hs ht).some_spec.1

noncomputable def sandbox_subset_equiv :
  sandbox_subset hs ht ≃ (ℕ × (s \ f '' s : set α)) ⊕ (ℕ × (f '' s \ s : set α)) :=
(cardinal.eq.mp (le_mk_iff_exists_subset.mp $ exists_sandbox_subset hs ht).some_spec.2).some

/-- Considered an implementation detail; use lemmas about `complete` instead. -/
noncomputable def shift_right : (ℕ × (s \ f '' s : set α)) ⊕ (ℕ × (f '' s \ s : set α)) → α
| (sum.inl ⟨0, a⟩) := a
| (sum.inl ⟨n + 1, a⟩) := (sandbox_subset_equiv hs ht).symm (sum.inl ⟨n, a⟩)
| (sum.inr ⟨n, a⟩) := (sandbox_subset_equiv hs ht).symm (sum.inr ⟨n + 1, a⟩)

/-- Considered an implementation detail; use lemmas about `complete` instead. -/
noncomputable def complete_to_fun (a : α) : α :=
if h : a ∈ sandbox_subset hs ht then
  shift_right hs ht (sandbox_subset_equiv hs ht ⟨a, h⟩)
else if h : a ∈ f '' s \ s then
  (sandbox_subset_equiv hs ht).symm (sum.inr ⟨0, a, h⟩)
else
  f a

/-- Considered an implementation detail; use lemmas about `complete` instead. -/
noncomputable def shift_left : (ℕ × (s \ f '' s : set α)) ⊕ (ℕ × (f '' s \ s : set α)) → α
| (sum.inl ⟨n, a⟩) := (sandbox_subset_equiv hs ht).symm (sum.inl ⟨n + 1, a⟩)
| (sum.inr ⟨0, a⟩) := a.1
| (sum.inr ⟨n + 1, a⟩) := (sandbox_subset_equiv hs ht).symm (sum.inr ⟨n, a⟩)

/-- Considered an implementation detail; use lemmas about `complete` instead. -/
noncomputable def complete_inv_fun [nonempty α] (a : α) : α :=
if h : a ∈ sandbox_subset hs ht then
  shift_left hs ht (sandbox_subset_equiv hs ht ⟨a, h⟩)
else if h : a ∈ s \ f '' s then
  (sandbox_subset_equiv hs ht).symm (sum.inl ⟨0, a, h⟩)
else
  inv_fun_on f s a

/-- The domain on which we will define the completion of a function to a local permutation. -/
def complete_domain : set α :=
s ∪ f '' s ∪ sandbox_subset hs ht

lemma complete_to_fun_domain (x : α) (h : x ∈ complete_domain hs ht) :
  complete_to_fun hs ht x ∈ complete_domain hs ht :=
begin
  unfold complete_to_fun complete_domain,
  split_ifs with h₁ h₂,
  cases sandbox_subset_equiv hs ht ⟨x, h₁⟩,
  { obtain ⟨_ | n, x⟩ := val,
    { exact or.inl (or.inl x.prop.1), },
    { exact or.inr ((sandbox_subset_equiv hs ht).symm _).prop, }, },
  { obtain ⟨n, x⟩ := val,
    exact or.inr ((sandbox_subset_equiv hs ht).symm _).prop, },
  { exact or.inr ((sandbox_subset_equiv hs ht).symm _).prop, },
  { rw [mem_diff, not_and_distrib, not_not] at h₂,
    refine or.inl (or.inr ⟨x, _, rfl⟩),
    cases h₂,
    { obtain ((h | h) | h) := h,
      exact h,
      cases h₂ h,
      cases h₁ h, },
    { exact h₂, }, },
end

lemma complete_inv_fun_domain [nonempty α] (x : α) (h : x ∈ complete_domain hs ht) :
  complete_inv_fun hs ht x ∈ complete_domain hs ht :=
begin
  unfold complete_inv_fun complete_domain,
  split_ifs with h₁ h₂,
  cases sandbox_subset_equiv hs ht ⟨x, h₁⟩,
  { obtain ⟨n, x⟩ := val,
    exact or.inr ((sandbox_subset_equiv hs ht).symm _).prop, },
  { obtain ⟨_ | n, x⟩ := val,
    { exact or.inl (or.inr x.prop.1), },
    { exact or.inr ((sandbox_subset_equiv hs ht).symm _).prop, }, },
  { exact or.inr ((sandbox_subset_equiv hs ht).symm _).prop, },
  { rw [mem_diff, not_and_distrib, not_not] at h₂,
    cases h₂,
    { rw complete_domain at h,
      obtain ((h | h) | h) := h,
      cases h₂ h,
      { refine or.inl (or.inl _),
        simp only [mem_image, ← exists_prop] at h,
        exact inv_fun_on_mem h, },
      cases h₁ h, },
    simp only [mem_image, ← exists_prop] at h₂,
    refine or.inl (or.inl (inv_fun_on_mem h₂)), },
end

lemma complete_left_inv [nonempty α] (hst : disjoint (s ∪ f '' s) t) (hf : inj_on f s)
  (x : α) (h : x ∈ complete_domain hs ht) : complete_inv_fun hs ht (complete_to_fun hs ht x) = x :=
begin
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem] at hst,
  by_cases h₁ : x ∈ s,
  { rw [complete_to_fun, dif_neg, dif_neg, complete_inv_fun, dif_neg, dif_neg],
    { exact hf (inv_fun_on_apply_mem h₁) h₁
        (show f (inv_fun_on f s (f x)) = f x, from inv_fun_on_apply_eq h₁), },
    { exact λ h', h'.2 ⟨x, h₁, rfl⟩, },
    { exact λ hx, hst (f x) ⟨or.inr ⟨x, h₁, rfl⟩, sandbox_subset_subset hs ht hx⟩, },
    { exact λ h', h'.2 h₁, },
    { exact λ hx, hst x ⟨or.inl h₁, sandbox_subset_subset hs ht hx⟩, }, },
  by_cases h₂ : x ∈ f '' s,
  { rw [complete_to_fun, dif_neg, dif_pos, complete_inv_fun, dif_pos],
    simp only [subtype.coe_eta, equiv.apply_symm_apply],
    refl,
    { exact ((sandbox_subset_equiv hs ht).symm _).prop,
      exact ⟨h₂, h₁⟩, },
    { exact λ h, hst x ⟨or.inr h₂, sandbox_subset_subset hs ht h⟩, }, },
  obtain ((h | h) | h) := h,
  { cases h₁ h, },
  { cases h₂ h, },
  rw [complete_to_fun, dif_pos h, complete_inv_fun],
  by_cases h₃ : ∃ a, sandbox_subset_equiv hs ht ⟨x, h⟩ = sum.inl ⟨0, a⟩,
  { obtain ⟨a, ha⟩ := h₃,
    rw [dif_neg, dif_pos, subtype.coe_eq_iff],
    refine ⟨h, _⟩,
    simp only [ha],
    exact a.prop,
    { rw equiv.symm_apply_eq, simp only [ha], ext; refl, },
    { rw ha,
      exact λ h, hst _ ⟨or.inl a.prop.1, sandbox_subset_subset hs ht h⟩, }, },
  have h₄ : (∃ n a, sandbox_subset_equiv hs ht ⟨x, h⟩ = sum.inl ⟨n + 1, a⟩) ∨
    ∃ n a, sandbox_subset_equiv hs ht ⟨x, h⟩ = sum.inr ⟨n, a⟩,
  { set val := sandbox_subset_equiv hs ht ⟨x, h⟩,
    clear_value val,
    obtain (⟨_ | n, b⟩ | ⟨n, b⟩) := val,
    cases h₃ ⟨b, rfl⟩,
    exact or.inl ⟨n, b, rfl⟩,
    exact or.inr ⟨n, b, rfl⟩, },
  cases h₄;
  { obtain ⟨n, a, ha⟩ := h₄,
    rw [dif_pos],
    simp only [ha],
    unfold shift_right,
    simp only [subtype.coe_eta, equiv.apply_symm_apply],
    exact subtype.coe_inj.mpr ((equiv.symm_apply_eq _).mpr ha.symm),
    rw ha,
    exact ((sandbox_subset_equiv hs ht).symm _).prop, },
end

lemma complete_right_inv [nonempty α] (hst : disjoint (s ∪ f '' s) t) (hf : inj_on f s)
  (x : α) (h : x ∈ complete_domain hs ht) : complete_to_fun hs ht (complete_inv_fun hs ht x) = x :=
begin
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem] at hst,
  by_cases h₁ : x ∈ f '' s,
  { rw [complete_inv_fun, dif_neg, dif_neg, complete_to_fun, dif_neg, dif_neg],
    { exact inv_fun_on_eq (set.mem_image_iff_bex.mp h₁), },
    { exact λ h', h'.2 (inv_fun_on_mem (set.mem_image_iff_bex.mp h₁)), },
    { exact λ hx, hst _ ⟨or.inl (inv_fun_on_mem (set.mem_image_iff_bex.mp h₁)),
        sandbox_subset_subset hs ht hx⟩, },
    { exact λ h', h'.2 h₁, },
    { exact λ hx, hst x ⟨or.inr h₁, sandbox_subset_subset hs ht hx⟩, }, },
  by_cases h₂ : x ∈ s,
  { rw [complete_inv_fun, dif_neg, dif_pos, complete_to_fun, dif_pos],
    simp only [subtype.coe_eta, equiv.apply_symm_apply],
    refl,
    { exact ((sandbox_subset_equiv hs ht).symm _).prop,
      exact ⟨h₂, h₁⟩, },
    { exact λ h, hst x ⟨or.inl h₂, sandbox_subset_subset hs ht h⟩, }, },
  obtain ((h | h) | h) := h,
  { cases h₂ h, },
  { cases h₁ h, },
  rw [complete_inv_fun, dif_pos h, complete_to_fun],
  by_cases h₃ : ∃ a, sandbox_subset_equiv hs ht ⟨x, h⟩ = sum.inr ⟨0, a⟩,
  { obtain ⟨a, ha⟩ := h₃,
    rw [dif_neg, dif_pos, subtype.coe_eq_iff],
    refine ⟨h, _⟩,
    simp only [ha],
    exact a.prop,
    { rw equiv.symm_apply_eq, simp only [ha], ext; refl, },
    { rw ha,
      exact λ h, hst _ ⟨or.inr a.prop.1, sandbox_subset_subset hs ht h⟩, }, },
  have h₄ : (∃ n a, sandbox_subset_equiv hs ht ⟨x, h⟩ = sum.inr ⟨n + 1, a⟩) ∨
    ∃ n a, sandbox_subset_equiv hs ht ⟨x, h⟩ = sum.inl ⟨n, a⟩,
  { set val := sandbox_subset_equiv hs ht ⟨x, h⟩,
    clear_value val,
    obtain (⟨n, b⟩ | ⟨_ | n, b⟩) := val,
    exact or.inr ⟨n, b, rfl⟩,
    cases h₃ ⟨b, rfl⟩,
    exact or.inl ⟨n, b, rfl⟩, },
  cases h₄;
  { obtain ⟨n, a, ha⟩ := h₄,
    rw [dif_pos],
    simp only [ha],
    unfold shift_left,
    simp only [subtype.coe_eta, equiv.apply_symm_apply],
    exact subtype.coe_inj.mpr ((equiv.symm_apply_eq _).mpr ha.symm),
    rw ha,
    exact ((sandbox_subset_equiv hs ht).symm _).prop, },
end

/-- Completes a function `f` on a domain `s` into a local permutation that agrees with `f` on `s`,
with domain contained in `s ∪ (f '' s) ∪ t`. -/
noncomputable def complete [nonempty α] (f : α → α) (s : set α) (t : set α)
  (hs : #(s ∆ (f '' s) : set α) ≤ #t) (ht : ℵ₀ ≤ #t) (hst : disjoint (s ∪ f '' s) t)
  (hf : inj_on f s) : local_perm α := {
  to_fun := complete_to_fun hs ht,
  inv_fun := complete_inv_fun hs ht,
  domain := complete_domain hs ht,
  to_fun_domain' := complete_to_fun_domain hs ht,
  inv_fun_domain' := complete_inv_fun_domain hs ht,
  left_inv' := complete_left_inv hs ht hst hf,
  right_inv' := complete_right_inv hs ht hst hf,
}

variables [nonempty α] {hst : disjoint (s ∪ f '' s) t} {hf : inj_on f s}

@[simp] lemma complete_domain_eq :
  (complete f s t hs ht hst hf).domain = complete_domain hs ht := rfl

lemma mem_complete_domain_of_mem (x : α) (hx : x ∈ s) : x ∈ complete_domain hs ht :=
or.inl (or.inl hx)

lemma mem_complete_domain_of_mem_image (x : α) (hx : x ∈ f '' s) : x ∈ complete_domain hs ht :=
or.inl (or.inr hx)

lemma not_mem_sandbox_of_mem (hst : disjoint (s ∪ f '' s) t) (x : α) (hx : x ∈ s) :
  x ∉ sandbox_subset hs ht :=
begin
  intro h,
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem] at hst,
  exact hst x ⟨or.inl hx, sandbox_subset_subset hs ht h⟩,
end

lemma not_mem_sandbox_of_mem_image (hst : disjoint (s ∪ f '' s) t) (x : α) (hx : x ∈ f '' s) :
  x ∉ sandbox_subset hs ht :=
begin
  intro h,
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem] at hst,
  exact hst x ⟨or.inr hx, sandbox_subset_subset hs ht h⟩,
end

@[simp] lemma complete_apply_eq (x : α) (hx : x ∈ s) : complete f s t hs ht hst hf x = f x :=
begin
  rw [complete, coe_mk, complete_to_fun, dif_neg, dif_neg],
  exact λ h', h'.2 hx,
  exact not_mem_sandbox_of_mem hs ht hst x hx,
end

end local_perm
