import Mathlib.Order.ConditionallyCompleteLattice.Basic

open scoped symmDiff

theorem Set.symmDiff_trans_subset {α : Type _} (s t u : Set α) :
    s ∆ u ⊆ s ∆ t ∪ t ∆ u := by
  intro x
  simp only [mem_symmDiff, mem_union]
  tauto

@[simp]
theorem Set.diff_symmDiff_self {α : Type _} (s t : Set α) :
    s \ (s ∆ t) = s ∩ t := by
  ext x
  simp only [mem_symmDiff, mem_diff, mem_inter_iff]
  tauto

@[simp]
theorem Set.inter_union_symmDiff {α : Type _} (s t : Set α) :
    s ∩ t ∪ s ∆ t = s ∪ t := by
  ext x
  simp only [mem_union, mem_inter_iff, mem_symmDiff]
  tauto

theorem Set.inter_subset_symmDiff_union_symmDiff {α : Type _} {s t u v : Set α} (h : Disjoint u v) :
    s ∩ t ⊆ s ∆ u ∪ t ∆ v := by
  intro x
  simp only [Set.disjoint_iff, subset_def, mem_empty_iff_false] at h
  simp only [mem_inter_iff, mem_union, and_imp, mem_symmDiff]
  tauto