import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Set.Pointwise.SMul

open scoped symmDiff Pointwise

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

theorem Set.smulSet_def {α β : Type _} {x : α} {s : Set β} [SMul α β] :
    x • s = (x • ·) '' s :=
  rfl

theorem Set.bounded_lt_union {α : Type _} [LinearOrder α] {s t : Set α}
    (hs : s.Bounded (· < ·)) (ht : t.Bounded (· < ·)) :
    (s ∪ t).Bounded (· < ·) := by
  obtain ⟨x, hx⟩ := hs
  obtain ⟨y, hy⟩ := ht
  use max x y
  rintro b (hb | hb)
  · rw [lt_max_iff]
    exact Or.inl (hx b hb)
  · rw [lt_max_iff]
    exact Or.inr (hy b hb)
