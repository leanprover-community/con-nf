import mathlib.equiv
import mathlib.order

instance with_bot_has_strict_total_order' (α : Type*)
[has_lt α] [is_well_order α (<)] : is_strict_total_order' (with_bot α) (<) :=
begin
  classical,
  letI : linear_order α := linear_order_of_STO' (<),
  apply_instance
end

lemma acc.coe_with_bot {α : Type*} [has_lt α] [is_well_order α (<)] {a : α}
(h : acc (<) a) : acc ((<) : with_bot α → with_bot α → Prop) (some a) :=
begin
  induction h with b h₁ h₂,
  refine acc.intro _ _, intros y hy,
  cases y,
  { refine acc.intro _ _, intros b hb, exfalso, simp at hb, exact hb },
  { simp at hy, exact h₂ y hy }
end

instance with_bot_is_well_order (α : Type*)
[has_lt α] [β : is_well_order α (<)] : is_well_order (with_bot α) (<) :=
begin
  refine ⟨⟨λ a, acc.intro _ (λ y hy, _)⟩⟩, cases a,
  { exfalso, simp at hy, exact hy },
  cases y,
  { refine acc.intro _ _, intros b hb,
    exfalso, simp at hb, exact hb },
  { simp at hy,
    obtain ⟨_, h⟩ := β.wf.apply a,
    exact (h y hy).coe_with_bot }
end
