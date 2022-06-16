import order.bounded_order

instance with_bot_has_strict_total_order' (α : Type*)
[has_lt α] [is_well_order α (<)] : is_strict_total_order' (with_bot α) (<) :=
begin
  classical,
  letI : linear_order α := linear_order_of_STO' (<),
  apply_instance
end

instance with_bot_is_well_order (α : Type*)
[preorder α] [β : is_well_order α (<)] : is_well_order (with_bot α) (<) :=
⟨with_bot.well_founded_lt β.2⟩
