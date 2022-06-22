import order.bounded_order

variables {α β : Type*}

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

/-- Pullback well-foundedness. -/

private def preimage_accessible {r : β → β → Prop} (f : α → β) (h : well_founded r) (y : β) :=
∀ x : α, f x = y → acc (inv_image r f) x

lemma well_founded.inv_image {r : β → β → Prop} (f : α → β) (h : well_founded r) :
  well_founded (inv_image r f) :=
  begin
      split,
      have preimage_accessible_inductive : Π (x_2 : β), (Π (y : β), r y x_2 →
          preimage_accessible f h y) → preimage_accessible f h x_2,
      {
        intros y hy x hx,
        split,
        intros x_2 hx_2,
        unfold inv_image at hx_2,
        specialize hy (f x_2),
        have key : preimage_accessible f h (f x_2),
        {
          apply hy,
          rw hx at hx_2,
          exact hx_2
        },
        unfold preimage_accessible at key,
        specialize key x_2,
        apply key; refl,
      },
      have all_preimages_accessible : ∀ y : β, preimage_accessible f h y,
      {
          apply well_founded.fix h preimage_accessible_inductive
      },
      intro x,
      have key :  ∀ x_2 : α, f x_2 = f x → acc (inv_image r f) x_2,
      {
        apply all_preimages_accessible
      },
      specialize key x,
      apply key; refl,
  end
