import ConNF.Aux.WellOrder
import Mathlib.SetTheory.Cardinal.Ordinal

noncomputable section
universe u v

open Cardinal

namespace Ordinal

def withBotOrderIso {α : Type u} [Preorder α] [IsWellOrder α (· < ·)] :
    ((· < ·) : WithBot α → WithBot α → Prop) ≃r
      Sum.Lex (EmptyRelation (α := PUnit)) ((· < ·) : α → α → Prop) where
  toFun := WithBot.recBotCoe (Sum.inl PUnit.unit) Sum.inr
  invFun := Sum.elim (λ _ ↦ ⊥) (λ x ↦ x)
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl
  map_rel_iff' {x y} := by cases x <;> cases y <;>
    simp only [Equiv.coe_fn_mk, WithBot.recBotCoe_bot, WithBot.recBotCoe_coe,
    WithBot.coe_lt_coe, WithBot.bot_lt_coe, empty_relation_apply, lt_self_iff_false, not_lt_bot,
    Sum.lex_inl_inl, Sum.lex_inr_inl, Sum.lex_inr_inr, Sum.Lex.sep]

@[simp]
theorem type_withBot {α : Type u} [Preorder α] [IsWellOrder α (· < ·)] :
    type ((· < ·) : WithBot α → WithBot α → Prop) = 1 + type ((· < ·) : α → α → Prop) := by
  change _ = type EmptyRelation + _
  rw [← type_sum_lex, type_eq]
  exact ⟨withBotOrderIso⟩

theorem noMaxOrder_of_isLimit {α : Type u} [Preorder α] [IsWellOrder α (· < ·)]
    (h : (type ((· < ·) : α → α → Prop)).IsLimit) : NoMaxOrder α := by
  constructor
  intro a
  have := (succ_lt_of_isLimit h).mpr (typein_lt_type (· < ·) a)
  obtain ⟨b, hb⟩ := typein_surj (· < ·) this
  use b
  have := Order.lt_succ (typein ((· < ·) : α → α → Prop) a)
  rw [← hb, typein_lt_typein] at this
  exact this

theorem isLimit_of_noMaxOrder {α : Type u} [Nonempty α] [Preorder α] [IsWellOrder α (· < ·)]
    (h : NoMaxOrder α) : (type ((· < ·) : α → α → Prop)).IsLimit := by
  constructor
  · simp only [ne_eq, type_eq_zero_iff_isEmpty, not_isEmpty_of_nonempty, not_false_eq_true]
  · intro o ho
    obtain ⟨x, hx⟩ := h.exists_gt (enum ((· < ·) : α → α → Prop) ⟨o, ho⟩)
    refine lt_of_le_of_lt ?_ (typein_lt_type ((· < ·) : α → α → Prop) x)
    rw [← typein_lt_typein ((· < ·) : α → α → Prop), typein_enum] at hx
    rwa [Order.succ_le_iff]

theorem isLimit_iff_noMaxOrder {α : Type u} [Nonempty α] [Preorder α] [IsWellOrder α (· < ·)] :
    (type ((· < ·) : α → α → Prop)).IsLimit ↔ NoMaxOrder α :=
  ⟨noMaxOrder_of_isLimit, isLimit_of_noMaxOrder⟩

theorem type_Iio_lt {α : Type u} [LtWellOrder α] (x : α) :
    type (Subrel ((· < ·) : α → α → Prop) (Set.Iio x)) < type ((· < ·) : α → α → Prop) :=
  typein_lt_type _ x

def iicOrderIso {α : Type u} [LtWellOrder α] (x : α) :
    (Subrel ((· < ·) : α → α → Prop) (Set.Iic x)) ≃r
      Sum.Lex (Subrel ((· < ·) : α → α → Prop) (Set.Iio x)) (EmptyRelation (α := PUnit)) where
  toFun y := if h : y = x then Sum.inr PUnit.unit else Sum.inl ⟨y, y.prop.lt_of_ne h⟩
  invFun := Sum.elim (λ y ↦ ⟨y, y.prop.le⟩) (λ _ ↦ ⟨x, le_rfl⟩)
  left_inv y := by aesop
  right_inv y := by aesop
  map_rel_iff' {y z} := by
    simp only [Equiv.coe_fn_mk, subrel_val, Subtype.coe_lt_coe]
    split_ifs with h h' h'
    · rw [Sum.lex_inr_inr, empty_relation_apply, false_iff, not_lt,
        Subtype.coe_injective (h.trans h'.symm)]
    · simp only [Sum.lex_inr_inl, false_iff, not_lt, ← Subtype.coe_le_coe, h]
      exact z.prop
    · simp only [Sum.Lex.sep, true_iff]
      rw [← Subtype.coe_lt_coe]
      exact lt_of_le_of_ne (y.prop.trans_eq h'.symm) (h'.trans_ne (Ne.symm h)).symm
    · simp only [Sum.lex_inl_inl, subrel_val, Subtype.coe_lt_coe]

theorem type_Iic_eq {α : Type u} [LtWellOrder α] (x : α) :
    type (Subrel ((· < ·) : α → α → Prop) (Set.Iic x)) =
    type (Subrel ((· < ·) : α → α → Prop) (Set.Iio x)) + 1 := by
  change _ = _ + type EmptyRelation
  rw [← type_sum_lex, type_eq]
  exact ⟨iicOrderIso x⟩

theorem type_Iic_lt {α : Type u} [LtWellOrder α] [NoMaxOrder α] (x : α) :
    type (Subrel ((· < ·) : α → α → Prop) (Set.Iic x)) < type ((· < ·) : α → α → Prop) := by
  rw [type_Iic_eq]
  haveI : Nonempty α := ⟨x⟩
  have h := isLimit_of_noMaxOrder (inferInstanceAs (NoMaxOrder α))
  exact h.right _ (type_Iio_lt x)

/-!
## Lifting ordinals
-/

@[simp]
theorem typein_ordinal (o : Ordinal.{u}) :
    -- TODO: Why can't Lean find this instance?
    letI := inferInstanceAs (IsWellOrder Ordinal (· < ·))
    typein (· < ·) o = lift.{u + 1} o := by
  letI := inferInstanceAs (IsWellOrder Ordinal (· < ·))
  induction o using Ordinal.induction with
  | h o ih =>
    apply le_antisymm
    · by_contra! h
      have := ih (enum ((· < ·) : Ordinal → Ordinal → Prop)
          ⟨lift.{u + 1} o, h.trans (typein_lt_type _ o)⟩) ?_
      · simp only [typein_enum, lift_inj] at this
        conv_rhs at h => rw [this]
        simp only [typein_enum, lt_self_iff_false] at h
      · conv_rhs => rw [← enum_typein (· < ·) o]
        exact enum_lt_enum.mpr h
    · by_contra! h
      rw [Ordinal.lt_lift_iff] at h
      obtain ⟨o', ho'₁, ho'₂⟩ := h
      rw [← ih o' ho'₂, typein_inj] at ho'₁
      exact ho'₂.ne ho'₁

instance ULift.isTrichotomous {α : Type u} {r : α → α → Prop} [IsTrichotomous α r] :
    IsTrichotomous (ULift.{v} α) (InvImage r ULift.down) := by
  constructor
  rintro ⟨a⟩ ⟨b⟩
  simp only [ULift.up_inj, InvImage]
  exact IsTrichotomous.trichotomous a b

instance ULift.isTrans {α : Type u} {r : α → α → Prop} [IsTrans α r] :
    IsTrans (ULift.{v} α) (InvImage r ULift.down) := by
  constructor
  rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
  simp only [InvImage]
  exact IsTrans.trans a b c

instance ULift.isWellOrder {α : Type u} {r : α → α → Prop} [IsWellOrder α r] :
    IsWellOrder (ULift.{v} α) (InvImage r ULift.down) :=
  ⟨⟩

theorem lift_typein_apply {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s]
    (f : r ≼i s) (a : α) :
    Ordinal.lift.{max u v, v} (Ordinal.typein s (f a)) =
    Ordinal.lift.{max u v, u} (Ordinal.typein r a) := by
  symm
  apply Quotient.sound
  constructor
  refine RelIso.ofSurjective ⟨⟨λ x ↦ ⟨f x.down, ?_⟩, ?_⟩, ?_⟩ ?_
  · simp only [Set.mem_setOf_eq, f.map_rel_iff]
    exact x.down.prop
  · intro x y h
    apply ULift.down_injective
    apply Subtype.coe_injective
    simp only [ULift.up_inj, Subtype.mk.injEq,
      EmbeddingLike.apply_eq_iff_eq] at h
    exact h
  · intro x y
    simp only [Order.Preimage, Function.Embedding.coeFn_mk, subrel_val]
    exact f.map_rel_iff
  · intro x
    obtain ⟨y, hy⟩ := f.mem_range_of_rel x.down.prop
    refine ⟨ULift.up ⟨y, ?_⟩, ?_⟩
    · have := x.down.prop
      rwa [Set.mem_setOf_eq, ← hy, f.map_rel_iff] at this
    · apply ULift.down_injective
      apply Subtype.coe_injective
      simp only [Set.mem_setOf_eq, Set.coe_setOf, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]
      exact hy

/-!
## The additive structure on the set of ordinals below a cardinal
-/

theorem card_Iio (o : Ordinal.{u}) : #(Set.Iio o) = Cardinal.lift.{u + 1} o.card := by
  rw [Cardinal.eq.mpr ⟨o.enumIsoToType.toEquiv.trans Equiv.ulift.{u + 1, u}.symm⟩,
    mk_uLift, mk_toType, lift_card]

instance {o : Ordinal.{u}} : LtWellOrder (Set.Iio o) where

theorem type_Iio (o : Ordinal.{u}) :
    type ((· < ·) : Set.Iio o → Set.Iio o → Prop) = lift.{u + 1} o := by
  have := Ordinal.lift_type_eq.{u + 1, u, u + 1}
    (r := ((· < ·) : Set.Iio o → Set.Iio o → Prop))
    (s := ((· < ·) : o.toType → o.toType → Prop))
  rw [lift_id, type_lt] at this
  rw [this]
  exact ⟨o.enumIsoToType.toRelIsoLT⟩

@[simp]
theorem typein_Iio {o : Ordinal.{u}} (x : Set.Iio o) :
    typein ((· < ·) : Set.Iio o → Set.Iio o → Prop) x = lift.{u + 1} x := by
  have := lift_typein_apply
      (r := ((· < ·) : Set.Iio o → Set.Iio o → Prop))
      (s := ((· < ·) : Ordinal → Ordinal → Prop))
      (f := ⟨⟨⟨Subtype.val, Subtype.val_injective⟩, ?_⟩, ?_⟩) x
  · rw [lift_id, lift_id, typein_ordinal] at this
    exact this.symm
  · rfl
  · simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, Subtype.range_coe_subtype,
      Set.mem_Iio, Set.mem_setOf_eq, Subtype.forall]
    intro a ha b hb
    exact hb.trans ha

variable {c : Cardinal.{u}} (h : ℵ₀ ≤ c)

theorem add_lt_ord (h : ℵ₀ ≤ c) {x y : Ordinal.{u}}
    (hx : x < c.ord) (hy : y < c.ord) : x + y < c.ord := by
  rw [lt_ord] at hx hy ⊢
  rw [card_add]
  exact Cardinal.add_lt_of_lt h hx hy

def iioAdd : Add (Set.Iio c.ord) where
  add x y := ⟨x + y, add_lt_ord h x.prop y.prop⟩

def iioSub (o : Ordinal) : Sub (Set.Iio o) where
  sub x y := ⟨x - y, (sub_le_self x y).trans_lt x.prop⟩

theorem ord_pos (h : ℵ₀ ≤ c) : 0 < c.ord := by
  rw [lt_ord, card_zero]
  exact aleph0_pos.trans_le h

def iioZero : Zero (Set.Iio c.ord) where
  zero := ⟨0, ord_pos h⟩

@[simp]
theorem iioAdd_def (x y : Set.Iio c.ord) :
    letI := iioAdd h
    ((x + y : Set.Iio c.ord) : Ordinal) = x + y :=
  rfl

def iioAddMonoid : AddMonoid (Set.Iio c.ord) where
  add_assoc x y z := by
    apply Subtype.val_injective
    rw [iioAdd_def, iioAdd_def, add_assoc]
    rfl
  zero_add x := by
    apply Subtype.val_injective
    rw [iioAdd_def]
    exact zero_add x.val
  add_zero x := by
    apply Subtype.val_injective
    rw [iioAdd_def]
    exact add_zero x.val
  nsmul := nsmulRec
  __ := iioAdd h
  __ := iioZero h

theorem nat_lt_ord (h : ℵ₀ ≤ c) (n : ℕ) : n < c.ord := by
  apply (nat_lt_omega n).trans_le
  apply ord_mono at h
  rwa [ord_aleph0] at h

def iioOfNat (n : ℕ) : OfNat (Set.Iio c.ord) n where
  ofNat := ⟨n, nat_lt_ord h n⟩

theorem iioOfNat_coe (n : ℕ) :
    letI := iioOfNat h
    ((OfNat.ofNat n : Set.Iio c.ord) : Ordinal) = n :=
  rfl

theorem iio_noMaxOrder (h : ℵ₀ ≤ c) : NoMaxOrder (Set.Iio c.ord) := by
  letI := iioAdd h
  letI := iioOfNat h
  constructor
  intro x
  use x + 1
  rw [← Subtype.coe_lt_coe, iioAdd_def, lt_add_iff_pos_right, iioOfNat_coe, Nat.cast_one]
  exact zero_lt_one

end Ordinal
