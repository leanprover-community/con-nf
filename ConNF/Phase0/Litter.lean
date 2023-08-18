import Mathlib.Data.Set.Pointwise.SMul
import ConNF.Mathlib.Equiv
import ConNF.Mathlib.Logic
import ConNF.Phase0.Params

/-!
# Litters, near-litters

In this file, we define litters and near-litters.

Litters are the parts of an indexed partition of `con_nf.atom`. Their precise definition can be
considered opaque, as we only care about the fact that their cardinality is `κ`.

## Main declarations

* `con_nf.litter`: The `i`-th litter.
* `con_nf.is_near_litter`: A set is a `i`-near-litter if it is near the `i`-th litter.
-/

noncomputable section

open Cardinal Set

open scoped Classical

universe u

namespace ConNF

variable [Params.{u}] {α β : Type u}

/-- The litters. This is the type indexing the partition of `atom`. -/
structure Litter where
  ν : μ
  β : TypeIndex
  γ : Λ
  β_ne_γ : β ≠ γ

instance : Inhabited Litter :=
  ⟨⟨default, ⊥, default, WithBot.bot_ne_coe⟩⟩

/-- Litters are equivalent to a subtype of a product type. -/
def litterEquiv : Litter ≃ { a : μ ×ₗ TypeIndex ×ₗ Λ // a.2.1 ≠ a.2.2 }
    where
  toFun L := ⟨⟨L.ν, L.β, L.γ⟩, L.β_ne_γ⟩
  invFun L := ⟨L.val.1, L.val.2.1, L.val.2.2, L.prop⟩
  left_inv := by rintro ⟨ν, β, γ, h⟩; rfl
  right_inv := by rintro ⟨⟨ν, β, γ⟩, h⟩; rfl

instance Subtype.isWellOrder {α : Type _} (p : α → Prop) [LT α] [IsWellOrder α (· < ·)] :
    IsWellOrder (Subtype p) (· < ·) :=
  RelEmbedding.isWellOrder (Subtype.relEmbedding (· < ·) p)

-- TODO: Remove after port.
instance Lex.isWellOrder {α β : Type _} [LT α] [LT β] [IsWellOrder α (· < ·)]
    [IsWellOrder β (· < ·)] : IsWellOrder (α ×ₗ β) (· < ·) :=
  instIsWellOrderProdLex

@[simp]
theorem mk_litter : #Litter = #μ := by
  refine
    litterEquiv.cardinal_eq.trans
      (le_antisymm ((Cardinal.mk_subtype_le _).trans_eq ?_)
        ⟨⟨fun ν => ⟨⟨ν, ⊥, default⟩, WithBot.bot_ne_coe⟩, fun ν₁ ν₂ =>
            congr_arg <| Prod.fst ∘ Subtype.val⟩⟩)
  have :=
    mul_eq_left (κ_regular.aleph0_le.trans κ_le_μ) (Λ_lt_κ.le.trans κ_lt_μ.le) Λ_limit.ne_zero
  simp only [Lex, mk_prod, lift_id, mk_typeIndex, mul_eq_self Λ_limit.aleph0_le, this]

/-- Principal segments (sets of the form `{y | y < x}`) have cardinality `< μ`. -/
theorem card_Iio_lt (x : μ) : #(Iio x) < #μ :=
  card_typein_lt (· < ·) x μ_ord.symm

/-- Initial segments (sets of the form `{y | y ≤ x}`) have cardinality `< μ`. -/
theorem card_Iic_lt (x : μ) : #(Iic x) < #μ := by
  rw [← Iio_union_right, mk_union_of_disjoint, mk_singleton]
  · exact (add_one_le_succ _).trans_lt (μ_strong_limit.isLimit.succ_lt (card_Iio_lt x))
  · simp

instance : LT Litter :=
  ⟨litterEquiv ⁻¹'o (· < ·)⟩

/-- Litters are well-ordered. -/
instance Litter.isWellOrder : IsWellOrder Litter (· < ·) :=
  RelIso.IsWellOrder.preimage _ litterEquiv

instance : LinearOrder Litter :=
  linearOrderOfSTO (· < ·)

instance : WellFoundedRelation Litter :=
  IsWellOrder.toHasWellFounded

/-- The base type of the construction, `τ₋₁` in the document. Instead of declaring it as an
arbitrary type of cardinality `μ` and partitioning it into suitable sets of litters afterwards, we
define it as `litter × κ`, which has the correct cardinality and comes with a natural
partition.

These are not 'atoms' in the ZFU, TTTU or NFU sense; they are simply the elements of the model which
are in type `τ₋₁`. -/
def Atom : Type _ :=
  Litter × κ

instance : Inhabited Atom :=
  ⟨⟨default, default⟩⟩

instance : LT Atom :=
  ⟨Prod.Lex (· < ·) (· < ·)⟩

/-- Atoms are well-ordered. -/
instance Atom.isWellOrder : IsWellOrder Atom (· < ·) :=
  instIsWellOrderProdLex

instance : LinearOrder Atom :=
  linearOrderOfSTO (· < ·)

instance : WellFoundedRelation Atom :=
  IsWellOrder.toHasWellFounded

/-- The cardinality of `τ₋₁` is the cardinality of `μ`.
We will prove that all types constructed in our model have cardinality equal to `μ`. -/
@[simp]
theorem mk_atom : #Atom = #μ := by
  simp_rw [Atom, mk_prod, lift_id, mk_litter,
    mul_eq_left (κ_regular.aleph0_le.trans κ_le_μ) κ_le_μ κ_regular.pos.ne']

variable {i j : Litter} {s t : Set Atom}

/-- The set corresponding to the `i`-th litter.

We define a litter as the set of elements of the base type `τ₋₁` where the first element of the pair
is `i`. However, as noted above, the definition can be viewed as opaque, since its cardinality is
the only interesting feature. -/
def litterSet (i : Litter) : Set Atom :=
  {p | p.1 = i}

@[simp]
theorem mem_litterSet {a : Atom} {i : Litter} : a ∈ litterSet i ↔ a.1 = i :=
  Iff.rfl

def litterSetEquiv (L : Litter) : litterSet L ≃ κ := ⟨
    fun x => x.1.2,
    fun k => ⟨(L, k), rfl⟩,
    fun x => Subtype.ext <| Prod.ext x.2.symm rfl,
    fun _ => rfl
  ⟩

/-- Each litter has cardinality `κ`. -/
@[simp]
theorem mk_litterSet (i : Litter) : #(litterSet i) = #κ :=
  Cardinal.eq.2 ⟨litterSetEquiv i⟩

/-- Two litters with different indices are disjoint. -/
theorem pairwise_disjoint_litterSet : Pairwise (Disjoint on litterSet) :=
  fun _ _ h => disjoint_left.2 fun _ hi hj => h <| hi.symm.trans hj

theorem eq_of_mem_litterSet_of_mem_litterSet {a : Atom}
    (hi : a ∈ litterSet i) (hj : a ∈ litterSet j) : i = j :=
  pairwise_disjoint_litterSet.eq <| not_disjoint_iff.2 ⟨_, hi, hj⟩

theorem litterSet_symmDiff_litterSet (h : i ≠ j) :
    litterSet i ∆ litterSet j = litterSet i ∪ litterSet j :=
  (pairwise_disjoint_litterSet h).symmDiff_eq_sup

def litterSetRelIso (L : Litter) : ((· < ·) : litterSet L → litterSet L → Prop) ≃r κr := by
  refine ⟨litterSetEquiv L, ?_⟩
  rintro ⟨⟨La, a⟩, ha⟩ ⟨⟨Lb, b⟩, hb⟩
  cases ha
  cases hb
  constructor
  · intro h
    exact Prod.Lex.right La h
  · rintro (⟨_, _, hL⟩ | ⟨_, hab⟩)
    cases lt_irrefl _ hL
    exact hab

noncomputable def litterSetOrderIso (L : Litter) : litterSet L ≃o κ :=
  OrderIso.ofRelIsoLT (litterSetRelIso L)

/-- The order type of a litter is `κ`. -/
theorem Litter.ordinal_type (L : Litter) :
    Ordinal.type ((· < ·) : litterSet L → litterSet L → Prop) = (#κ).ord := by
  rw [← κ_ord, Ordinal.type_eq]; exact ⟨litterSetRelIso L⟩

end ConNF
