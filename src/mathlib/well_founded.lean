import data.prod.lex
import set_theory.ordinal.arithmetic

universe u

variables {α : Type u} {r : α → α → Prop}

/-- The length of the longest `r`-chain of elements ending in `a`. -/
noncomputable def acc.rank {a : α} (h : acc r a) : ordinal.{u} :=
acc.rec_on h $ λ a h ih, ordinal.sup.{u u} $ λ b : {b // r b a}, order.succ $ ih b b.2

lemma acc.rank_eq {a : α} (h : acc r a) :
  h.rank = ordinal.sup.{u u} (λ b : {b // r b a}, order.succ (h.inv b.2).rank) :=
by { change (acc.intro a $ λ _, h.inv).rank = _, refl }

/-- if `r a b` then the rank of `a` is less than the rank of `b`. -/
lemma acc.rank_lt_of_rel {a b : α} (hb : acc r b) (h : r a b) : (hb.inv h).rank < hb.rank :=
(order.lt_succ _).trans_le $
  by { rw hb.rank_eq, refine le_trans _ (ordinal.le_sup.{u u} _ ⟨a, h⟩), refl }


/-- A type synonym for `α`, intended to extend a well founded partial order on `α` to a well order.
-/
def well_order_extension (α : Type u) : Type u := α

namespace well_founded

variable (hwf : well_founded r)
include hwf

/-- The length of the longest `r`-chain of elements ending in `a`. -/
noncomputable def rank (a : α) : ordinal.{u} := (hwf.apply a).rank

lemma rank_lt_of_rel {a b : α} (h : r a b) : hwf.rank a < hwf.rank b := acc.rank_lt_of_rel _ h

/-- An arbitrary well order on `α` that extends `r`. -/
noncomputable def well_order_extension : linear_order α :=
let l : linear_order α := is_well_order.linear_order well_ordering_rel in by exactI
  @linear_order.lift' α (ordinal ×ₗ α) _ (λ a : α, (hwf.rank a, a)) (λ _ _, congr_arg prod.snd)

lemma well_order_extension_lt_def :
  hwf.well_order_extension.lt = inv_image (prod.lex (<) well_ordering_rel) (λ a, (hwf.rank a, a)) :=
rfl

instance well_order_extension.is_well_founded_lt : is_well_founded α hwf.well_order_extension.lt :=
⟨inv_image.wf _ $ prod.lex_wf ordinal.well_founded_lt.wf well_ordering_rel.is_well_order.wf⟩

/-- Any well-founded relation can be extended to a well-ordering on that type. -/
lemma exists_well_order_ge : ∃ s, r ≤ s ∧ is_well_order α s :=
⟨hwf.well_order_extension.lt, λ a b h, prod.lex.left _ _ (hwf.rank_lt_of_rel h), by split⟩

end well_founded

namespace well_order_extension
variables [partial_order α] [well_founded_lt α] {a b : well_order_extension α}

noncomputable instance : linear_order (well_order_extension α) :=
(is_well_founded.wf : @well_founded α (<)).well_order_extension

lemma lt_def :
  a < b ↔ inv_image (prod.lex (<) well_ordering_rel)
    (λ a, ((is_well_founded.wf : @well_founded α (<)).rank a, a)) a b := iff.rfl

instance : well_founded_lt (well_order_extension α) :=
well_founded.well_order_extension.is_well_founded_lt _

end well_order_extension
