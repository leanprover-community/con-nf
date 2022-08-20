universe u

namespace con_nf

/--
A model of tangled type theory, defined as follows.

* A type `Λ`, which indexes the sorts of our construction. For now, we only require that `Λ` must be
    a preorder, although in our construction this will turn out to be a well-order.
* For each `Λ`, a type `tangle`. These are the model elements.
* For each `β, α` in `Λ` such that `β < α`, a membership relation between `β`-tangles and
    `α`-tangles.
* The extensionality condition: for *each* lower sort `β < α`, an `α`-tangle is uniquely identified
    by its `β`-tangle elements.
* Some additional conditions, such as that "there exists a union operation on tangles", and
    "the comprehension axiom is satisfied". These are not yet given, since we have not decided on
    the precise way we will encode these axioms in Lean.
-/
structure ttt_model :=
(Λ : Type u)
[Λ_preorder : preorder Λ]
(tangle : Λ → Type u)
(mem ⦃β α : Λ⦄ : β < α → tangle β → tangle α → Prop)
(ext : ∀ ⦃β α : Λ⦄ (h : β < α) (t₁ t₂ : tangle α),
  (∀ (s : tangle β), mem h s t₁ ↔ mem h s t₂) → t₁ = t₂)
(structure_is_incomplete : false)

end con_nf
