import phase0.struct_perm

/-!
# Phase 1 of the recursion

This file contains the induction hypothesis for the first phase of the recursion. In this phase at
level `α`, we assume phase 1 at all levels `β < α`, but we do not assume any interaction between the
levels. Interaction will be introduced in phase 2.

## Main declarations

* `con_nf.phase_1`: The data for the first phase of the recursion.
-/

open with_bot

noncomputable theory

universe u

namespace con_nf
variable [params.{u}]

/-- The motor of the initial recursion. This contains all the information needed for phase 1 of the
recursion. Note that this is slightly different to the blueprint's formulation; here, we keep phase
1 data *cumulatively*, for all previous iterations of the recursion at once. -/
class phase_1 (α : Λ) :=
(tangle : Π β < α, Type u)
(to_tangle : Π β hβ, near_litter ↪ tangle β hβ)
(of_tangle : Π β hβ, tangle β hβ ↪ μ)
(allowable : Π β < α, Type u)
[allowable_group : Π β hβ, group (allowable β hβ)]
(allowable_to_struct_perm : Π β hβ, allowable β hβ →* struct_perm β)
[allowable_action : Π β hβ, mul_action (allowable β hβ) (tangle _ hβ)]
(smul_to_tangle : Π β hβ (π : allowable β hβ) N,
  π • to_tangle β hβ N = to_tangle β hβ (allowable_to_struct_perm _ _ π • N))
(pretangle_inj : Π β hβ, tangle β hβ ↪ pretangle β)
(smul_pretangle_inj : Π β hβ (π : allowable β hβ) (t : tangle β hβ),
  allowable_to_struct_perm β hβ π • pretangle_inj β hβ t = pretangle_inj β hβ (π • t))
(typed_singleton : Π β hβ, atom ↪ tangle β hβ)
(designated_support : Π β hβ (t : tangle β hβ), support β (allowable β hβ) t)
(litter_lt : Π β hβ (L : litter) (a ∈ litter_set L),
  of_tangle _ hβ (to_tangle β hβ L.to_near_litter) < of_tangle _ hβ (typed_singleton β _ a))
(litter_lt_near_litter : Π β hβ (N : near_litter) (hN : litter_set N.fst ≠ N.snd),
  of_tangle β hβ (to_tangle β hβ N.fst.to_near_litter) < of_tangle β hβ (to_tangle β hβ N))
(symm_diff_lt_near_litter : Π β hβ (N : near_litter) (a ∈ litter_set N.fst ∆ N.snd),
  of_tangle _ hβ (typed_singleton β hβ a) < of_tangle _ hβ (to_tangle β hβ N))
(support_lt : Π β hβ (t : tangle β hβ) (c : support_condition β)
  (hc : c ∈ (designated_support β hβ t).to_potential_support)
  (not_singleton : ∀ a, t ≠ typed_singleton β hβ a)
  (not_near_litter : ∀ (L : litter), t ≠ to_tangle β hβ L.to_near_litter),
  of_tangle _ hβ (c.fst.elim (typed_singleton β hβ) (to_tangle β hβ)) < of_tangle _ hβ t)

-- TODO(zeramorphic): remove hN from litter_lt_near_litter, replace with ≤ by injectivity of iota

/-- The type of tangles that we assume were constructed at stage `α`.
Later in the recursion, we will construct this type explicitly, but for now, we will just assume
that it exists.
Fields in `phase_1` give more information about this type. -/
add_decl_doc phase_1.tangle

/-- An injection from near-litters into level `α` tangles.
These will be explicitly constructed as "typed near-litters", which are codes of the form
`(α, -1, N)` for `N` a near-litter.

Since we haven't assumed anything about the structure of tangles at this level, we can't construct
these typed near-litters explicitly, so we rely on this function instead. In the blueprint, this is
function `j`. -/
add_decl_doc phase_1.to_tangle

/-- An injection from level `α` tangles into the type `μ`.
Since `μ` has a well-ordering, this induces a well-ordering on `α`-tangles: to compare two tangles,
simply compare their images under this map.

Conditions satisfied by this injection are given in `litter_lt`, `litter_lt_near_litter`,
`symm_diff_lt_near_litter`, and `support_lt`. In the blueprint, this is function `ι`. -/
add_decl_doc phase_1.of_tangle

/-- The type of allowable permutations that we assume exists on `α`-tangles.
This is given as a plain type, its action on `α`-tangles is given by `allowable_action`. -/
add_decl_doc phase_1.allowable

/-- The type of allowable permutations at level `α` forms a group with respect to function
composition. Note that at this stage in the recursion, we have not established that the allowable
permutations on `α`-tangles are actually (coercible to) functions, so we cannot compose them with
the `∘` symbol; we must instead use group multiplication `*`. -/
add_decl_doc phase_1.allowable_group

/-- Allowable permutations can be considered a subtype of structural permutations. However, we
cannot write this explicitly in type theory, so instead we assume this monoid homomorphism from
allowable permutations to structural permutations. This can be thought of as an inclusion map that
preserves the group structure. This allows allowable permutations to act on pretangles. -/
add_decl_doc phase_1.allowable_to_struct_perm

/-- Allowable permutations act on tangles. This action commutes with certain other operations; the
exact conditions are given in `smul_to_tangle` and `smul_pretangle_inj`. -/
add_decl_doc phase_1.allowable_action

/-- The action of allowable permutations on tangles commutes with the `to_tangle` function mapping
near-litters to typed near-litters. This is quite clear to see when representing tangles as codes,
but since at this stage tangles are just a type, we have to state this condition explicitly. -/
add_decl_doc phase_1.smul_to_tangle

/-- Tangles can be considered a subtype of pretangles, which are tangles without extensionality and
which are guaranteed to have a `-1`-extension. This injection can be seen as an inclusion map.
Since pretangles have a membership relation, we can use this map to see the members of a tangle at
any given level, by first converting it to a pretangle. -/
add_decl_doc phase_1.pretangle_inj

/-- The action of allowable permutations on tangles commutes with the `pretangle_inj` injection
converting tangles into pretangles. -/
add_decl_doc phase_1.smul_pretangle_inj

/-- For any atom `a`, we can construct an `α`-tangle that has a `-1`-extension that contains exactly
this atom. This is called a typed singleton. In the blueprint, this is the function `k`. -/
add_decl_doc phase_1.typed_singleton

/-- For each tangle, we provide a support for it. This is known as the designated support of the
tangle. -/
add_decl_doc phase_1.designated_support

/-- Each typed litter `L` precedes the typed singletons of all of its elements `a ∈ L`. -/
add_decl_doc phase_1.litter_lt

/-- Each near litter `N` which is not a litter comes later than its associated liter `L = N°`. -/
add_decl_doc phase_1.litter_lt_near_litter

/-- Each near litter `N` comes after all elements in the symmetric difference `N ∆ N°` (which is
a small set by construction). Note that if `N` is a litter, this condition is vacuously true. -/
add_decl_doc phase_1.symm_diff_lt_near_litter

/-- For all tangles `t` that are not typed singletons and not typed litters, `t` comes later than
all of the support conditions in its designated support. That is, if an atom `a` is in the
designated support for `t`, then `t` lies after `a`, and if a near-litter `N` is in the designated
support for `t`, then `t` lies after `N` (under suitable maps to `μ`). -/
add_decl_doc phase_1.support_lt

export phase_1 (to_tangle allowable allowable_group allowable_action smul_to_tangle
  pretangle_inj)

attribute [instance] allowable_group allowable_action

variables (α : Λ) [phase_1 α]

/-- The tangles already constructed at stage `α`. -/
def tangle : Π β < (α : type_index), Type u
| ⊥ h := atom
| ((β : Λ) : type_index) h := phase_1.tangle β $ coe_lt_coe.1 h

/-- For each type index less than `α`, there is an embedding from tangles at that level into `μ`. -/
@[irreducible] def of_tangle : Π {β : type_index} (h : β < α), tangle α β h ↪ μ
| ⊥ h := let equiv := (cardinal.eq.mp mk_atom).some in ⟨equiv.to_fun, equiv.injective⟩
| (some β) h := phase_1.of_tangle β (coe_lt_coe.mp h)

/-- Nonempty sets of tangles. -/
abbreviation tangles (γ : type_index) (hγ : γ < α) : Type u :=
{s : set (tangle α γ hγ) // s.nonempty}

end con_nf
