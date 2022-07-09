import phase0.struct_perm

/-!
# Phase 1 of the recursion

This file contains the induction hypothesis for the first phase of the recursion. In this phase at
level `α`, we assume phase 1 at all levels `β < α`, but we do not assume any interaction between the
levels. Interaction will be introduced in phase 2.

## Main declarations

* `con_nf.tangle_data`: The data for the first phase of the recursion.
-/

open set with_bot

noncomputable theory

universe u

namespace con_nf
variable [params.{u}]

section define_tangle_data

class core_tangle_data (α : type_index) :=
(tangle : Type u)
(allowable : Type u)
[allowable_group : group allowable]
(allowable_to_struct_perm : allowable →* struct_perm α)
[allowable_action : mul_action allowable tangle]

export core_tangle_data (allowable_to_struct_perm)
attribute [instance] core_tangle_data.allowable_group core_tangle_data.allowable_action

class positioned_tangle_data (α : type_index) [core : core_tangle_data α] :=
(position : core.tangle ↪ μ)

export positioned_tangle_data (position)

variables (α : Λ) [core : core_tangle_data α]

class almost_tangle_data :=
(to_tangle : near_litter ↪ core.tangle)
(smul_to_tangle : Π (π : core.allowable) N, π • to_tangle N =
  to_tangle (allowable_to_struct_perm π • N))
(pretangle_inj : core.tangle ↪ pretangle α)
(smul_pretangle_inj : Π (π : core.allowable) (t : core.tangle),
  allowable_to_struct_perm π • pretangle_inj t = pretangle_inj (π • t))
(typed_singleton : atom ↪ core.tangle)
(designated_support : Π (t : core.tangle), support core.allowable_to_struct_perm t)

export almost_tangle_data (to_tangle typed_singleton designated_support)

variables [almost : almost_tangle_data α] [positioned_tangle_data α]

class tangle_data :=
(litter_lt : Π (L : litter) (a ∈ litter_set L),
  position (to_tangle L.to_near_litter : core.tangle) < position (typed_singleton a : core.tangle))
(litter_lt_near_litter : Π (N : near_litter),
  position (to_tangle N.fst.to_near_litter : core.tangle) ≤ position (to_tangle N : core.tangle))
(symm_diff_lt_near_litter : Π (N : near_litter) (a ∈ litter_set N.fst ∆ N.snd),
  position (typed_singleton a : core.tangle) < position (to_tangle N : core.tangle))
(support_lt : Π (t : core.tangle) (c : support_condition α)
  (hc : c ∈ ((almost.designated_support : Π (t : core.tangle), support _ _) t).to_potential_support)
  (not_singleton : ∀ a, t ≠ typed_singleton a)
  (not_near_litter : ∀ (L : litter), t ≠ to_tangle L.to_near_litter),
  position (c.fst.elim (typed_singleton) (to_tangle) : core.tangle) < position t)

/-- The type of tangles that we assume were constructed at stage `α`.
Later in the recursion, we will construct this type explicitly, but for now, we will just assume
that it exists.
Fields in `tangle_data` give more information about this type. -/
add_decl_doc core_tangle_data.tangle

/-- The type of allowable permutations that we assume exists on `α`-tangles.
This is given as a plain type, its action on `α`-tangles is given by `allowable_action`. -/
add_decl_doc core_tangle_data.allowable

/-- The type of allowable permutations at level `α` forms a group with respect to function
composition. Note that at this stage in the recursion, we have not established that the allowable
permutations on `α`-tangles are actually (coercible to) functions, so we cannot compose them with
the `∘` symbol; we must instead use group multiplication `*`. -/
add_decl_doc core_tangle_data.allowable_group

/-- Allowable permutations can be considered a subtype of structural permutations. However, we
cannot write this explicitly in type theory, so instead we assume this monoid homomorphism from
allowable permutations to structural permutations. This can be thought of as an inclusion map that
preserves the group structure. This allows allowable permutations to act on pretangles. -/
add_decl_doc core_tangle_data.allowable_to_struct_perm

/-- Allowable permutations act on tangles. This action commutes with certain other operations; the
exact conditions are given in `smul_to_tangle` and `smul_pretangle_inj`. -/
add_decl_doc core_tangle_data.allowable_action

/-- An injection from near-litters into level `α` tangles.
These will be explicitly constructed as "typed near-litters", which are codes of the form
`(α, -1, N)` for `N` a near-litter.

Since we haven't assumed anything about the structure of tangles at this level, we can't construct
these typed near-litters explicitly, so we rely on this function instead. In the blueprint, this is
function `j`. -/
add_decl_doc almost_tangle_data.to_tangle

/-- The action of allowable permutations on tangles commutes with the `to_tangle` function mapping
near-litters to typed near-litters. This is quite clear to see when representing tangles as codes,
but since at this stage tangles are just a type, we have to state this condition explicitly. -/
add_decl_doc almost_tangle_data.smul_to_tangle

/-- Tangles can be considered a subtype of pretangles, which are tangles without extensionality and
which are guaranteed to have a `-1`-extension. This injection can be seen as an inclusion map.
Since pretangles have a membership relation, we can use this map to see the members of a tangle at
any given level, by first converting it to a pretangle. -/
add_decl_doc almost_tangle_data.pretangle_inj

/-- The action of allowable permutations on tangles commutes with the `pretangle_inj` injection
converting tangles into pretangles. -/
add_decl_doc almost_tangle_data.smul_pretangle_inj

/-- For any atom `a`, we can construct an `α`-tangle that has a `-1`-extension that contains exactly
this atom. This is called a typed singleton. In the blueprint, this is the function `k`. -/
add_decl_doc almost_tangle_data.typed_singleton

/-- For each tangle, we provide a support for it. This is known as the designated support of the
tangle. -/
add_decl_doc almost_tangle_data.designated_support

/-- An injection from level `α` tangles into the type `μ`.
Since `μ` has a well-ordering, this induces a well-ordering on `α`-tangles: to compare two tangles,
simply compare their images under this map.

Conditions satisfied by this injection are given in `litter_lt`, `litter_lt_near_litter`,
`symm_diff_lt_near_litter`, and `support_lt`. In the blueprint, this is function `ι`. -/
add_decl_doc positioned_tangle_data.position

/-- Each typed litter `L` precedes the typed singletons of all of its elements `a ∈ L`. -/
add_decl_doc tangle_data.litter_lt

/-- Each near litter `N` which is not a litter comes later than its associated liter `L = N°`. -/
add_decl_doc tangle_data.litter_lt_near_litter

/-- Each near litter `N` comes after all elements in the symmetric difference `N ∆ N°` (which is
a small set by construction). Note that if `N` is a litter, this condition is vacuously true. -/
add_decl_doc tangle_data.symm_diff_lt_near_litter

/-- For all tangles `t` that are not typed singletons and not typed litters, `t` comes later than
all of the support conditions in its designated support. That is, if an atom `a` is in the
designated support for `t`, then `t` lies after `a`, and if a near-litter `N` is in the designated
support for `t`, then `t` lies after `N` (under suitable maps to `μ`). -/
add_decl_doc tangle_data.support_lt

end define_tangle_data

export core_tangle_data (tangle allowable allowable_to_struct_perm)
export almost_tangle_data (to_tangle pretangle_inj typed_singleton)
export positioned_tangle_data (position)

/-- The tangle data at level `⊥` is constructed by taking the tangles to be the atoms, the allowable
permutations to be near-litter-permutations. -/
instance bot.core_tangle_data : core_tangle_data ⊥ :=
{ tangle := atom,
  allowable := near_litter_perm,
  allowable_to_struct_perm := struct_perm.to_bot_iso.to_monoid_hom,
  allowable_action := infer_instance }

def bot.positioned_tangle_data : positioned_tangle_data ⊥ := ⟨nonempty.some mk_atom.le⟩

variables (α : type_index) [core_tangle_data α]

/-- Nonempty sets of tangles. -/
abbreviation tangles : Type u := {s : set (tangle α) // s.nonempty}

/-- The core tangle data up to phase `α`. -/
abbreviation core_tangle_cumul (α : Λ) := Π β : Iio α, core_tangle_data β

abbreviation positioned_tangle_cumul (α : Λ) [core : core_tangle_cumul α] :=
Π β : Iio α, @positioned_tangle_data _ β (core β)

abbreviation almost_tangle_cumul (α : Λ) [core : core_tangle_cumul α] :=
Π β : Iio α, @almost_tangle_data _ β (core β)

abbreviation tangle_cumul (α : Λ) [core : core_tangle_cumul α]
  [pos : positioned_tangle_cumul α] [almost : almost_tangle_cumul α] :=
Π β : Iio α, @tangle_data _ β (core β) (almost β) (pos β)

instance core_tangle_cumul.to_core_tangle_data (α : Λ) [hα : core_tangle_cumul α] :
  Π β : Iio (α : type_index), core_tangle_data β
| ⟨⊥, h⟩ := bot.core_tangle_data
| ⟨(β : Λ), hβ⟩ := hα ⟨β, coe_lt_coe.1 hβ⟩

end con_nf
