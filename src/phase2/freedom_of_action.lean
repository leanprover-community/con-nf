import phase2.basic

/-!
# The freedom of action theorem

In this file, we will state and prove the freedom of action theorem.

We state the freedom of action condition at a particular proper type index `α`. Note that many of
the definitions are in a slightly different form from the blueprint and paper. This is likely for
one of two reasons:

* The freedom of action theorem has been substantially changed since the blueprint and paper were
    created. The blueprint is in the process of being updated, but it may not precisely reflect the
    current implementation.
* We define our paths between type indices in the opposite category `Paths(Λ, <)ᵒᵖ = Paths(Λ, >)`
    instead of the category `Paths(Λ, <)` as is seen in the blueprint. This means that paths are
    thought of as going "downwards" from `α` to `⊥` instead of upwards. Path composition is
    therefore reversed.

For most of these proofs, we assume the phase 2 assumptions at `α`. However, since we often want to
talk about allowable permutations and specifications at lower levels, we often have an ambient
parameter `B : le_index α`, which can be thought of as a path from `α` to some lower index `B`.

Often, when the blueprint or paper talks about an `α`-something, we will instead define it as a
`B`-something for increased generality. This is most useful when stating and proving the restriction
lemma and the condition on non-flexible litters.

-----

## Definitions

### Specifications

The freedom of action theorem concerns itself with completing *specifications* of allowable
permutations into an actual allowable partial permutation that satisfies the specification. In
particular, we define a specification as a set that specifies the images of certain atoms and
near-litters under certain derivatives of a permutation. For example, a specification for an
`B`-allowable permutation might specify that `π_A(a) = b` for `A` a `B`-extended index, and `a` and
`b` atoms.

We implement this in Lean by defining a specification as a set of binary conditions, where each
binary condition specifies either an atom to be supplied to `π` and the atom it is to be mapped to,
or a near-litter to be supplied and the near-litter it is to be mapped to, together with the
`B`-extended index along which we take the derivative.

We say that an allowable permutation `π` *satisfies* a given specification if all of the binary
conditions in the specification are realised by the specification; that is, if a binary condition
specifies `π_A(x) = y` then we must in fact have `π_A(x) = y` for this particular `π`.

### Allowability

We say that a specification is *allowable* (`allowable_spec`) if it satisfies a collection of
relatively permissive conditions. Essentially, we need to ensure that there are no obvious local
contradictions in the specification. For example, the one-to-one condition requires that if we
specify `π_A(a) = b`, we cannot also specify `π_A(a) = c` for some `c ≠ b`, and we cannot specify
`π_A(d) = b` for `d ≠ a` either.

More details on these conditions are discussed in depth later.

If a specification is allowable, we call it an *allowable partial permutation*
(`allowable_partial_perm`).

-----

## The theorem itself

We say that *freedom of action* holds along a path `B` if any partial allowable permutation `σ`
admits an allowable permutation `π` that satisfies it. The freedom of action theorem, our goal in
this file, states that if freedom of action holds along all proper paths `B`, and we are in the
synthesised context produced by our constructions in phase 1 at `α`, then freedom of action holds
at `α` (or more properly, at the nil path `α ⟶ α`).

To prove the freedom of action theorem, we follow the following steps.

1. We construct a preorder on the type of allowable partial permutations that satisfies some
    technical conditions (`perm_le`). Now, suppose we have a particular allowable partial
    permutation `σ`. We apply Zorn's lemma to this to generate another allowable partial permutation
    `τ` which is maximal under `≤` (`perm_le`), such that `σ ≤ τ`.
2. We prove that any allowable partial permutation `τ` which is maximal under `≤` is total and
    co-total, in the sense that the specification defines where every atom and near-litter go, along
    any derivative path.
3. We then prove that a total and co-total allowable partial permutation can be synthesised into an
    allowable permutation `π` given that we are in the synthesised context at `α`. This is precisely
    the allowable permutation that we need to complete the proof.

### Step 1: Zorn's lemma

What we call `σ ≤ τ`, the blueprint calls `σ ⊑ τ`, saying that `τ` "carefully extends" `σ`.
`σ ≤ τ` means that `σ ⊆ τ` as specifications, and:

* if `τ` has any new `A`-flexible litter, then it has all (in both domain and range);
* within each litter, if `τ.domain` has any new atom, then it must have all atoms in that litter
    (and hence must also have the litter by allowability), and dually for the range.

To prove that Zorn's lemma can be applied, we must show that for any chain `c` of allowable
partial permutations, the union of the specifications in the chain is allowable, and carefully
extends every element of the chain.

The non-trivial part of this proof is the "small or all" conditions for atoms and flexible litters.
Due to the particular construction of the preorder `≤`, if we add any atom (resp. flexible litter),
we must add all of them.

### Step 2: Totality

By symmetry, it suffices to only consider totality. We construct the well-founded relation `≺`
(read "constrains") on support conditions. Note that here, a support condition represents the
expression `π_A(x)` without specifying what `x` maps to under `π`. Suppose `π_A(x)` is a support
condition, and `S` is the set of conditions that constrain it; then informally we might say that
if binary conditions associated with each element of `S` lie in `σ` (we say that `S` is a subset of
the domain of `σ`) then we can uniquely determine where `x` is "supposed to" map to under `π`.
More precisely, if `S` is a subset of the domain of `σ`, we can extend `σ` to an allowable partial
permutation `τ ≥ σ` where `π_A(x)` is specified.

We provide one proof for each of the four cases of what `x` may be:

1. an atom;
2. a near-litter;
3. a *flexible* litter;
4. a *non-flexible* litter.

Informally, a flexible litter is one which is not the image of any f-map.

Non-flexible litters are the image of some f-map, and so the unpacked coherence condition specifies
what must happen to that litter, since any allowable permutation must commute with this f-map.
Conversely, flexible litters are not constrained by anything. We therefore need to treat them quite
differently when constructing the extended specification `τ`.

Then, because `≺` is well-founded, any element can be added to an allowable partial permutation
since inductively everything that transitively constrains it can also be added. So any `σ` that
is maximal must be total.

### Step 3: Synthesis into an allowable permutation

This is not yet complete.

-/

open function quiver with_bot cardinal
open_locale cardinal

universe u

namespace con_nf
variables [params.{u}]

open struct_perm

/-- A *binary condition* is like a support condition but uses either two atoms or two near-litters
instead of one. A binary condition `⟨⟨x, y⟩, A⟩` represents the constraint `π_A(x) = y` on an
allowable permutation. -/
@[derive inhabited]
def binary_condition (α : type_index) : Type u :=
((atom × atom) ⊕ (near_litter × near_litter)) × extended_index α

/-- The binary condition representing the inverse permutation. If `π_A(x) = y`,
then `π_A⁻¹(y) = x`. -/
instance (α : type_index) : has_inv (binary_condition α) :=
⟨λ c, ⟨c.fst.elim (λ atoms, sum.inl ⟨atoms.2, atoms.1⟩) (λ Ns, sum.inr ⟨Ns.2, Ns.1⟩), c.snd⟩⟩

/-- Converts a binary condition `⟨⟨x, y⟩, A⟩` into the support condition `⟨x, A⟩`. -/
def binary_condition.domain {α : type_index} (cond : binary_condition α) : support_condition α :=
⟨cond.fst.elim (λ atoms, sum.inl atoms.fst) (λ Ns, sum.inr Ns.fst), cond.snd⟩

/-- Converts a binary condition `⟨⟨x, y⟩, A⟩` into the support condition `⟨y, A⟩`. -/
def binary_condition.range {α : type_index} (cond : binary_condition α) : support_condition α :=
⟨cond.fst.elim (λ atoms, sum.inl atoms.snd) (λ Ns, sum.inr Ns.snd), cond.snd⟩

/-- There are `μ` binary conditions. -/
lemma mk_binary_condition (α : type_index) : #(binary_condition α) = #μ :=
begin
  unfold binary_condition,
  have h := μ_strong_limit.is_limit.aleph_0_le,
  rw [← cardinal.mul_def, ← cardinal.add_def, ← cardinal.mul_def, ← cardinal.mul_def, mk_atom,
      mk_near_litter, cardinal.mul_eq_self h, cardinal.add_eq_self h],
  exact cardinal.mul_eq_left h (le_trans (mk_extended_index α) (le_of_lt (lt_trans Λ_lt_κ κ_lt_μ)))
      (mk_extended_index_ne_zero α),
end

/-- A *unary specification* is a set of support conditions. This can be thought of as either the
domain or range of a `spec`. -/
abbreviation unary_spec (α : type_index) : Type u := set (support_condition α)

/-- A *specification* of an allowable permutation is a set of binary conditions on the allowable
permutation. -/
abbreviation spec (α : type_index) : Type u := set (binary_condition α)

instance (α : type_index) : has_inv (spec α) := ⟨λ σ, {c | c⁻¹ ∈ σ}⟩

/-- Inverses are involutive. -/
instance (α : type_index) : has_involutive_inv (spec α) := ⟨has_inv.inv, λ σ, by
ext ⟨x | x, y⟩; simp only [has_inv.inv, set.mem_set_of_eq, sum.elim_inl, sum.elim_inr, prod.mk.eta]⟩

/-- The domain of a specification is the unary specification consisting of the domains of all
binary conditions in the specification. -/
def spec.domain {α : type_index} (σ : spec α) : unary_spec α := binary_condition.domain '' σ
/-- The range of a specification is the unary specification consisting of the ranges of all
binary conditions in the specification. -/
def spec.range {α : type_index} (σ : spec α) : unary_spec α := binary_condition.range '' σ

@[simp] lemma spec.domain_empty {α : type_index} : spec.domain (∅ : spec α) = ∅ :=
begin
  unfold spec.domain,
  simp,
end

@[simp] lemma spec.range_empty {α : type_index} : spec.range (∅ : spec α) = ∅ :=
begin
  unfold spec.range,
  simp,
end

@[simp] lemma spec.domain_union {α : type_index} (σ τ : spec α) :
  (σ ∪ τ).domain = σ.domain ∪ τ.domain :=
begin
  ext c,
  unfold spec.domain,
  simp only [set.mem_image, set.mem_union_eq],
  split,
  { rintro ⟨x, hx₁ | hx₁, hx₂⟩,
    exact or.inl ⟨x, hx₁, hx₂⟩,
    exact or.inr ⟨x, hx₁, hx₂⟩, },
  { rintro (⟨x, hx₁, hx₂⟩ | ⟨x, hx₁, hx₂⟩),
    exact ⟨x, or.inl hx₁, hx₂⟩,
    exact ⟨x, or.inr hx₁, hx₂⟩, },
end

@[simp] lemma spec.range_union {α : type_index} (σ τ : spec α) :
  (σ ∪ τ).range = σ.range ∪ τ.range :=
begin
  ext c,
  unfold spec.range,
  simp only [set.mem_image, set.mem_union_eq],
  split,
  { rintro ⟨x, hx₁ | hx₁, hx₂⟩,
    exact or.inl ⟨x, hx₁, hx₂⟩,
    exact or.inr ⟨x, hx₁, hx₂⟩, },
  { rintro (⟨x, hx₁, hx₂⟩ | ⟨x, hx₁, hx₂⟩),
    exact ⟨x, or.inl hx₁, hx₂⟩,
    exact ⟨x, or.inr hx₁, hx₂⟩, },
end

@[simp] lemma spec.sUnion_domain_eq_domain_sUnion {α : type_index} (c : set (spec α)) :
  ⋃₀ (spec.domain '' c) = spec.domain ⋃₀ c :=
begin
  ext x,
  unfold spec.domain,
  simp only [set.sUnion_image, set.mem_Union, set.mem_image, exists_prop, set.mem_sUnion],
  exact ⟨λ ⟨σ, hσ, b, hbσ, hb⟩, ⟨b, ⟨σ, hσ, hbσ⟩, hb⟩,
         λ ⟨b, ⟨σ, hσ, hbσ⟩, hb⟩, ⟨σ, hσ, b, hbσ, hb⟩⟩,
end

/-- combined lemma for `spec.inv_domain` and `spec.inv_range`, since the proof is the same. -/
lemma spec.inv_domain_range {α : type_index} (σ : spec α) : σ⁻¹.domain = σ.range ∧ σ⁻¹.range = σ.domain :=
begin
  split; ext x; split,
  all_goals
  { rintro ⟨c, hc⟩,
    refine ⟨c⁻¹, _⟩,
    obtain ⟨⟨c1, c2⟩ | ⟨c1, c2⟩, c⟩ := c;
    simpa only using hc }
end

lemma spec.inv_mem_inv {α : type_index} {σ : spec α} {x : binary_condition α} : x ∈ σ ↔ x⁻¹ ∈ σ⁻¹ :=
by obtain ⟨x1 | x1, x2⟩ := x;
  simp only [has_inv.inv, sum.elim_inl, sum.elim_inr, set.mem_set_of_eq, prod.mk.eta]

lemma spec.inv_domain {α : type_index} (σ : spec α) : σ⁻¹.domain = σ.range := (spec.inv_domain_range σ).1

lemma spec.inv_range {α : type_index} (σ : spec α) : σ⁻¹.range = σ.domain := (spec.inv_domain_range σ).2

lemma spec.inv_union {α : type_index} (σ τ : spec α) : (σ ∪ τ)⁻¹ = σ⁻¹ ∪ τ⁻¹ :=
begin
  ext,
  rw spec.inv_mem_inv,
  split; intro h; cases h,
  { exact or.inl (spec.inv_mem_inv.2 h) },
  { exact or.inr (spec.inv_mem_inv.2 h) },
  { exact or.inl (spec.inv_mem_inv.1 h) },
  { exact or.inr (spec.inv_mem_inv.1 h) }
end

lemma spec.inl_mem_inv {α : type_index} (σ : spec α) (a₁ a₂ : atom) (A : extended_index α) :
  (sum.inl (a₁, a₂), A) ∈ σ⁻¹ ↔ (sum.inl (a₂, a₁), A) ∈ σ :=
spec.inv_mem_inv

lemma spec.inr_mem_inv {α : type_index} (σ : spec α) (N₁ N₂ : near_litter) (A : extended_index α) :
  (sum.inr (N₁, N₂), A) ∈ σ⁻¹ ↔ (sum.inr (N₂, N₁), A) ∈ σ :=
spec.inv_mem_inv

/-- A structural permutation *satisfies* a condition `⟨⟨x, y⟩, A⟩` if `π_A(x) = y`. -/
def struct_perm.satisfies_cond {α : type_index} (π : struct_perm α) (c : binary_condition α) :=
c.fst.elim
  (λ atoms, derivative c.snd π • atoms.fst = atoms.snd)
  (λ Ns, derivative c.snd π • Ns.fst = Ns.snd)

@[simp] lemma struct_perm.satisfies_cond_atoms {α : type_index} (π : struct_perm α) (a b : atom)
  (A : extended_index α) : π.satisfies_cond ⟨sum.inl ⟨a, b⟩, A⟩ ↔ derivative A π • a = b :=
by { unfold struct_perm.satisfies_cond, refl }

@[simp] lemma struct_perm.satisfies_cond_near_litters {α : type_index} (π : struct_perm α)
  (M N : near_litter) (A : extended_index α) :
  π.satisfies_cond ⟨sum.inr ⟨M, N⟩, A⟩ ↔ derivative A π • M = N :=
by { unfold struct_perm.satisfies_cond, refl }

/-- A structural permutation *satisfies* a specification if for all conditions `⟨⟨x, y⟩, A⟩` in the
specification, we have `π_A(x) = y`. -/
def struct_perm.satisfies {α : type_index} (π : struct_perm α) (σ : spec α) : Prop :=
∀ c ∈ σ, π.satisfies_cond c

lemma struct_perm.satisfies_mono {α : type_index} (π : struct_perm α) (σ ρ : spec α) (hσρ : σ ⊆ ρ) :
  π.satisfies ρ → π.satisfies σ :=
λ hρ c hc, hρ c (hσρ hc)

lemma struct_perm.satisfies_union_left {α : type_index} (π : struct_perm α) (σ ρ : spec α) :
  π.satisfies (σ ∪ ρ) → π.satisfies σ :=
λ h c hc, h c (set.mem_union_left _ hc)

lemma struct_perm.satisfies_union_right {α : type_index} (π : struct_perm α) (σ ρ : spec α) :
  π.satisfies (σ ∪ ρ) → π.satisfies ρ :=
λ h c hc, h c (set.mem_union_right _ hc)

/- There is an injection from the type of structural permutations to the type of specifications,
in such a way that any structural permutation satisfies its specification. We construct this
specification by simply drawing the graph of the permutation on atoms and near-litters. -/
def struct_perm.to_spec {α : type_index} (π : struct_perm α) : spec α :=
set.range (λ (x : atom × extended_index α),
  ⟨sum.inl ⟨x.fst, derivative x.snd π • x.fst⟩, x.snd⟩) ∪
set.range (λ (x : near_litter × extended_index α),
  ⟨sum.inr ⟨x.fst, derivative x.snd π • x.fst⟩, x.snd⟩)

/-- Any structural permutation satisfies its own specification. -/
lemma struct_perm.satisfies_to_spec {α : type_index} (π : struct_perm α) : π.satisfies π.to_spec :=
begin
  rintros ⟨⟨x, y⟩ | ⟨x, y⟩, A⟩ hxy; cases hxy;
  simpa only [set.mem_range, prod.mk.inj_iff, prod.exists, exists_eq_right, exists_eq_left,
    sum.elim_inl, sum.elim_inr, false_and, exists_false] using hxy,
end

/-- The map from structural permutations to their specifications is injective. -/
lemma struct_perm.to_spec_injective :∀ (α : type_index), injective (@struct_perm.to_spec _ α)
| ⊥ := begin unfold injective,
  intros σ τ heq,
  unfold struct_perm.to_spec at heq,
  dsimp [(set.range)] at heq,
  rw set.ext_iff at heq,
  simp only [prod.exists, set.mem_union_eq, set.mem_set_of_eq] at heq,
  apply ext_bot,
  intros,
  specialize heq ⟨sum.inl ⟨a, σ • a⟩ , path.nil⟩,
  simp only [prod.mk.inj_iff, exists_eq_right, derivative_nil, exists_eq_left, exists_false,
  or_false, eq_self_iff_true, true_iff] at heq,
  symmetry, exact heq, end
| (α : Λ) := begin
  unfold injective,
  intros σ τ heq,
  apply ext,
  funext,
  intros,
  apply struct_perm.to_spec_injective β,
  unfold struct_perm.to_spec at heq ⊢,
  dsimp [(set.range)] at heq ⊢,
  rw set.ext_iff at heq ⊢,
  simp only [prod.exists, set.mem_union_eq, set.mem_set_of_eq] at heq ⊢,
  intro x,
  cases x,
  specialize heq ⟨x_fst, (@path.cons type_index con_nf.quiver ↑α ↑α β path.nil hβ).comp x_snd⟩,
  simp_rw derivative_derivative,
  cases x_fst,
  simp only [prod.mk.inj_iff, exists_eq_right, derivative_nil, exists_eq_left, exists_false,
  or_false, eq_self_iff_true, true_iff] at heq ⊢,
  exact heq,
  simp only [derivative_cons_nil, prod.mk.inj_iff, exists_false, exists_eq_right, false_or] at heq ⊢,
  exact heq,
end
using_well_founded { dec_tac := `[assumption] }


/-- We can extend any support condition to one of a higher proper type index `α` by providing a path
connecting the old extended index up to `α`. -/
def support_condition.extend_path {α β : type_index} (c : support_condition β)
  (A : path (α : type_index) β) : support_condition α := ⟨c.fst, A.comp c.snd⟩

/-- We can extend any binary condition to one of a higher proper type index `α` by providing a path
connecting the old extended index up to `α`. -/
def binary_condition.extend_path {α β : type_index} (c : binary_condition β)
  (A : path (α : type_index) β) : binary_condition α := ⟨c.fst, A.comp c.snd⟩

/-- We can lower a unary specification to a lower proper type index with respect to a path
`A : α ⟶ β` by only keeping support conditions whose paths begin with `A`. -/
def unary_spec.lower {α β : type_index} (σ : unary_spec α) (A : path α β) : unary_spec β :=
{c | c.extend_path A ∈ σ}

/-- Lowering along the empty path does nothing. -/
lemma unary_spec.lower_nil {α β γ : type_index} (σ : unary_spec α) : σ.lower path.nil = σ :=
by simp only
  [unary_spec.lower, support_condition.extend_path, path.nil_comp, prod.mk.eta, set.set_of_mem_eq]

/-- The lowering map is functorial. -/
lemma unary_spec.lower_lower {α β γ : type_index} (σ : unary_spec α)
  (A : path (α : type_index) β) (B : path (β : type_index) γ) :
  (σ.lower A).lower B = σ.lower (path.comp A B) :=
by simp only [unary_spec.lower, support_condition.extend_path, set.mem_set_of_eq, path.comp_assoc]

@[simp] lemma unary_spec.lower_union {α β : type_index} (σ τ : unary_spec α) (A : path α β) :
  (σ ∪ τ).lower A = σ.lower A ∪ τ.lower A :=
by ext ⟨x | x, y⟩; simp only [unary_spec.lower, set.mem_union_eq, set.mem_set_of_eq]

@[simp] lemma unary_spec.sUnion_lower_eq_lower_sUnion {α β : type_index} (c : set (unary_spec α))
  (A : path α β) : (⋃ (s ∈ c), unary_spec.lower s A) = unary_spec.lower (⋃₀ c) A :=
by ext; simp only [unary_spec.lower, set.mem_Union, set.mem_set_of_eq, set.mem_sUnion]

/-- We can lower a specification to a lower proper type index with respect to a path
`A : α ⟶ β` by only keeping binary conditions whose paths begin with `A`. -/
def spec.lower {α β : type_index} (σ : spec α) (A : path (α : type_index) β) : spec β :=
{c | c.extend_path A ∈ σ}

/-- Lowering along the empty path does nothing. -/
lemma spec.lower_nil {α : type_index} (σ : spec α) : σ.lower path.nil = σ :=
by simp only
  [spec.lower, binary_condition.extend_path, path.nil_comp, prod.mk.eta, set.set_of_mem_eq]

/-- The lowering map is functorial. -/
lemma spec.lower_lower {α β γ : type_index} (σ : spec α)
  (A : path (α : type_index) β) (B : path (β : type_index) γ) :
  (σ.lower A).lower B = σ.lower (path.comp A B) :=
by simp only [spec.lower, binary_condition.extend_path, set.mem_set_of_eq, path.comp_assoc]

@[simp] lemma spec.lower_union {α β : type_index} (σ τ : spec α) (A : path α β) :
  (σ ∪ τ).lower A = σ.lower A ∪ τ.lower A :=
by ext ⟨x | x, y⟩; simp only [spec.lower, set.mem_union_eq, set.mem_set_of_eq]

/-- Lowering a specification corresponds exactly to forming the derivative of the corresponding
structural permutation. -/
lemma struct_perm.spec_lower_eq_derivative {α β : type_index} (π : struct_perm α)
  (A : path (α : type_index) β) : π.to_spec.lower A = (struct_perm.derivative A π).to_spec := begin
dsimp only [(spec.lower), (struct_perm.to_spec)],
ext,
simp only [set.mem_union_eq, set.mem_range, prod.exists, set.mem_set_of_eq],
cases x,
dsimp [(binary_condition.extend_path)],
simp only [prod.mk.inj_iff, exists_eq_right],
rw derivative_derivative,
end

/-- A specification is total if it specifies where every element in its domain goes. -/
def spec.total {α : type_index} (σ : spec α) : Prop := σ.domain = set.univ
/-- A specification is co-total if it specifies where every element in its codomain came from. -/
def spec.co_total {α : type_index} (σ : spec α) : Prop := σ.range = set.univ

lemma spec.co_total_of_inv_total {α : type_index} (σ : spec α) :
  σ⁻¹.total → σ.co_total :=
begin
  unfold has_inv.inv spec.total spec.co_total spec.domain spec.range binary_condition.domain binary_condition.range,
  intro h,
  rw set.eq_univ_iff_forall at h ⊢,
  intro c,
  obtain ⟨⟨⟨x1, x2⟩ | ⟨x1, x2⟩, y⟩, hxy, hc⟩ := h c,
  { refine ⟨⟨sum.inl ⟨x2, x1⟩, y⟩, hxy, hc⟩ },
  { refine ⟨⟨sum.inr ⟨x2, x1⟩, y⟩, hxy, hc⟩ }
end

lemma spec.total_1_1_restriction {α β : type_index} (σ : spec α) (A : path (α : type_index) β) :
  (σ.total → (σ.lower A).total) ∧ (σ.co_total → (σ.lower A).co_total) :=
begin
  split,
  all_goals {
    intro hσ,
    unfold spec.total spec.co_total spec.lower spec.domain spec.range at hσ ⊢,
    ext,
    refine ⟨by simp, λ _, _⟩,
    simp only [set.mem_image, set.mem_set_of_eq],
    obtain ⟨y, ⟨hyσ, hy⟩⟩ := (set.ext_iff.1 hσ $ x.extend_path A).2 (set.mem_univ _),
    set z : binary_condition β := ⟨y.fst, x.snd⟩,
    refine ⟨z, ⟨_, prod.ext_iff.2 ⟨(prod.ext_iff.1 hy).1, rfl⟩⟩⟩,
    have : y = z.extend_path A, -- probably can cut this
    { ext,
      { refl },
      { unfold binary_condition.extend_path,
        dsimp only,
        exact congr_arg prod.snd hy } },
    convert hyσ, rw ← this },
end

/-- If we lower a total specification along a path, it is still total.
This is one part of `total-1-1-restriction` in the blueprint. -/
lemma spec.lower_total {α β : type_index} (σ : spec α) (A : path (α : type_index) β) :
  σ.total → (σ.lower A).total := (spec.total_1_1_restriction _ _).1

/-- If we lower a co-total specification along a path, it is still co-total.
This is one part of `total-1-1-restriction` in the blueprint. -/
lemma spec.lower_co_total {α β : type_index} (σ : spec α) (A : path (α : type_index) β) :
  σ.co_total → (σ.lower A).co_total := (spec.total_1_1_restriction _ _).2

variables (α : Λ) [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [phase_2_assumptions α] (B : le_index α)

/--
Support conditions can be said to *constrain* each other in a number of ways. This is discussed
in the "freedom of action discussion".

1. `⟨L, A⟩ ≺ ⟨a, A⟩` when `a ∈ L` and `L` is a litter. We can say that an atom is constrained by the
    litter it belongs to.
2. `⟨N°, A⟩ ≺ ⟨N, A⟩` when `N` is a near-litter not equal to its corresponding litter `N°`.
3. `⟨a, A⟩ ≺ ⟨N, A⟩` for all `a ∈ N ∆ N°`.
4. `⟨y, B : (γ < β) : A⟩ ≺ ⟨L, A⟩` for all paths `A : α ⟶ β` and `γ, δ < β` with `γ ≠ δ`,
    and `L = f_{γ,δ}^A(x)` for some `x ∈ τ_{γ:A}`, where `⟨y, B⟩` lies in the designated support
    `S_x` of `x`.
-/
@[mk_iff] inductive constrains : support_condition B → support_condition B → Prop
| mem_litter (L : litter) (a ∈ litter_set L) (A : extended_index B) :
    constrains ⟨sum.inr L.to_near_litter, A⟩ ⟨sum.inl a, A⟩
| near_litter (N : near_litter) (hN : litter_set N.fst ≠ N.snd) (A : extended_index B) :
    constrains ⟨sum.inr N.fst.to_near_litter, A⟩ ⟨sum.inr N, A⟩
| symm_diff (N : near_litter) (a ∈ litter_set N.fst ∆ N.snd) (A : extended_index B) :
    constrains ⟨sum.inl a, A⟩ ⟨sum.inr N, A⟩
| f_map ⦃β : Λ⦄ ⦃γ : type_index⦄ ⦃δ : Λ⦄ (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
    (A : path (B : type_index) β)
    (t : tangle_path ((lt_index.mk' hγ (path.comp B.path A)) : le_index α))
    (c ∈ (designated_support_path t).carrier) :
    constrains
      ⟨c.fst, path.comp (path.cons A hγ) c.snd⟩
      ⟨sum.inr (f_map_path hγ hδ t).to_near_litter,
        path.cons (path.cons A (coe_lt_coe.mpr hδ)) (bot_lt_coe _)⟩

/-! We declare new notation for the "constrains" relation on support conditions. -/
infix ` ≺ `:50 := constrains _ _

/-- The `≺` relation is well-founded. By the conditions on orderings, if we have `⟨x, A⟩ ≺ ⟨y, B⟩`,
then `x < y` in `µ`, under the `to_tangle_path` or `typed_singleton_path` maps. -/

lemma constrains_wf : well_founded (constrains α B) := sorry

instance : has_well_founded (support_condition B) := ⟨constrains α B, constrains_wf α B⟩

variables {α} {B}

/-- A litter and extended index is *flexible* if it is not of the form `f_{γ,δ}^A(x)` for some
`x ∈ τ_{γ:A}` with conditions defined as above. Hence, it is not constrained by anything. -/
def flexible (L : litter) (A : extended_index B) : Prop := ∀ ⦃β : Λ⦄ ⦃γ : type_index⦄ ⦃δ : Λ⦄
  (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ) (C : path (B : type_index) β)
  (t : tangle_path ((lt_index.mk' hγ (path.comp B.path C)) : le_index α)),
L ≠ (f_map_path hγ hδ t) ∨ A ≠ path.cons (path.cons C $ coe_lt_coe.mpr hδ) (bot_lt_coe _)

local attribute [semireducible] litter
@[simp] lemma mk_flexible_litters (A : extended_index B) : #{L : litter // flexible L A} = #μ :=
begin
  by_cases ((B : type_index) = ⊥),
  { have H : ∀ (L : litter), flexible L A,
    { intro L,
      unfold flexible,
      intros β γ δ hγ hδ hγδ C,
      have hγB := lt_of_lt_of_le hγ (le_of_path C),
      exfalso,
      rw h at hγB,
      exact not_lt_bot hγB, },
    rw ← mk_litter,
    rw cardinal.eq,
    exact ⟨⟨subtype.val, (λ L, ⟨L, H L⟩), (λ S, subtype.eta _ _), (λ L, rfl)⟩⟩, },
  { refine le_antisymm _ _,
    { rw ← mk_litter,
      refine cardinal.mk_subtype_le _, },
    { rw cardinal.le_def,
      rw ← ne.def at h,
      rw with_bot.ne_bot_iff_exists at h,
      obtain ⟨B', hB'⟩ := h,
      refine ⟨⟨(λ x, ⟨⟨⟨⊥, B'⟩, x⟩, _⟩), _⟩⟩,
      { intros β γ δ hγ hδ hγδ C t,
        left,
        intro h,
        sorry,
        -- have := f_map_fst ⊥ (proper_lt_index.mk' hδ (B.path.comp C)).index t,
        -- unfold f_map_path at h,
        --rw ← h at this,
      },
      { sorry, }, }, },
end
local attribute [irreducible] litter

/-- A litter and extended index is flexible only if it is not constrained by anything. -/
lemma unconstrained_of_flexible (L : litter) (A : extended_index B) (h : flexible L A) :
∀ c, ¬ c ≺ ⟨sum.inr L.to_near_litter, A⟩ :=
begin
  intros c hc,
  rw constrains_iff at hc,
  obtain ⟨L, a, ha, A', hc, hA'⟩ | ⟨N, hN, A', hc, hA'⟩ |
    ⟨N, a, ha, A', hc, hA'⟩ | ⟨β, δ, γ, hγ, hδ, hγδ, A', t, ht, c', hc, h'⟩ := hc,
  { cases hA' },
  { obtain ⟨hLN, hAA'⟩ := prod.mk.inj_iff.1 hA',
    simp only at hLN,
    rw ← hLN at hN,
    apply hN, refl },
  { obtain ⟨hLN, hAA'⟩ := prod.mk.inj_iff.1 hA',
    suffices : litter_set N.1 = N.2,
    { have that := symm_diff_self (litter_set N.1),
      nth_rewrite 1 this at that,
      rw that at ha, exact ha },
    simp only at hLN,
    rw ← hLN, refl },
    unfold extended_index at A,
  specialize h hγ hδ hγδ _ t,
  obtain ⟨hLN, hAA'⟩ := prod.mk.inj_iff.1 h',
  simp only at hLN,
  cases h,
  { exact h (congr_arg sigma.fst hLN), },
  { exact h hAA', }
end

namespace unary_spec

variable (B)

noncomputable instance {β : Λ} {γ : type_index} {hγ : γ < β} (A : path (B : type_index) β) :
  mul_action (struct_perm ((lt_index.mk' hγ (path.comp B.path A)) : le_index α).index)
    (support_condition γ) :=
struct_perm.mul_action

/-- A unary specification is *support-closed* if whenever `⟨f_{γ,δ}^A(x), A⟩ ∈ σ`, `S_{γ:A}`
supports `x`. -/
def support_closed (σ : unary_spec B) : Prop :=
∀ ⦃β : Λ⦄ ⦃γ : type_index⦄ ⦃δ : Λ⦄ (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
    (A : path (B : type_index) β)
    (t : tangle_path ((lt_index.mk' hγ (path.comp B.path A)) : le_index α)),
  (⟨sum.inr (f_map_path hγ hδ t).to_near_litter,
    path.cons (path.cons A (coe_lt_coe.mpr hδ)) (bot_lt_coe _)⟩
      : support_condition B) ∈ σ →
      supports (allowable_path_to_struct_perm (lt_index.mk' hγ (path.comp B.path A) : le_index α))
        (σ.lower (path.cons A hγ)) t

end unary_spec

namespace spec

variable (B)

/-!
We now set out the allowability conditions for specifications of permutations.
These are collected in the structure `allowable_spec`, which may be treated as a proposition.
We say a specification is allowable if `allowable_spec` holds.
-/

/--
A specification is *one-to-one* on a particular path `A` if
* `⟨a, b₁⟩, ⟨a, b₂⟩ ∈ σ` implies `b₁ = b₂`,
* `⟨a₁, b⟩, ⟨a₂, b⟩ ∈ σ` implies `a₁ = a₂`,
where `a, b` may be either atoms or near-litters.
-/
@[mk_iff] structure one_to_one_forward_path (σ : spec B) (A : extended_index B) : Prop :=
(atom        : ∀ b, {a | (⟨sum.inl ⟨a, b⟩, A⟩ : binary_condition B) ∈ σ}.subsingleton)
(near_litter : ∀ N, {M | (⟨sum.inr ⟨M, N⟩, A⟩ : binary_condition B) ∈ σ}.subsingleton)

/-- A specification is one-to-one if it is one-to-one on all paths. -/
def one_to_one_forward (σ : spec B) : Prop := ∀ A, σ.one_to_one_forward_path B A

/-- If we lower a one-to-one specification along a path, it is still one-to-one.
This is one part of `total-1-1-restriction` in the blueprint. -/
lemma lower_one_to_one {β : type_index} (σ : spec B) (A : path (B : type_index) β) :
  σ.one_to_one_forward B → (σ.lower A).one_to_one_forward ⟨β, path.comp B.path A⟩ :=
begin
  intros ho he,
  split; intros hz ha hb hc hd; dsimp at hb hd,
  { exact (ho $ A.comp he).atom hz (by assumption) (by assumption), },
  { exact (ho $ A.comp he).near_litter hz (by assumption) (by assumption), },
end

/-- A specification is the graph of a structural permutation if it is one-to-one and total.
This is one direction of implication of `total-1-1-gives-perm` on the blueprint - the other
direction may not be needed. We may also require `hσ₃ : σ.co_total` or
`hσ₄ : σ⁻¹.one_to_one_forward B` - but hopefully this isn't needed. -/
lemma graph_struct_perm (σ : spec B) (hσ₁ : σ.one_to_one_forward B) (hσ₂ : σ.total) :
  ∃ (π : struct_perm B), π.to_spec = σ := sorry

/-- The allowability condition on atoms.
In an absent litter, we must specify only `< κ`-many atoms.
In a present litter, we can specify either `< κ`-many atoms and they are mapped to the right place,
or all of the atoms in the litter, and their range is exactly the image of the litter.
Note that the `small` constructor does not depend on whether the litter is present or absent. -/
@[mk_iff] inductive atom_cond (σ : spec B) (L : litter) (A : extended_index B) : Prop
| all
    (L' : near_litter) (hL : (⟨sum.inr ⟨L.to_near_litter, L'⟩, A⟩ : binary_condition B) ∈ σ)
    (atom_map : litter_set L → atom) :
  (∀ a ∈ litter_set L, (⟨sum.inl ⟨a, atom_map ⟨a, ‹_›⟩⟩, A⟩ : binary_condition B) ∈ σ) →
  L'.snd.val = set.range atom_map → atom_cond
| small_out
    (hL : (sum.inr L.to_near_litter, A) ∉ σ.domain) :
  small {a ∈ litter_set L | (⟨sum.inl a, A⟩ : support_condition B) ∈ σ.domain} → atom_cond
| small_in
    (L' : near_litter) (hL : (sum.inr (L.to_near_litter, L'), A) ∈ σ) :
  small {a ∈ litter_set L | (⟨sum.inl a, A⟩ : support_condition B) ∈ σ.domain} →
  (∀ ⦃a b : atom⦄ (hin : (sum.inl (a, b), A) ∈ σ), a ∈ litter_set L ↔ b ∈ L'.snd.val) → atom_cond

/-- The allowability condition on near-litters.
If a near-litter is present, so are its litter and all atoms in the symmetric difference, and it is
mapped to the right place. -/
def near_litter_cond (σ : spec B) (N₁ N₂ : near_litter) (A : extended_index B) : Prop :=
(⟨sum.inr ⟨N₁, N₂⟩, A⟩ : binary_condition B) ∈ σ →
  ∃ M, (⟨sum.inr ⟨N₁.fst.to_near_litter, M⟩, A⟩ : binary_condition B) ∈ σ ∧
  ∃ (symm_diff : litter_set N₁.fst ∆ N₁.snd → atom),
    (∀ a : litter_set N₁.fst ∆ N₁.snd, (⟨sum.inl ⟨a, symm_diff a⟩, A⟩ : binary_condition B) ∈ σ) ∧
  N₂.snd.val = M.snd.val ∆ set.range symm_diff

/-- This is the allowability condition for flexible litters of a given extended index.
Either all flexible litters are in both the domain and range (`all`), or there are `μ`-many not in
the domain and `μ`-many not in the range. -/
@[mk_iff] inductive flexible_cond (σ : spec B) (A : extended_index B) : Prop
| co_large :
  #μ = #{L | flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ σ.domain} →
  #μ = #{L | flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ σ.range} →
  flexible_cond
| all :
  (∀ L, flexible L A → (sum.inr L.to_near_litter, A) ∈ σ.domain) →
  (∀ L, flexible L A → (sum.inr L.to_near_litter, A) ∈ σ.range) →
  flexible_cond

-- TODO: This instance feels unnecessary and really shouldn't be needed.
-- Is there a better way of writing `non_flexible_cond` so that the instance is inferred?
instance (β : Λ) (γ : type_index) (hγ : γ < β) (A : path (B : type_index) β) :
mul_action (allowable_path (le_index.cons ⟨β, B.path.comp A⟩ hγ))
  (tangle_path (lt_index.mk' hγ (B.path.comp A) : le_index α)) :=
core_tangle_data.allowable_action

/-- The allowability condition on non-flexible litters.
Whenever `σ` contains some condition `⟨⟨f_{γ,δ}^A(g), N⟩, [-1,δ,A]⟩`, then every allowable
permutation extending `σ` has `N = f_{γ,δ}^A(ρ • g)`. -/
def non_flexible_cond (σ : spec B) : Prop :=
∀ ⦃β : Λ⦄ ⦃γ : type_index⦄ ⦃δ : Λ⦄ (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ) (N : near_litter)
  (A : path (B : type_index) β)
  (t : tangle_path ((lt_index.mk' hγ (path.comp B.path A)) : le_index α)),
  (⟨sum.inr ⟨(f_map_path hγ hδ t).to_near_litter,
    N⟩, path.cons (path.cons A (coe_lt_coe.mpr hδ)) (bot_lt_coe _)⟩ : binary_condition B) ∈ σ →
  ∀ (ρ : allowable_path B), (allowable_path_to_struct_perm _ ρ).satisfies σ →
  N = (f_map_path hγ hδ
        ((allowable_derivative_path ⟨β, _⟩ hγ (allowable_derivative_path_comp B A ρ)) • t)
      ).to_near_litter

/-- A specification is *allowable* in the forward direction if it satisfies the following
conditions. -/
structure allowable_spec_forward (σ : spec B) : Prop :=
(one_to_one : σ.one_to_one_forward B)
(atom_cond : ∀ L A, σ.atom_cond B L A)
(near_litter_cond : ∀ N₁ N₂ A, σ.near_litter_cond B N₁ N₂ A)
(non_flexible_cond : σ.non_flexible_cond B)
(support_closed : σ.domain.support_closed B)

/-- A specification is *allowable* if it is allowable in the forward and backward directions. -/
structure allowable_spec (σ : spec B) : Prop :=
(forward : σ.allowable_spec_forward B)
(backward : σ⁻¹.allowable_spec_forward B)
(flexible_cond : ∀ A, σ.flexible_cond B A)

end spec

variable (B)

namespace spec

/-- The inverse of an allowable specification is allowable. -/
lemma inv_allowable (σ : spec B) (hσ : σ.allowable_spec B) :
  σ⁻¹.allowable_spec B := {
  forward := hσ.backward,
  backward := by { rw inv_inv, exact hσ.forward },
  flexible_cond := λ A, begin
    obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := hσ.flexible_cond A,
    { refine flexible_cond.co_large _ _,
      { rw inv_domain, exact h₂, },
      { rw inv_range, exact h₁, }, },
    { refine flexible_cond.all _ _,
      { rw inv_domain, exact h₂, },
      { rw inv_range, exact h₁, }, },
  end
}

end spec

/-- An *allowable partial permutation* is a specification that is allowable as defined above. -/
def allowable_partial_perm := {σ : spec B // σ.allowable_spec B}

instance allowable_partial_perm.has_inv : has_inv (allowable_partial_perm B) :=
⟨λ σ, ⟨σ.val⁻¹, σ.val.inv_allowable B σ.property⟩⟩

/-- Inverses are involutive. -/
instance : has_involutive_inv (allowable_partial_perm B) :=
⟨has_inv.inv, λ σ, by ext ⟨x | x, y⟩; simp [has_inv.inv]⟩

@[simp] lemma allowable_partial_perm.inv_def (σ : allowable_partial_perm B) :
  σ⁻¹.val = (σ.val)⁻¹ := rfl

/-! We prove the restriction lemma: if `σ` is a partial allowable permutation, then so is `σ`
restricted to a lower path `A`. The proof should be mostly straightforward. The non-trivial bit is
the "co-large or all" on flexible litters: in a proper restriction, `μ`-many non-flexible litters
get freed up and become flexible, so if it was “all”, it becomes "co-large". -/

section lower

variables {σ : spec B} {β : Λ} (A : path (B : type_index) β) (hβ : (β : type_index) < B)

lemma lower_one_to_one_forward (hσ : σ.allowable_spec B) :
  (σ.lower A).one_to_one_forward (le_index.mk β (path.comp B.path A)) :=
spec.lower_one_to_one _ _ _ hσ.forward.one_to_one

lemma lower_atom_cond (hσ : σ.allowable_spec B) :
  ∀ L C, (σ.lower A).atom_cond (le_index.mk β (path.comp B.path A)) L C :=
begin
  intros L C,
  unfold spec.lower binary_condition.extend_path,
  obtain ⟨N, atom_map, h1, h2, h3⟩ | ⟨hL, hsmall⟩ | ⟨N, hL, hsmall, hmaps⟩ := hσ.forward.atom_cond L (A.comp C),
  { exact spec.atom_cond.all N atom_map h1 h2 h3 },
  refine spec.atom_cond.small_out _ _,
  { convert hL using 1,
    refine eq_iff_iff.2 ⟨_, _⟩; rintro ⟨⟨_ | ⟨x, y⟩, C⟩, hbin, hdom⟩; cases hdom,
    { exact ⟨_, hbin, prod.mk.inj_iff.2 ⟨(prod.mk.inj hdom).1, rfl⟩⟩ },
    { exact ⟨(sum.inr (L.to_near_litter, y), C), hbin, prod.mk.inj_iff.2 ⟨(prod.mk.inj hdom).1, rfl⟩⟩ } },
  swap,
  refine spec.atom_cond.small_in N hL _ hmaps,
  all_goals { convert hsmall,
    unfold spec.domain binary_condition.domain,
    ext a,
    simp only [set.mem_image, prod.mk.inj_iff],
    split; rintro ⟨⟨x, y⟩, hx1, hx2, hx3⟩,
    { exact ⟨⟨x, A.comp y⟩, hx1, hx2, by rw ← hx3⟩ },
    dsimp only at hx3,
    rw hx3 at hx1 hx2,
    exact ⟨⟨x, C⟩, hx1, hx2, rfl⟩ }
end

lemma lower_near_litter_cond (hσ : σ.allowable_spec B) :
  ∀ N₁ N₂ C, (σ.lower A).near_litter_cond (le_index.mk β (path.comp B.path A)) N₁ N₂ C :=
λ N₁ N₂ C hN, hσ.forward.near_litter_cond N₁ N₂ (A.comp C) hN

lemma flexible_descends (C : extended_index (⟨β, B.path.comp A⟩ : le_index α)) (L : litter) :
flexible L (A.comp C) → flexible L C :=
begin
  intro hf,
  unfold flexible at hf ⊢,
  simp at hf ⊢,
  intros hb hd hg hgb hdb hdg hp htp,
  have h1 := hf hgb hdb hdg,
  --have h2 := h1 hp,
  sorry,
end

/-- Descending down a proper path `A`, `μ`-many litters become flexible. -/
--make C a parameter?

lemma lower_flexible_co_large (hβ : (B : type_index) ≠ β) :
  #{L : litter // ∃ (C : extended_index (⟨β, B.path.comp A⟩ : le_index α)),
    flexible L C ∧ ¬ flexible L (A.comp C)} = #μ :=
begin
  refine le_antisymm _ _,
  { rw ← mk_litter, exact cardinal.mk_subtype_le _, },
  sorry
end

lemma lower_flexible_cond (hσ : σ.allowable_spec B) (C : extended_index β) :
  (σ.lower A).flexible_cond (le_index.mk β (path.comp B.path A)) C :=
begin
  by_cases hβ : (B : type_index) = β,
  { obtain ⟨B_index, B⟩ := B,
    dsimp only [le_index_coe_def] at *,
    subst hβ,
    rw [path_eq_nil A, spec.lower_nil σ],
    rw path.comp_nil,
    --exact hσ.flexible_cond C,
    sorry, },

  -- The existing proof has been modified and simplified into the following structure.

  obtain ⟨hdom, hrge⟩ | ⟨hdom, hrge⟩ := hσ.flexible_cond (A.comp C),
  { refine spec.flexible_cond.co_large _ _,
    { refine le_antisymm _ _,
      { rw hdom, refine cardinal.mk_subtype_mono _,
        -- This should be an approachable goal, solvable with `flexible_descends`.
        sorry },
      { rw ← mk_litter, exact cardinal.mk_subtype_le _, } },
    { -- Same thing here.
      sorry, },
  },
  { refine spec.flexible_cond.co_large _ _,
    -- Why are these goals true?
    -- We shouldn't try to solve these without a firm understanding of the mathematical proof.
    -- It's possible the definition is not quite correct.
    sorry, sorry },

  /- { refine spec.flexible_cond.all _ _,
    { intros L hf,
      have hdom' := hdom L _,
      { unfold spec.lower,
        unfold binary_condition.extend_path,
        unfold spec.domain at hdom' ⊢,
        dsimp at hdom' ⊢,
        obtain ⟨x, hx_1, hx_2⟩ := hdom',
        refine ⟨⟨x.fst, C⟩,_,_⟩,
        { obtain ⟨atoms | Ns, he'⟩ := x,
          { unfold binary_condition.domain at hx_2,
            simp at hx_2,
            exfalso,
            exact hx_2,
          },
          { unfold binary_condition.domain at hx_2,
            simp at hx_2 ⊢,
            obtain ⟨hx_2,hx_3⟩ := hx_2,
            rw hx_3 at hx_1,
            exact hx_1,
          },
        },
        { unfold binary_condition.domain at hx_2 ⊢,
          simp at hx_2 ⊢,
          exact and.elim_left hx_2,
        },
      },
      {
        sorry
        -- exact flexible_descends _ _ _ L hf,
      },
    },
    { intros L hf,
      have hrge' := hrge L _,
      { unfold spec.lower,
        unfold binary_condition.extend_path,
        unfold spec.range at hrge' ⊢,
        dsimp at hrge' ⊢,
        obtain ⟨x, hx_1, hx_2⟩ := hrge',
        refine ⟨⟨x.fst, C⟩,_,_⟩,
        { obtain ⟨atoms | Ns, he'⟩ := x,
          { unfold binary_condition.range at hx_2,
            simp at hx_2,
            exfalso,
            exact hx_2,
          },
          { unfold binary_condition.range at hx_2,
            simp at hx_2 ⊢,
            obtain ⟨hx_2,hx_3⟩ := hx_2,
            rw hx_3 at hx_1,
            exact hx_1,
          },
        },
        { unfold binary_condition.range at hx_2 ⊢,
          simp at hx_2 ⊢,
          obtain ⟨hx_2,hx_3⟩ := hx_2,
          exact hx_2,
        },
      },
      {
        sorry
        -- exact flexible_descends _ _ _ L hf,
      },
    }
  }, -/
end

lemma lower_non_flexible_cond (hσ : σ.allowable_spec B) :
  (σ.lower A).non_flexible_cond (le_index.mk β (path.comp B.path A)) := sorry

lemma lower_domain_closed (hσ : σ.allowable_spec B) :
  (σ.lower A).domain.support_closed (le_index.mk β (path.comp B.path A)) := sorry

lemma lower_allowable (σ : spec B) (hσ : σ.allowable_spec B)
  ⦃β : Λ⦄ (A : path (B : type_index) β) (hβ : (β : type_index) < B) :
  (σ.lower A).allowable_spec (le_index.mk β (path.comp B.path A)) := {
  forward := {
    one_to_one := lower_one_to_one_forward B A hσ,
    atom_cond := lower_atom_cond B A hσ,
    near_litter_cond := lower_near_litter_cond B A hσ,
    non_flexible_cond := lower_non_flexible_cond B A hσ,
    support_closed := lower_domain_closed B A hσ,
  },
  backward := {
    one_to_one := lower_one_to_one_forward B A (σ.inv_allowable B hσ),
    atom_cond := lower_atom_cond B A (σ.inv_allowable B hσ),
    near_litter_cond := lower_near_litter_cond B A (σ.inv_allowable B hσ),
    non_flexible_cond := lower_non_flexible_cond B A (σ.inv_allowable B hσ),
    support_closed := lower_domain_closed B A (σ.inv_allowable B hσ),
  },
  flexible_cond := lower_flexible_cond B A hσ,
}

end lower

/-- We say that *freedom of action* holds along a path `B` if any partial allowable permutation `σ`
admits an allowable permutation `π` extending it. -/
def freedom_of_action : Prop := ∀ σ : allowable_partial_perm B,
∃ (π : allowable_path B), (allowable_path_to_struct_perm B π).satisfies σ.val

/-- If an allowable partial permutation `σ` supports some `α`-tangle `t`, any permutations extending
`σ` must map `t` to the same value.
TODO: Can this be proven only assuming the permutations are structural? -/
lemma eq_of_supports (σ : allowable_partial_perm B) (t : tangle_path B)
  (ht : supports (allowable_path_to_struct_perm B) σ.val.domain t) (π₁ π₂ : allowable_path B)
  (hπ₁ : (allowable_path_to_struct_perm B π₁).satisfies σ.val)
  (hπ₂ : (allowable_path_to_struct_perm B π₂).satisfies σ.val) : π₁ • t = π₂ • t := sorry

/-- The action lemma. If freedom of action holds, and `σ` is any allowable partial permutation
that supports some `α`-tangle `t`, then there exists a unique `α`-tangle `σ(t)` such that every
allowable permutation `π` extending `σ` maps `t` to `σ(t)`.

Proof: Freedom of action gives some extension `π`, and hence some candidate value; the support
condition implies that any two extensions agree. Use the above lemma for the second part. -/
lemma exists_tangle_of_supports (σ : allowable_partial_perm B) (t : tangle_path B)
  (foa : freedom_of_action B) (ht : supports (allowable_path_to_struct_perm B) σ.val.domain t) :
  ∃ s, ∀ π, (allowable_path_to_struct_perm B π).satisfies σ.val → π • t = s :=
⟨(foa σ).some • t, λ π₁ hπ₁, eq_of_supports B σ t ht π₁ (foa σ).some hπ₁ (foa σ).some_spec⟩

namespace allowable_partial_perm

/--
We now define a preorder on partial allowable permutations.
`σ ≤ ρ` (written `σ ⊑ ρ` in the blueprint) means:

* `σ` is a subset of `ρ`;
* if `ρ` has any new `A`-flexible litter, then it has all (in both domain and range);
* within each litter, if `ρ.domain` has any new atom, then it must have all
    atoms in that litter (and hence must also have the litter), and dually for the range.

Note that the second condition is exactly the condition in `spec.flexible_cond.all`.
-/
structure perm_le (σ ρ : allowable_partial_perm B) : Prop :=
(subset : σ.val ⊆ ρ.val)
(all_flex_domain (L : litter) (N : near_litter) (A : extended_index B) (hL : flexible L A)
  (hσ : (⟨sum.inr ⟨L.to_near_litter, N⟩, A⟩ : binary_condition B) ∉ σ.val)
  (hρ : (⟨sum.inr ⟨L.to_near_litter, N⟩, A⟩ : binary_condition B) ∈ ρ.val) :
  (∀ L', flexible L' A →
    (⟨sum.inr L'.to_near_litter, A⟩ : support_condition B) ∈ ρ.val.domain ∧
    (⟨sum.inr L'.to_near_litter, A⟩ : support_condition B) ∈ ρ.val.range))
(all_flex_range (L : litter) (N : near_litter) (A : extended_index B) (hL : flexible L A)
  (hσ : (⟨sum.inr ⟨N, L.to_near_litter⟩, A⟩ : binary_condition B) ∉ σ.val)
  (hρ : (⟨sum.inr ⟨N, L.to_near_litter⟩, A⟩ : binary_condition B) ∈ ρ.val) :
  (∀ L', flexible L' A →
    (⟨sum.inr L'.to_near_litter, A⟩ : support_condition B) ∈ ρ.val.domain ∧
    (⟨sum.inr L'.to_near_litter, A⟩ : support_condition B) ∈ ρ.val.range))
(all_atoms_domain (a b : atom) (L : litter) (ha : a ∈ litter_set L) (A : extended_index B)
  (hσ : (⟨sum.inl ⟨a, b⟩, A⟩ : binary_condition B) ∉ σ.val)
  (hρ : (⟨sum.inl ⟨a, b⟩, A⟩ : binary_condition B) ∈ ρ.val) :
  ∀ c ∈ litter_set L, ∃ d, (⟨sum.inl ⟨c, d⟩, A⟩ : binary_condition B) ∈ ρ.val)
(all_atoms_range (a b : atom) (L : litter) (ha : b ∈ litter_set L) (A : extended_index B)
  (hσ : (⟨sum.inl ⟨a, b⟩, A⟩ : binary_condition B) ∉ σ.val)
  (hρ : (⟨sum.inl ⟨a, b⟩, A⟩ : binary_condition B) ∈ ρ.val) :
  ∀ c ∈ litter_set L, ∃ d, (⟨sum.inl ⟨d, c⟩, A⟩ : binary_condition B) ∈ ρ.val)

instance has_le : has_le (allowable_partial_perm B) := ⟨perm_le B⟩

/-! We now prove that the claimed preorder really is a preorder. -/

lemma extends_refl (σ : allowable_partial_perm B) : σ ≤ σ :=
⟨set.subset.rfl,
 λ _ _ _ _ h1 h2, by cases h1 h2,
 λ _ _ _ _ h1 h2, by cases h1 h2,
 λ _ _ _ _ _ h1 h2, by cases h1 h2,
 λ _ _ _ _ _ h1 h2, by cases h1 h2⟩

lemma extends_trans (ρ σ τ : allowable_partial_perm B)
  (h₁ : ρ ≤ σ) (h₂ : σ ≤ τ) : ρ ≤ τ :=
begin
  obtain ⟨hsub, hflx_domain, hflx_range, hatom_domain, hatom_range⟩ := h₁,
  obtain ⟨hsub', hflx_domain', hflx_range', hatom_domain', hatom_range'⟩ := h₂,
  refine ⟨hsub.trans hsub', λ L N A hLA hnin hin, _, λ L N A hLA hnin hin, _,
    λ a b L hab A hnin hin, _, λ a b L hab A hnin hin, _⟩,
  { by_cases (sum.inr (L.to_near_litter, N), A) ∈ σ.val,
    { exact λ l hla,
        ⟨set.image_subset binary_condition.domain hsub' (hflx_domain L N A hLA hnin h l hla).1,
        set.image_subset binary_condition.range hsub' (hflx_domain L N A hLA hnin h l hla).2⟩ },
    { exact hflx_domain' L N A hLA h hin } },
  { by_cases (sum.inr (N, L.to_near_litter), A) ∈ σ.val,
    { exact λ l hla,
        ⟨set.image_subset binary_condition.domain hsub' (hflx_range L N A hLA hnin h l hla).1,
        set.image_subset binary_condition.range hsub' (hflx_range L N A hLA hnin h l hla).2⟩ },
    { exact hflx_range' L N A hLA h hin } },
  { by_cases (sum.inl (a, b), A) ∈ σ.val,
    { intros c hc,
      obtain ⟨d, hd⟩ := hatom_domain a b L hab A hnin h c hc,
      refine ⟨d, hsub' hd⟩ },
    { exact hatom_domain' a b L hab A h hin } },
  { by_cases (sum.inl (a, b), A) ∈ σ.val,
    { intros c hc,
      obtain ⟨d, hd⟩ := hatom_range a b L hab A hnin h c hc,
      refine ⟨d, hsub' hd⟩ },
    { exact hatom_range' a b L hab A h hin } },
end

instance preorder : preorder (allowable_partial_perm B) := {
  le := perm_le B,
  le_refl := extends_refl B,
  le_trans := extends_trans B,
}

/-- A condition required later. -/
lemma inv_le (σ τ : allowable_partial_perm B) : σ ≤ τ → σ⁻¹ ≤ τ⁻¹ :=
begin
  rintro ⟨h1, h2, h3, h4, h5⟩,
  have : τ⁻¹.val = (τ.val)⁻¹ := rfl,
  refine ⟨λ x h, h1 h,
          λ L N hLA hnin hin L' A' hLA', _,
          λ L N hLA hnin hin L' A' hLA', _,
          λ a b, h5 b a, λ a b, h4 b a⟩,
  { rw [this, spec.inv_domain, spec.inv_range],
    exact and.comm.1 (h3 L N hLA hnin hin L' A' hLA') },
  { rw [this, spec.inv_domain, spec.inv_range],
    exact and.comm.1 (h2 L N hLA hnin hin L' A' hLA') }
end

lemma inv_le_iff (σ τ : allowable_partial_perm B) : σ⁻¹ ≤ τ⁻¹ ↔ σ ≤ τ :=
⟨by simpa only [inv_inv] using inv_le B σ⁻¹ τ⁻¹, inv_le _ _ _⟩

section zorn_setup

/-! To set up for Zorn's lemma, we need to show that the union of all allowable partial permutations
in a chain is an upper bound for the chain. In particular, we first show that it is allowable, and
then we show it extends all elements in the chain.

Non-trivial bit: the "small or all" conditions — these are enforced by the "if adding any, add all"
parts of the definition of ≤. -/

variables (c : set (allowable_partial_perm B))

lemma is_subset_chain_of_is_chain (hc : is_chain (≤) c) :
  is_chain (⊆) (subtype.val '' c) :=
begin
  rintros σ ⟨x, hx₁, hx₂⟩ τ ⟨y, hy₁, hy₂⟩ hneq,
  cases hc hx₁ hy₁ (λ he, hneq _);
  rw [← hx₂, ← hy₂],
  { exact or.inl h.subset, },
  { exact or.inr h.subset, },
  { rw he, }
end

lemma one_to_one_Union (hc : is_chain (≤) c) :
  spec.one_to_one_forward B ⋃₀ (subtype.val '' c) :=
begin
  intro A,
  split,
  all_goals { intros b x hx y hy,
    rw set.mem_set_of at hx hy,
    rw set.mem_sUnion at hx hy,
    obtain ⟨σx, Hx, hx⟩ := hx,
    obtain ⟨σy, Hy, hy⟩ := hy,
    have hc' := is_subset_chain_of_is_chain B c hc Hx Hy,
    by_cases (σx = σy),
    rw ← h at hy,
    obtain ⟨⟨σx,hσx⟩, Hx₁, rfl⟩ := Hx,
    swap,
    specialize hc' h,
    cases hc',
    have hx' := set.mem_of_mem_of_subset hx hc',
    obtain ⟨⟨σy,hσy⟩, Hy₁, rfl⟩ := Hy,
    swap,
    have hy' := set.mem_of_mem_of_subset hy hc',
    obtain ⟨⟨σx,hσx⟩, Hx₁, rfl⟩ := Hx, },
  -- Note: there must be a better way of doing this below.
  exact (hσx.forward.one_to_one A).atom b hx hy',
  exact (hσy.forward.one_to_one A).atom b hx' hy,
  exact (hσx.forward.one_to_one A).atom b hx hy,
  exact (hσx.forward.one_to_one A).near_litter b hx hy',
  exact (hσy.forward.one_to_one A).near_litter b hx' hy,
  exact (hσx.forward.one_to_one A).near_litter b hx hy,
end

lemma atom_cond_Union (hc : is_chain (≤) c) :
  ∀ L A, spec.atom_cond B (⋃₀ (subtype.val '' c)) L A :=
begin
  intros L A,
  rcases set.eq_empty_or_nonempty c with hemp | ⟨⟨σ, hσ₁⟩, hσ₂⟩,
  { refine spec.atom_cond.small_out _ _,
    { simp only [hemp, set.sUnion_image, set.mem_empty_eq, set.Union_false, set.Union_empty,
      spec.domain_empty, not_false_iff], },
    { simp only [hemp, set.sUnion_image, set.mem_empty_eq, set.Union_false, set.Union_empty,
      spec.domain_empty, set.sep_false, small_empty], } },
  { by_cases h' : (∃ (ρ : allowable_partial_perm B) (hρ : ρ ∈ c) (τ : allowable_partial_perm B)
        (hτ : τ ∈ c) a b (ha : a ∈ litter_set L),
        (sum.inl (a, b), A) ∉ ρ.val ∧ (sum.inl (a, b), A) ∈ τ.val ∧ ρ ≤ τ),
    { obtain ⟨ρ, hρ, τ, hτ, a, b, ha, Hρ, Hτ, hρτ⟩ := h',
      obtain ⟨N, h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N, h₁, h₂, h₃⟩ := τ.prop.forward.atom_cond L A,
      { refine spec.atom_cond.all N _ atom_map _ h₃,
        { exact set.mem_sUnion_of_mem h₁ ⟨τ, hτ, rfl⟩, },
        { exact λ a' ha', set.mem_sUnion_of_mem (h₂ a' ha') ⟨τ, hτ, rfl⟩, }, },
      all_goals { exfalso,
        refine ne_of_lt h₂ _, rw ← mk_litter_set L, convert rfl,
        ext a', split,
        { intro ha',
          split,
          { exact ha', },
          { cases hρτ.all_atoms_domain a b L ha A Hρ Hτ a' ha' with d hd,
            refine ⟨_, hd, rfl⟩, }, },
        { exact and.left, }, }, },
    { push_neg at h',
      have H' : ∀ (ρ : allowable_partial_perm B), ρ ∈ c → ∀ (τ : allowable_partial_perm B),
                  τ ∈ c → ∀ (a b : atom), a ∈ litter_set L →
                  (sum.inl (a, b), A) ∈ ρ.val → (sum.inl (a, b), A) ∈ τ.val,
      { intros ρ hρ τ hτ a b ha Hτ, contrapose Hτ, intro Hρ,
        refine h' τ hτ ρ hρ a b ha Hτ Hρ _,
        cases hc hτ hρ _ with h₁ h₁,
        { exact h₁, },
        { cases Hτ (h₁.1 Hρ), },
        { intro heq, rw heq at Hτ, exact Hτ Hρ, }, },
      have : {a ∈ litter_set L | (sum.inl a, A) ∈ spec.domain (⋃₀ (subtype.val '' c))}
              = {a ∈ litter_set L | (sum.inl a, A) ∈ σ.domain},
      { ext a,
        rw [set.mem_sep_iff, set.mem_sep_iff],
        refine and_congr_right (λ ha, ⟨_, _⟩),
        { rintro ⟨⟨⟨a', b⟩ | _, C⟩, ⟨_, ⟨ρ, hρ, rfl⟩, hb⟩, hab⟩; cases hab,
          refine ⟨_, H' ρ hρ _ hσ₂ a b ha hb, rfl⟩, },
        { exact λ ⟨b, hbσ, hba⟩, ⟨b, ⟨σ, ⟨_, hσ₂, rfl⟩, hbσ⟩, hba⟩, }, },
      obtain ⟨N, h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N, hN, h₁, h₂⟩ := hσ₁.forward.atom_cond L A,
      { exact spec.atom_cond.all N ⟨_, ⟨_, hσ₂, rfl⟩, h₁⟩ atom_map
            (λ a' ha', set.mem_sUnion_of_mem (h₂ a' ha') ⟨_, hσ₂, rfl⟩) h₃, },
      { by_cases (sum.inr L.to_near_litter, A) ∈ spec.domain (⋃₀ (subtype.val '' c)),
        { obtain ⟨⟨_ | ⟨N₁, N₂⟩, C⟩, hc₁, hc₂⟩ := h; cases hc₂,
          refine spec.atom_cond.small_in N₂ hc₁ (by rwa this) _,
          { rintros a' b ⟨τ, ⟨⟨τ, hτ⟩, hτc, hτeq⟩, hτa'⟩,
            cases hτeq,
            obtain ⟨ρ, ⟨⟨ρ, hρ⟩, hρc, hρeq⟩, hρN₂⟩ := hc₁,
            cases hρeq,
            obtain ⟨N', h₁', atom_map', h₂', h₃'⟩ | ⟨h₁', h₂'⟩ | ⟨N', hN', h₁', h₂'⟩ :=
              hρ.forward.atom_cond L A,
            { rw [(hρ.backward.one_to_one A).near_litter _ hρN₂ h₁', h₃'],
              refine ⟨λ ha',
                ⟨⟨a', ha'⟩,
                  (hτ.backward.one_to_one A).atom _ (H' _ hρc _ hτc _ _ ha' (h₂' a' ha')) hτa'⟩, _⟩,
              rintro ⟨⟨b', hb'⟩, rfl⟩,
              have := (hτ.forward.one_to_one A).atom _ (H' _ hρc _ hτc _ _ hb' (h₂' b' hb')) hτa',
              rwa this at hb' },
            { cases h₁' ⟨_, hρN₂, rfl⟩, },
            { rw [(hρ.backward.one_to_one A).near_litter _ hρN₂ hN'],
              refine ⟨λ ha', (h₂' $ H' _ hτc _ hρc _ _ ha' hτa').1 ha', λ hb, _⟩,
              sorry }, } },
        { exact spec.atom_cond.small_out h (by rwa this), }, },
      { refine spec.atom_cond.small_in N _ _ _,
        { exact set.mem_sUnion_of_mem hN ⟨_, hσ₂, rfl⟩, },
        { rwa this, },
        { rintros a' b ⟨τ, ⟨⟨τ, hτ⟩, hτc, hτeq⟩, hτa'⟩, cases hτeq,
          refine ⟨λ ha', (h₂ $ H' _ hτc _ hσ₂ a' b ha' hτa').1 ha', _⟩,
          sorry }, }, }, },
end

lemma near_litter_cond_Union (hc : is_chain (≤) c) :
  ∀ N₁ N₂ A, spec.near_litter_cond B (⋃₀ (subtype.val '' c)) N₁ N₂ A :=
begin
  rintros N₁ N₂ A ⟨ρ, ⟨σ, hσ, rfl⟩, hρ⟩,
  obtain ⟨M, hM, symm_diff, h1, h2⟩ := σ.prop.forward.near_litter_cond N₁ N₂ A hρ,
  exact ⟨M, ⟨σ, ⟨σ, hσ, rfl⟩, hM⟩, symm_diff, λ a, ⟨σ, ⟨σ, hσ, rfl⟩, h1 a⟩, h2⟩,
end

lemma flexible_cond_Union (hc : is_chain (≤) c) :
  ∀ C, spec.flexible_cond B (⋃₀ (subtype.val '' c)) C :=
begin
  intro C,
  rcases set.eq_empty_or_nonempty c with hemp | ⟨⟨σ, hσ₁⟩, hσ₂⟩,
  { rw hemp,
    refine spec.flexible_cond.co_large _ _;
    simp only [set.image_empty, set.sUnion_empty, spec.domain_empty, spec.range_empty,
               set.mem_empty_eq, not_false_iff, and_true, set.coe_set_of,
               mk_flexible_litters], },
  { by_cases h : (∃ (ρ : allowable_partial_perm B) (hρ : ρ ∈ c) (τ : allowable_partial_perm B)
      (hτ : τ ∈ c) L (hL : flexible L C),
      (((sum.inr L.to_near_litter, C) ∉ ρ.val.domain ∧
        (sum.inr L.to_near_litter, C) ∈ τ.val.domain) ∨
       ((sum.inr L.to_near_litter, C) ∉ ρ.val.range ∧
        (sum.inr L.to_near_litter, C) ∈ τ.val.range)) ∧ ρ ≤ τ),
    { obtain ⟨ρ, hρ, τ, hτ, L, hL, ⟨h, hρτ⟩⟩ := h,
      have H : ∀ L', flexible L' C →
          (⟨sum.inr L'.to_near_litter, C⟩ : support_condition B) ∈ τ.val.domain ∧
          (⟨sum.inr L'.to_near_litter, C⟩ : support_condition B) ∈ τ.val.range,
      { rcases h with ⟨Hρ, ⟨⟨_ | ⟨N₁, N₂⟩, _⟩, hb₁, hb₂⟩⟩ | ⟨Hρ, ⟨⟨_ | ⟨N₁, N₂⟩, _⟩, hb₁, hb₂⟩⟩;
        cases hb₂,
        { exact hρτ.all_flex_domain L N₂ C hL (λ Hρ', Hρ ⟨_, Hρ', rfl⟩) hb₁, },
        { exact hρτ.all_flex_range L N₁ C hL (λ Hρ', Hρ ⟨_, Hρ', rfl⟩) hb₁, }, },
        refine spec.flexible_cond.all _ _;
        intros L' hL';
        specialize H L' hL';
        cases H with H₁ H₂,
        refine set.mem_of_subset_of_mem _ H₁, swap,
        refine set.mem_of_subset_of_mem _ H₂,
        all_goals {
          intros sc hsc,
          simp only [spec.domain, spec.range, subtype.val_eq_coe, set.sUnion_image, set.mem_image,
                     set.mem_Union, exists_prop, subtype.exists, subtype.coe_mk,
                     exists_and_distrib_right],
          obtain ⟨bc, h₁, h₂⟩ := hsc,
          use bc,
          use τ.val,
          split,
          { use τ.prop,
            rwa subtype.eta, },
          { exact h₁, },
          exact h₂, }, },
    { push_neg at h,
      have H : ∀ (ρ : allowable_partial_perm B), ρ ∈ c → ∀ (τ : allowable_partial_perm B), τ ∈ c →
               ∀ (L : litter), flexible L C →
               ((sum.inr L.to_near_litter, C) ∈ ρ.val.domain →
                (sum.inr L.to_near_litter, C) ∈ τ.val.domain) ∧
               ((sum.inr L.to_near_litter, C) ∈ ρ.val.range →
                (sum.inr L.to_near_litter, C) ∈ τ.val.range),
      { intros ρ hρ τ hτ L hL,
        split;
        all_goals {
          intro Hτ,
          contrapose Hτ,
          intro Hρ, },
        specialize h τ hτ ρ hρ L hL (or.inl ⟨Hτ, Hρ⟩), swap,
        specialize h τ hτ ρ hρ L hL (or.inr ⟨Hτ, Hρ⟩),
        all_goals {
          refine h _,
          cases hc hτ hρ _ with h₁ h₁,
          { exact h₁, },
          { obtain ⟨b, hb₁, hb₂⟩ := Hρ,
            rw ← hb₂ at Hτ,
            exfalso,
            refine Hτ _,
            use b,
            exact ⟨h₁.1 hb₁, rfl⟩, },
          { intro heq,
            rw heq at Hτ,
            exact Hτ Hρ, }, }, },
      obtain ⟨hdom, hrge⟩ | ⟨hdom, hrge⟩ := hσ₁.flexible_cond C,
      { refine spec.flexible_cond.co_large _ _,
        convert hdom using 3, swap, convert hrge using 3,
        all_goals {
          ext,
          rw [set.mem_set_of, set.mem_set_of, and.congr_right_iff],
          intro hx,
          split,
          { refine λ hxc hxσ, hxc _,
            refine set.mem_of_mem_of_subset hxσ (set.image_subset _ (set.subset_sUnion_of_mem _)),
            rw set.mem_image,
            use ⟨σ, hσ₁⟩,
            exact ⟨hσ₂, rfl⟩, },
          refine λ hxσ hxc, hxσ _,
          obtain ⟨b, hb₁, hb₂⟩ := hxc,
          rw set.mem_sUnion at hb₁,
          obtain ⟨ρv, hρ, hbρ⟩ := hb₁,
          rw set.mem_image at hρ,
          obtain ⟨ρ, hρc, hρv⟩ := hρ,
        },
        refine (H ρ hρc ⟨σ, hσ₁⟩ hσ₂ x hx).right _, unfold spec.range, swap,
        refine (H ρ hρc ⟨σ, hσ₁⟩ hσ₂ x hx).left _, unfold spec.domain,
        all_goals {
          rw set.mem_image,
          rw ← hρv at hbρ,
          exact ⟨b, hbρ, hb₂⟩,
        }, },
      { refine spec.flexible_cond.all _ _;
        intros L hL,
        rename hdom h', swap, rename hrge h',
        all_goals {
          specialize h' L hL,
          refine set.mem_of_mem_of_subset h' (set.image_subset _ (set.subset_sUnion_of_mem _)),
          rw set.mem_image,
          use ⟨σ, hσ₁⟩,
          exact ⟨hσ₂, rfl⟩,
        }, }, }, },
end

-- Note: the non-flexible conditions can't be worked on yet, until allowable.lean compiles.

lemma non_flexible_cond_Union (hc : is_chain (≤) c) :
  spec.non_flexible_cond B ⋃₀ (subtype.val '' c) :=
begin
  rintro β γ δ hγ hδ hγδ N A t ⟨_, ⟨σ, hσ₁, rfl⟩, hσv⟩ π hπ,
  refine σ.prop.forward.non_flexible_cond hγ hδ hγδ N A t hσv π _,
  refine struct_perm.satisfies_mono _ _ _ (set.subset_sUnion_of_mem _) hπ,
  simpa only [hσ₁, set.mem_image, subtype.exists, exists_and_distrib_right, exists_eq_right,
              subtype.coe_eta, exists_prop, and_true] using σ.prop,
end

lemma domain_closed_Union (hc : is_chain (≤) c) :
  unary_spec.support_closed B (spec.domain ⋃₀ (subtype.val '' c)) :=
begin
  unfold unary_spec.support_closed,
  intros β γ δ hγ hδ hγδ A t h,
  rw [← spec.sUnion_domain_eq_domain_sUnion, ← unary_spec.sUnion_lower_eq_lower_sUnion] at *,
  rw set.mem_sUnion at h,
  obtain ⟨_, ⟨_, ⟨σ, hσ₁, rfl⟩, rfl⟩, ⟨b, hb₁, hb₂⟩⟩ := h,
  have hσ := σ.prop.forward.support_closed hγ hδ hγδ A t ⟨b, hb₁, hb₂⟩,
  refine supports_mono _ hσ,
  convert @set.subset_bUnion_of_mem (unary_spec B) _ _ _ (spec.domain σ) _ using 1,
  refl,
  simp only [subtype.val_eq_coe, set.mem_image, subtype.exists, subtype.coe_mk,
              exists_and_distrib_right, exists_eq_right],
  refine ⟨σ, ⟨σ.prop, _⟩, rfl⟩,
  rwa subtype.coe_eta,
end

variables (hc : is_chain (≤) c)

/-- The union of a chain of allowable partial permutations is allowable. -/
lemma allowable_Union :
  spec.allowable_spec B ⋃₀ (subtype.val '' c) :=
have c_inv_chain : is_chain has_le.le (has_inv.inv '' c) := begin
  rintros σ' ⟨σ, hσ₁, hσ₂⟩ τ' ⟨τ, hτ₁, hτ₂⟩ hne,
  rw [← hσ₂, ← hτ₂],
  have := hc hσ₁ hτ₁ _,
  { rw [inv_le_iff, inv_le_iff],
    exact this, },
  { refine λ h, hne _,
    rw [← hσ₂, ← hτ₂, h], },
end,
have Union_rw : (⋃₀ (subtype.val '' c))⁻¹ = (⋃₀ (subtype.val ''
  ((λ (σ : allowable_partial_perm B), ⟨σ.val⁻¹, σ.val.inv_allowable B σ.property⟩) '' c))) :=
begin
  unfold has_inv.inv,
  ext cond,
  split,
  { rintro ⟨σ, ⟨⟨σ, hσ⟩, hσ₁, rfl⟩, hmem⟩,
    exact ⟨σ⁻¹, ⟨⟨σ⁻¹, spec.inv_allowable B σ hσ⟩, ⟨⟨σ, hσ⟩, hσ₁, rfl⟩, rfl⟩, hmem⟩, },
  { rintro ⟨σ, ⟨⟨σ, hσ⟩, ⟨τ, hτ₁, hτ₂⟩, rfl⟩, hmem⟩,
    refine ⟨σ⁻¹, ⟨⟨σ⁻¹, spec.inv_allowable B σ hσ⟩, _, rfl⟩, _⟩,
    { rw subtype.mk_eq_mk at hτ₂, simp_rw ← hτ₂, unfold has_inv.inv, convert hτ₁,
      ext ⟨c₁ | c₁, c₂⟩; dsimp; rw prod.mk.eta, },
    { unfold has_inv.inv, obtain ⟨c₁ | c₁, c₂⟩ := cond; dsimp; rw prod.mk.eta; exact hmem, } },
end,
{
  forward := {
    one_to_one := one_to_one_Union B c hc,
    atom_cond := atom_cond_Union B c hc,
    near_litter_cond := near_litter_cond_Union B c hc,
    non_flexible_cond := non_flexible_cond_Union B c hc,
    support_closed := domain_closed_Union B c hc,
  },
  backward := {
    one_to_one := by { rw Union_rw,
      exact one_to_one_Union B (has_inv.inv '' c) c_inv_chain },
    atom_cond := by { rw Union_rw,
      exact atom_cond_Union B (has_inv.inv '' c) c_inv_chain },
    near_litter_cond := by { rw Union_rw,
      exact near_litter_cond_Union B (has_inv.inv '' c) c_inv_chain },
    non_flexible_cond := by { rw Union_rw,
      exact non_flexible_cond_Union B (has_inv.inv '' c) c_inv_chain },
    support_closed := by { rw Union_rw,
      exact domain_closed_Union B (has_inv.inv '' c) c_inv_chain },
  },
  flexible_cond := flexible_cond_Union B c hc,
}

lemma le_Union₂ (σ τ : allowable_partial_perm B)
  (hτ : τ ∈ c) : τ ≤ ⟨⋃₀ (subtype.val '' c), allowable_Union B c hc⟩ :=
begin
  have hsub : ∀ (t : allowable_partial_perm B) (ht : t ∈ c), t.val ⊆ ⋃₀ (subtype.val '' c) :=
    λ t ht b hb, ⟨t.val, set.mem_image_of_mem _ ht, hb⟩,
  refine ⟨hsub τ hτ,
    λ L N A hLA hnin hin, _,
    λ L N A hLA hnin hin, _,
    λ a b L h A hnin hin p hp, _,
    λ a b L h A hnin hin p hp, _⟩,
  all_goals
  { obtain ⟨ρ, ⟨σ, hσ, hσρ⟩, hρ⟩ := hin,
    rw ← hσρ at hρ,
    have hneq : σ ≠ τ,
    { by_contra,
      rw h at hρ,
      exact hnin hρ },
    obtain ⟨hsub, -, -, -⟩ | hleq := hc hσ hτ hneq,
    { cases hnin (hsub hρ) } },
  { have := hleq.2 L N A hLA hnin hρ,
    exact λ l hla, ⟨
      set.image_subset binary_condition.domain (hsub σ hσ) (this l hla).1,
      set.image_subset binary_condition.range (hsub σ hσ) (this l hla).2⟩ },
  { have := hleq.3 L N A hLA hnin hρ,
    exact λ l hla, ⟨
      set.image_subset binary_condition.domain (hsub σ hσ) (this l hla).1,
      set.image_subset binary_condition.range (hsub σ hσ) (this l hla).2⟩ },
  { obtain ⟨q, hq⟩ := hleq.4 a b L h A hnin hρ p hp,
    exact ⟨q, (hsub σ hσ) hq⟩ },
  { obtain ⟨q, hq⟩ := hleq.5 a b L h A hnin hρ p hp,
    exact ⟨q, (hsub σ hσ) hq⟩ }
end

lemma le_Union₁ (hcne : c.nonempty) (σ : allowable_partial_perm B)
  (hc₁ : c ⊆ {ρ : allowable_partial_perm B | σ ≤ ρ}) :
  σ ≤ ⟨⋃₀ (subtype.val '' c), allowable_Union B c hc⟩ :=
let ⟨τ, h⟩ := hcne in (set.set_of_app_iff.1 $ set.mem_def.1 $ hc₁ h).trans (le_Union₂ B c hc σ τ h)

end zorn_setup

/-- There is a maximal allowable partial permutation extending any given allowable partial
permutation. This result is due to Zorn's lemma. -/
lemma maximal_perm (σ : allowable_partial_perm B) :
  ∃ (m : allowable_partial_perm B) (H : m ∈ {ρ : allowable_partial_perm B | σ ≤ ρ}), σ ≤ m ∧
    ∀ (z : allowable_partial_perm B), z ∈ {ρ : allowable_partial_perm B | σ ≤ ρ} →
    m ≤ z → z ≤ m :=
zorn_nonempty_preorder₀ {ρ | σ ≤ ρ}
  (λ c hc₁ hc₂ τ hτ,
    ⟨⟨⋃₀ (subtype.val '' c), allowable_Union B c hc₂⟩,
      le_Union₁ B c hc₂ ⟨τ, hτ⟩ σ hc₁,
      λ τ, le_Union₂ B c hc₂ σ τ⟩)
  σ (extends_refl _ _)

section values

/-- Gets the value that a given input atom `b` is mapped to
under any allowable `π` extending `σ`. -/
noncomputable def atom_value (σ : allowable_partial_perm B) (A : extended_index B)
  (b : atom) (hb : (sum.inl b, A) ∈ σ.val.domain) : atom :=
@sum.rec _ _ (λ (c : atom × atom ⊕ near_litter × near_litter),
  c.elim (λ atoms, sum.inl atoms.fst) (λ Ns, sum.inr Ns.fst) = sum.inl b → atom)
  (λ lhs _, lhs.snd) (λ lhs h, by cases h)
  hb.some.fst
  (congr_arg prod.fst hb.some_spec.right)

lemma atom_value_spec (σ : allowable_partial_perm B) (A : extended_index B)
  (b : atom) (hb : (sum.inl b, A) ∈ σ.val.domain) :
  (sum.inl (b, atom_value B σ A b hb), A) ∈ σ.val :=
begin
  unfold atom_value,
  generalize hc : hb.some = c,
  obtain ⟨hc₁, hc₂⟩ := hb.some_spec,
  simp_rw hc at hc₁ hc₂ ⊢,
  obtain ⟨⟨b₁, b₂⟩ | Ns, C⟩ := c,
  { obtain ⟨⟨⟨d₁, d₂⟩ | _, D⟩, hd₁, hd₂⟩ := hb; cases hd₂,
    rw ← hc₂ at hd₂, cases hd₂,
    convert hd₁,
    exact (σ.property.backward.one_to_one A).atom b hc₁ hd₁, },
  { cases hc₂, }
end

lemma atom_value_spec_range (σ : allowable_partial_perm B) (A : extended_index B)
  (b : atom) (hb : (sum.inl b, A) ∈ σ.val.domain) :
  (sum.inl (atom_value B σ A b hb), A) ∈ σ.val.range :=
⟨(sum.inl (b, atom_value B σ A b hb), A), atom_value_spec B σ A b hb, rfl⟩

@[simp] lemma atom_value_eq_of_mem (σ : allowable_partial_perm B) (A : extended_index B)
  (a b : atom) (hab : (sum.inl (a, b), A) ∈ σ.val) :
  atom_value B σ A a ⟨_, hab, rfl⟩ = b :=
(σ.property.backward.one_to_one A).atom a (atom_value_spec B σ A a ⟨_, hab, rfl⟩) hab

noncomputable def atom_value_inj (σ : allowable_partial_perm B) (A : extended_index B) :
  {b | (sum.inl b, A) ∈ σ.val.domain} ↪ atom :=
⟨λ b, atom_value B σ A b.val b.property, begin
  intros b₁ b₂ hb,
  have h₁ := atom_value_spec B σ A b₁ b₁.property,
  have h₂ := atom_value_spec B σ A b₂ b₂.property,
  dsimp at hb, rw ← hb at h₂,
  exact subtype.coe_inj.mp
    ((σ.property.forward.one_to_one A).atom (atom_value B σ A b₁ b₁.property) h₁ h₂),
end⟩

lemma atom_value_mem_inv (σ : allowable_partial_perm B) (A : extended_index B)
  (b : atom) (hb : (sum.inl b, A) ∈ σ.val.domain) :
  (sum.inl (atom_value B σ A b hb, b), A) ∈ σ⁻¹.val :=
atom_value_spec B σ A b hb

/-- Composing the `atom_value` operation with the inverse permutation does nothing. -/
lemma atom_value_inv (σ : allowable_partial_perm B) (A : extended_index B)
  (b : atom) (hb : (sum.inl b, A) ∈ σ.val.domain) :
  atom_value B σ⁻¹ A (atom_value B σ A b hb) ⟨_, atom_value_mem_inv B σ A b hb, rfl⟩ = b :=
begin
  have := atom_value_spec B σ⁻¹ A (atom_value B σ A b hb) ⟨_, atom_value_mem_inv B σ A b hb, rfl⟩,
  simp_rw [allowable_partial_perm.inv_def, spec.inl_mem_inv] at this,
  exact (σ.property.forward.one_to_one A).atom _ this (atom_value_spec B σ A b hb),
end

/-- Gets the value that a given input near litter `N` is mapped to
under any allowable `π` extending `σ`. -/
noncomputable def near_litter_value (σ : allowable_partial_perm B) (A : extended_index B)
  (N : near_litter) (hb : (sum.inr N, A) ∈ σ.val.domain) : near_litter :=
@sum.rec _ _ (λ (c : atom × atom ⊕ near_litter × near_litter),
  c.elim (λ atoms, sum.inl atoms.fst) (λ Ns, sum.inr Ns.fst) = sum.inr N → near_litter)
  (λ lhs h, by cases h) (λ lhs _, lhs.snd)
  hb.some.fst
  (congr_arg prod.fst hb.some_spec.right)

lemma near_litter_value_spec (σ : allowable_partial_perm B) (A : extended_index B)
  (N : near_litter) (hN : (sum.inr N, A) ∈ σ.val.domain) :
  (sum.inr (N, near_litter_value B σ A N hN), A) ∈ σ.val :=
begin
  unfold near_litter_value,
  generalize hc : hN.some = c,
  obtain ⟨hc₁, hc₂⟩ := hN.some_spec,
  simp_rw hc at hc₁ hc₂ ⊢,
  obtain ⟨_ | ⟨N₁, N₂⟩, C⟩ := c,
  { cases hc₂, },
  { obtain ⟨⟨_ | ⟨N₃, N₄⟩, D⟩, hd₁, hd₂⟩ := hN; cases hd₂,
    rw ← hc₂ at hd₂, cases hd₂,
    convert hd₁,
    exact (σ.property.backward.one_to_one A).near_litter N hc₁ hd₁, },
end

lemma near_litter_value_spec_range (σ : allowable_partial_perm B) (A : extended_index B)
  (N : near_litter) (hN : (sum.inr N, A) ∈ σ.val.domain) :
  (sum.inr (near_litter_value B σ A N hN), A) ∈ σ.val.range :=
⟨(sum.inr (N, near_litter_value B σ A N hN), A), near_litter_value_spec B σ A N hN, rfl⟩

noncomputable def near_litter_value_inj (σ : allowable_partial_perm B) (A : extended_index B) :
  {N | (sum.inr N, A) ∈ σ.val.domain} ↪ near_litter :=
⟨λ N, near_litter_value B σ A N.val N.property, begin
  intros N₁ N₂ hN,
  have h₁ := near_litter_value_spec B σ A N₁ N₁.property,
  have h₂ := near_litter_value_spec B σ A N₂ N₂.property,
  dsimp at hN, rw ← hN at h₂,
  exact subtype.coe_inj.mp
    ((σ.property.forward.one_to_one A).near_litter (near_litter_value B σ A N₁ N₁.property) h₁ h₂),
end⟩

lemma exists_mem_symm_diff_of_ne {α : Type*} {s t : set α} (h : s ≠ t) : ∃ a, a ∈ s ∆ t :=
begin
  cases set.eq_empty_or_nonempty (s ∆ t) with h₁ h₁,
  { exfalso,
    refine h _,
    unfold symm_diff at h₁,
    simp only [set.eq_empty_iff_forall_not_mem, set.sup_eq_union, set.mem_union_eq,
      set.mem_diff] at h₁,
    push_neg at h₁,
    ext a,
    exact ⟨λ h, (h₁ a).left h, λ h, (h₁ a).right h⟩, },
  { exact h₁ }
end

/-
If the images of two litters under `σ` intersect, the litters must intersect, and therefore are
equal. This is a rather technical result depending on various allowability conditions.
-/
lemma litter_eq_of_image_inter (σ : allowable_partial_perm B) (A : extended_index B)
  {L₁ L₂ : litter} {N₁ N₂ : near_litter}
  (hL₁ : (sum.inr (L₁.to_near_litter, N₁), A) ∈ σ.val)
  (hL₂ : (sum.inr (L₂.to_near_litter, N₂), A) ∈ σ.val)
  (a : atom)
  (haN₁ : a ∈ N₁.snd.val)
  (haN₂ : a ∈ N₂.snd.val) : L₁ = L₂ :=
begin
  obtain ⟨N, h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N, hN, h₁, h₂⟩ :=
    σ.property.forward.atom_cond L₁ A,
  { cases (σ.property.backward.one_to_one A).near_litter _ hL₁ h₁,
    rw h₃ at haN₁,
    obtain ⟨a₁, ha₁⟩ := haN₁,
    have map₁ := h₂ a₁ a₁.property,
    rw subtype.coe_eta at map₁,
    rw ha₁ at map₁,

    obtain ⟨N', h₁', atom_map', h₂', h₃'⟩ | ⟨h₁', h₂'⟩ | ⟨N', hN', h₁', h₂'⟩ :=
      σ.property.forward.atom_cond L₂ A,
    { cases (σ.property.backward.one_to_one A).near_litter _ hL₂ h₁',
      rw h₃' at haN₂,
      obtain ⟨a₂, ha₂⟩ := haN₂,
      have map₂ := h₂' a₂ a₂.property,
      rw subtype.coe_eta at map₂,
      rw ha₂ at map₂,

      obtain ⟨⟨a₁L, a₁⟩, ha₁'⟩ := a₁,
      obtain ⟨⟨a₂L, a₂⟩, ha₂'⟩ := a₂,
      cases (σ.property.forward.one_to_one A).atom a map₁ map₂, cases ha₁', cases ha₂', refl, },
    { cases h₁' ⟨_, hL₂, rfl⟩, },
    { cases (σ.property.backward.one_to_one A).near_litter _ hL₂ hN',
      have := h₂' (h₂ a₁ a₁.property),
      rw subtype.coe_eta at this,
      rw ha₁ at this,
      obtain ⟨⟨a₁L, a₁⟩, ha₁'⟩ := a₁,
      cases this.mpr haN₂, cases ha₁', refl, }, },
  { cases h₁ ⟨_, hL₁, rfl⟩, },
  { cases (σ.property.backward.one_to_one A).near_litter _ hL₁ hN,
    obtain ⟨N', h₁', atom_map', h₂', h₃'⟩ | ⟨h₁', h₂'⟩ | ⟨N', hN', h₁', h₂'⟩ :=
      σ.property.forward.atom_cond L₂ A,
    { cases (σ.property.backward.one_to_one A).near_litter _ hL₂ h₁',
      rw h₃' at haN₂,
      obtain ⟨a₂, ha₂⟩ := haN₂,
      have map₂ := h₂' a₂ a₂.property,
      rw subtype.coe_eta at map₂,
      rw ha₂ at map₂,

      have := h₂ (h₂' a₂ a₂.property),
      rw subtype.coe_eta at this,
      rw ha₂ at this,
      obtain ⟨⟨a₂L, a₂⟩, ha₂'⟩ := a₂,
      cases this.mpr haN₁, cases ha₂', refl, },
    { cases h₁' ⟨_, hL₂, rfl⟩, },
    { cases (σ.property.backward.one_to_one A).near_litter _ hL₂ hN',

      obtain ⟨M₁, hM₁, s₁, hs₁, gs₁⟩ := σ.property.backward.near_litter_cond _ _ A hL₁,
      obtain ⟨M₂, hM₂, s₂, hs₂, gs₂⟩ := σ.property.backward.near_litter_cond _ _ A hL₂,
      dsimp only at gs₁ gs₂,

      cases set.eq_empty_or_nonempty ((N₁.snd.val \ litter_set N₁.fst) ∩ N₂.snd) with hN₁ hN₁,
      { cases set.eq_empty_or_nonempty ((N₂.snd.val \ litter_set N₂.fst) ∩ N₁.snd) with hN₂ hN₂,
        { rw set.eq_empty_iff_forall_not_mem at hN₁ hN₂, specialize hN₁ a, specialize hN₂ a,
          rw [set.mem_inter_iff, and_comm, set.mem_diff] at hN₁ hN₂,
          push_neg at hN₁ hN₂, specialize hN₁ haN₂ haN₁, specialize hN₂ haN₁ haN₂,
          have := eq_of_mem_litter_set_of_mem_litter_set hN₁ hN₂,
          rw this at hM₁,
          have M₁_eq_M₂ := (σ.property.forward.one_to_one A).near_litter _ hM₁ hM₂,
          dsimp only at M₁_eq_M₂, subst M₁_eq_M₂,
          refine litter_set.near_iff _,
          rw [gs₁, gs₂],
          unfold is_near,
          rw [symm_diff_left_comm, ← symm_diff_assoc, symm_diff_symm_diff_cancel_left],
          refine lt_of_le_of_lt
            (cardinal.mk_le_mk_of_subset $ symm_diff_le_sup (set.range s₁) (set.range s₂)) _,
          refine lt_of_le_of_lt (cardinal.mk_union_le _ _) _,
          refine cardinal.add_lt_of_lt κ_regular.aleph_0_le
            (lt_of_le_of_lt cardinal.mk_range_le N₁.snd.property)
            (lt_of_le_of_lt cardinal.mk_range_le N₂.snd.property), },
        { obtain ⟨aN₂, haN₂, haN₂'⟩ := hN₂,
          have := hs₂ ⟨aN₂, or.inr haN₂⟩,
          exact eq_of_mem_litter_set_of_mem_litter_set
            ((h₂ this).symm.mp haN₂') ((h₂' this).symm.mp haN₂.left), } },
      { obtain ⟨aN₁, haN₁, haN₁'⟩ := hN₁,
          have := hs₁ ⟨aN₁, or.inr haN₁⟩,
          exact eq_of_mem_litter_set_of_mem_litter_set
            ((h₂ this).symm.mp haN₁.left) ((h₂' this).symm.mp haN₁'), }, }, },
end

lemma litter_image_disjoint (σ : allowable_partial_perm B) (A : extended_index B)
  {L₁ L₂ : litter} {N₁ N₂ : near_litter}
  (hN₁ : (sum.inr (L₁.to_near_litter, N₁), A) ∈ σ.val)
  (hN₂ : (sum.inr (L₂.to_near_litter, N₂), A) ∈ σ.val) :
  L₁ ≠ L₂ → disjoint N₁.snd.val N₂.snd.val :=
begin
  contrapose!,
  rw set.not_disjoint_iff,
  rintro ⟨a, ha₁, ha₂⟩,
  exact litter_eq_of_image_inter B σ A hN₁ hN₂ a ha₁ ha₂,
end

-- An application of the near litter condition using litter_image_disjoint.
lemma near_litter_image_disjoint (σ : allowable_partial_perm B) (A : extended_index B)
  {N M N' M' : near_litter}
  (hN : (sum.inr (N, N'), A) ∈ σ.val) (hM : (sum.inr (M, M'), A) ∈ σ.val) :
  disjoint N.snd.val M.snd.val → disjoint N'.snd.val M'.snd.val :=
sorry

end values

/-! The next few lemmas are discussed in "FoA proof sketch completion". -/

-- TODO: Generalise and improve the naming of the following lemmas.

section exists_ge_atom

/-!
Suppose that we have an atom whose litter is specified in `σ`. We want to extend `σ` such that all
of the atoms in this litter are now specified. To do this, we construct an arbitrary bijection of
the unassigned atoms in the litter in the domain with the unassigned atoms in the litter's image.
-/

variables (σ : allowable_partial_perm B) (a : atom) (A : extended_index B) (N : near_litter)

lemma atom_value_inj_range (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  set.range (λ (b : {b : atom | b ∈ litter_set a.fst ∧ (sum.inl b, A) ∈ σ.val.domain}),
    (atom_value_inj B σ A) ⟨b.val, b.property.right⟩) =
  {b : atom | b ∈ N.snd.val ∧ (sum.inl b, A) ∈ σ.val.range} :=
begin
  rw set.range_eq_iff,
  refine ⟨λ c, ⟨_, _⟩, λ c hc, _⟩,
  { dsimp only [atom_value_inj, subtype.coe_mk, embedding.coe_fn_mk],
    have := atom_value_spec B σ A c c.property.right,
    obtain ⟨N', h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N', hN, h₁, h₂⟩ :=
      σ.property.forward.atom_cond a.fst A,
    { cases (σ.property.backward.one_to_one A).near_litter _ ha h₁,
      rw h₃,
      rw set.mem_range,
      refine ⟨⟨c, c.2.1⟩, _⟩,
      rw (σ.property.backward.one_to_one A).atom _ (h₂ c c.2.1) this, refl, },
    { cases h₁ ⟨_, ha, rfl⟩, },
    { cases (σ.property.backward.one_to_one A).near_litter _ ha hN,
      exact (h₂ this).mp c.property.left, }, },
  { exact ⟨_, atom_value_spec B σ A c c.property.right, rfl⟩, },
  { obtain ⟨hc, ⟨⟨⟨a₁, a₂⟩ | Ns, C⟩, hd₁, hd₂⟩⟩ := hc,
    { cases hd₂,
      refine ⟨⟨a₁, _, ⟨_, hd₁, rfl⟩⟩, (σ.property.backward.one_to_one A).atom a₁
        (atom_value_spec B σ A a₁ ⟨_, hd₁, rfl⟩) hd₁⟩,
      obtain ⟨M, hM, s, hs₁, hs₂⟩ := σ.property.backward.near_litter_cond _ _ _ ha,
      dsimp only at hs₂,
      by_cases c ∈ litter_set N.fst,
      { obtain ⟨N', h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N', hN, h₁, h₂⟩ :=
          σ.property.backward.atom_cond N.fst A,
        { cases (σ.property.forward.one_to_one A).near_litter _ h₁ hM,
          cases (σ.property.forward.one_to_one A).atom _ (h₂ c h) hd₁,
          rw [hs₂, h₃],
          refine or.inl ⟨⟨_, rfl⟩, _⟩,
          rintro ⟨d, hd⟩,
          have := hs₁ d,
          rw hd at this,
          cases (σ.property.backward.one_to_one A).atom _ this hd₁,
          obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := d.property,
          { exact h₂ hc, },
          { exact h₂ h, }, },
        { cases h₁ ⟨_, hM, rfl⟩,  },
        { cases (σ.property.forward.one_to_one A).near_litter _ hM hN,
          rw hs₂,
          refine or.inl ⟨(h₂ hd₁).mp h, _⟩,
          rintro ⟨d, hd⟩,
          have := hs₁ d,
          rw hd at this,
          cases (σ.property.backward.one_to_one A).atom _ this hd₁,
          obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := d.property,
          { exact h₂ hc, },
          { exact h₂ h, } }, },
      { have := (σ.property.forward.one_to_one A).atom _ hd₁ (hs₁ ⟨c, or.inr ⟨hc, h⟩⟩),
        dsimp only at this, subst this,
        rw hs₂, refine or.inr ⟨⟨_, rfl⟩, _⟩,
        obtain ⟨N', h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N', hN, h₁, h₂⟩ :=
          σ.property.backward.atom_cond N.fst A,
        { cases (σ.property.forward.one_to_one A).near_litter _ h₁ hM,
          rw h₃,
          rintro ⟨d, hd⟩,
          have := h₂ d d.property,
          rw [subtype.coe_eta, hd] at this,
          cases (σ.property.backward.one_to_one A).atom _ hd₁ this,
          exact h d.property, },
        { cases h₁ ⟨_, hM, rfl⟩, },
        { cases (σ.property.forward.one_to_one A).near_litter _ hM hN,
          rw ← h₂ hd₁, exact h, } }, },
    { cases hd₂, } }
end

/-- The domain and range of an allowable partial permutation, restricted to a given litter, are
equivalent. The equivalence produced by this function is induced by the allowable partial
permutation itself, so if this function maps an atom `a` to `b`, we have `π_A(a) = b` for all
allowable `π` satisfying `σ`. -/
noncomputable def cond_domain_range_equiv (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  {b | b ∈ litter_set a.fst ∧ (sum.inl b, A) ∈ σ.val.domain} ≃
  {b | b ∈ N.snd.val ∧ (sum.inl b, A) ∈ σ.val.range} :=
begin
  convert equiv.of_injective (λ (b : {b | b ∈ litter_set a.fst ∧ (sum.inl b, A) ∈ σ.val.domain}),
    atom_value_inj B σ A ⟨b.val, b.property.right⟩) _ using 2,
  { symmetry, exact atom_value_inj_range B σ a A N ha, },
  { intros b₁ b₂ hb,
    simpa only [subtype.mk_eq_mk, subtype.val_inj] using
      @function.embedding.injective _ _ (atom_value_inj B σ A)
        ⟨b₁.val, b₁.property.right⟩ ⟨b₂.val, b₂.property.right⟩ hb, },
end

/-- If we are in the "small" case (although this holds in both cases), the amount of atoms in a
given litter whose positions we have not defined so far is the same as the amount of atoms in the
resulting near-litter which are not the image of anything under `σ`. This means we can construct an
arbitrary bijection of these remaining atoms, "filling out" the specification to define the
permutation of all atoms in the litter to the atoms in the resulting near-litter. -/
lemma equiv_not_mem_atom (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  #↥{a' ∈ litter_set a.fst | (⟨sum.inl a', A⟩ : support_condition B) ∉ σ.val.domain} =
    #↥{a' ∈ N.snd.val | (⟨sum.inl a', A⟩ : support_condition B) ∉ σ.val.range} :=
begin
  have h₁ : #↥{a' ∈ litter_set a.fst | (⟨sum.inl a', A⟩ : support_condition B) ∉ σ.val.domain} = #κ,
  { cases le_iff_eq_or_lt.mp (cardinal.mk_le_mk_of_subset (show
      {a' ∈ litter_set a.fst | (⟨sum.inl a', A⟩ : support_condition B) ∉ σ.val.domain}
        ⊆ litter_set a.fst, by simp only [set.sep_subset])),
    { rw [h, mk_litter_set], },
    { rw mk_litter_set at h,
      exfalso, refine (ne_of_lt $ cardinal.add_lt_of_lt κ_regular.aleph_0_le hsmall h) _,
      rw [cardinal.mk_sep, cardinal.mk_sep],
      convert cardinal.mk_sum_compl _ using 1,
      rw mk_litter_set, }, },
  have h₂' : #↥{a' ∈ N.snd.val | (⟨sum.inl a', A⟩ : support_condition B) ∈ σ.val.range} < #κ,
  { convert hsmall using 1,
    rw cardinal.eq,
    exact ⟨(cond_domain_range_equiv B σ a A N ha).symm⟩, },
  have h₂ : #↥{a' ∈ N.snd.val | (⟨sum.inl a', A⟩ : support_condition B) ∉ σ.val.range} = #κ,
  { cases le_iff_eq_or_lt.mp (cardinal.mk_le_mk_of_subset (show
      {a' ∈ N.snd.val | (⟨sum.inl a', A⟩ : support_condition B) ∉ σ.val.range}
        ⊆ N.snd.val, by simp only [set.sep_subset])),
    { rw [h, N.snd.property.mk_eq_κ], },
    { rw N.snd.property.mk_eq_κ at h,
      exfalso, refine (ne_of_lt $ cardinal.add_lt_of_lt κ_regular.aleph_0_le h₂' h) _,
      rw [cardinal.mk_sep, cardinal.mk_sep],
      convert cardinal.mk_sum_compl _ using 1,
      rw N.snd.property.mk_eq_κ, }, },
  rw [h₁, h₂],
end

private noncomputable def atom_map
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  ↥{a' ∈ litter_set a.fst | (⟨sum.inl a', A⟩ : support_condition B) ∉ σ.val.domain} ≃
    ↥{a' ∈ N.snd.val | (⟨sum.inl a', A⟩ : support_condition B) ∉ σ.val.range} :=
(cardinal.eq.mp $ equiv_not_mem_atom B σ a A N hsmall ha).some

/-- The binary condition associated with this atom. -/
private noncomputable def atom_to_cond
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  {a' ∈ litter_set a.fst | (⟨sum.inl a', A⟩ : support_condition B) ∉ σ.val.domain} →
    binary_condition B :=
λ b, (sum.inl ⟨b, atom_map B σ a A N hsmall ha b⟩, A)

lemma atom_to_cond_spec (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (b) : ∃ c, atom_to_cond B σ a A N hsmall ha b = (sum.inl (b, c), A) ∧
    (c ∈ N.snd.val ∧ (sum.inl c, A) ∉ σ.val.range) :=
⟨atom_map B σ a A N hsmall ha b, rfl, (atom_map B σ a A N hsmall ha b).property⟩

lemma atom_to_cond_eq (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  {b c d e f C D} (hb : atom_to_cond B σ a A N hsmall ha b = (sum.inl (d, e), C))
  (hc : atom_to_cond B σ a A N hsmall ha c = (sum.inl (d, f), D)) :
  e = f ∧ C = D :=
begin
  simp only [atom_to_cond, prod.mk.inj_iff] at hb hc,
  obtain ⟨⟨h1, h2⟩, h3⟩ := hb,
  obtain ⟨⟨h1', h2'⟩, h3'⟩ := hc,
  rw [subtype.coe_inj.1 (h1.trans h1'.symm), h2'] at h2,
  exact ⟨h2.symm, h3.symm.trans h3'⟩,
end

lemma atom_to_cond_eq' (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  {b c d e f C D} (hb : atom_to_cond B σ a A N hsmall ha b = (sum.inl (e, d), C))
  (hc : atom_to_cond B σ a A N hsmall ha c = (sum.inl (f, d), D)) :
  e = f ∧ C = D :=
begin
  simp only [atom_to_cond, prod.mk.inj_iff] at hb hc,
  obtain ⟨⟨h1, h2⟩, h3⟩ := hb,
  obtain ⟨⟨h1', h2'⟩, h3'⟩ := hc,
  rw [← h2', subtype.coe_inj, embedding_like.apply_eq_iff_eq] at h2,
  exact ⟨h1.symm.trans ((subtype.coe_inj.2 h2).trans h1'), h3.symm.trans h3'⟩,
end

lemma exists_atom_to_cond (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  {c : atom} (hc₁ : c ∈ N.snd.val) (hc₂ : (sum.inl c, A) ∉ σ.val.range) :
  ∃ d, atom_to_cond B σ a A N hsmall ha d = (sum.inl (d, c), A) :=
begin
  obtain ⟨d, hd⟩ : (⟨c, hc₁, hc₂⟩ : ↥{a' ∈ N.snd.val | _}) ∈ set.range (atom_map B σ a A N hsmall ha),
  { rw equiv.range_eq_univ, exact set.mem_univ _, },
  refine ⟨d, _⟩, unfold atom_to_cond, rw hd, refl,
end

lemma atom_union_one_to_one_forward (hc : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  spec.one_to_one_forward B (σ.val ∪ set.range (atom_to_cond B σ a A N hsmall ha)) :=
begin
  refine λ C, ⟨λ b p hp q hq, _, λ N' M hM M' hM', _⟩,
  { simp only [subtype.val_eq_coe, set.mem_sep_eq, set.mem_set_of_eq,
               set.mem_union_eq, set.mem_range, set_coe.exists] at hp hq,
    obtain hp | ⟨x, ⟨hxa, hxσ⟩, hx⟩ := hp; obtain hq | ⟨y, ⟨hya, hyσ⟩, hy⟩ := hq,
    { exact (σ.prop.forward.one_to_one C).atom b hp hq },
    { obtain ⟨c, hcond, hc, hcnin⟩ := atom_to_cond_spec B σ a A N hsmall ha ⟨y, hya, hyσ⟩,
      cases hy.symm.trans hcond,
      cases hcnin ⟨_, hp, rfl⟩ },
    { obtain ⟨c, hcond, hc, hcnin⟩ := atom_to_cond_spec B σ a A N hsmall ha ⟨x, hxa, hxσ⟩,
      cases hx.symm.trans hcond,
      cases hcnin ⟨_, hq, rfl⟩ },
    { exact (atom_to_cond_eq' B σ a A _ hsmall ha hx hy).1, } },
  simp only [subtype.val_eq_coe, set.mem_sep_eq, set.mem_set_of_eq,
             set.mem_union_eq, set.mem_range, set_coe.exists] at hM hM',
  obtain hM | ⟨x, ⟨hxa, hxσ⟩, hx⟩ := hM,
  { obtain hM' | ⟨y, ⟨hya, hyσ⟩, hy⟩ := hM',
    { exact (σ.prop.forward.one_to_one C).near_litter N' hM hM' },
    simp only [atom_to_cond, prod.mk.inj_iff, false_and] at hy,
    cases hy },
  { simp only [atom_to_cond, prod.mk.inj_iff, false_and] at hx,
    cases hx }
end

lemma atom_union_one_to_one_backward (hc : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  spec.one_to_one_forward B (σ.val ∪ set.range (atom_to_cond B σ a A N hsmall ha))⁻¹ :=
begin
  refine λ C, ⟨λ b p hp q hq, _, λ N' M hM M' hM', _⟩,
  { simp only [subtype.val_eq_coe, set.mem_sep_eq, set.mem_set_of_eq,
               set.mem_union_eq, set.mem_range, set_coe.exists, set.mem_inv] at hp hq,
    obtain hp | ⟨x, ⟨hxa, hxσ⟩, hx⟩ := hp; obtain hq | ⟨y, ⟨hya, hyσ⟩, hy⟩ := hq,
    { exact (σ.prop.backward.one_to_one C).atom b hp hq },
    { obtain ⟨⟨h1, h2⟩, h3⟩ := hy, -- auto subst what???
      simp only [has_inv.inv, sum.elim_inl] at hp,
      cases hyσ ⟨_, hp, by simp only [binary_condition.domain, sum.elim_inl]⟩ },
    { obtain ⟨⟨h1, h2⟩, h3⟩ := hx, -- same as above
      simp only [has_inv.inv, sum.elim_inl] at hq,
      cases hxσ ⟨_, hq, by simp only [binary_condition.domain, sum.elim_inl]⟩ },
    { exact (atom_to_cond_eq B σ a A _ hsmall ha hx hy).1 } },
  obtain hM | ⟨x, ⟨hxa, hxσ⟩, hx⟩ := hM,
  obtain hM' | ⟨y, ⟨hya, hyσ⟩, hy⟩ := hM',
  exact (σ.prop.backward.one_to_one C).near_litter N' hM hM'
end

lemma atom_union_atom_cond_forward (hc : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  ∀ L C, spec.atom_cond B (σ.val ∪ set.range (atom_to_cond B σ a A N hsmall ha)) L C :=
begin
  intros L C,
  obtain ⟨L', hL, atom_map, hin, himg⟩ | ⟨hL, hLsmall⟩ | ⟨L', hL, hLsmall, hmaps⟩ := σ.prop.forward.atom_cond L C,
  { exact spec.atom_cond.all L' (or.inl hL) atom_map (λ a ha, or.inl (hin a ha)) himg },
  { by_cases a.fst ≠ L ∨ A ≠ C,
    { refine spec.atom_cond.small_out _ _,
      { unfold spec.domain,
        rintro ⟨⟨_ | ⟨N, M⟩, D⟩, hin | hin, hdom⟩; cases hdom,
        { exact hL ⟨_, hin, rfl⟩ },
        { unfold atom_to_cond at hin,
          cases hin with _ hin, cases hin } },
      unfold small spec.domain,
      rw set.image_union,
      have : {a_1 ∈ litter_set L | (sum.inl a_1, C) ∈
        binary_condition.domain '' σ.val ∪ binary_condition.domain '' set.range (atom_to_cond B σ a A N hsmall ha)} = {a_1 ∈ litter_set L | (sum.inl a_1, C) ∈
          binary_condition.domain '' σ.val} ∪ {a_1 ∈ litter_set L | (sum.inl a_1, C) ∈
            binary_condition.domain '' set.range (atom_to_cond B σ a A N hsmall ha)},
      { ext,
        simp only [subtype.val_eq_coe, set.mem_sep_eq, set.mem_union_eq, set.mem_image, set.mem_range, set_coe.exists],
        split,
        { rintro ⟨hL, h | h⟩,
          { exact or.inl ⟨hL, h⟩ },
          { exact or.inr ⟨hL, h⟩ } },
        { rintro (⟨hL, h⟩ | ⟨hL, h⟩),
          { exact ⟨hL, or.inl h⟩ },
          { exact ⟨hL, or.inr h⟩ } } },
      rw this,
      convert lt_of_le_of_lt (cardinal.mk_union_le _ _) (cardinal.add_lt_of_lt κ_regular.aleph_0_le
        hLsmall $ lt_of_eq_of_lt (cardinal.mk_emptyc _) κ_regular.pos),
      simp only [binary_condition.domain, subtype.val_eq_coe, set.mem_sep_eq,
                 set.mem_image, set.mem_range, set_coe.exists,
  prod.mk.inj_iff],
      cases h,
      { refine funext (λ x, eq_iff_iff.2 ⟨_, λ h, by cases h⟩),
        rintro ⟨hx, ⟨⟨x', y⟩ | _, b⟩, ⟨_, ⟨ha, _⟩, hb1⟩, hb2, -⟩,
        { simp only [atom_to_cond, sum.elim_inl, subtype.coe_mk, prod.mk.inj_iff] at hb1 hb2,
          obtain ⟨⟨rfl, -⟩, -⟩ := hb1,
          subst hb2,
          exact pairwise_disjoint_litter_set a.fst L h ⟨ha, hx⟩, },
        { cases hb1 } },
      { refine set.ext (λ x, ⟨_, λ hx, by cases hx⟩),
        rintro ⟨hL, ⟨b1, b2⟩, ⟨_, _, h1⟩, -, h2⟩,
        have := congr_arg prod.snd h1,
        simp only [atom_to_cond] at h2 this,
        exact h (this.trans h2) } },
    { obtain ⟨rfl, rfl⟩ := and_iff_not_or_not.2 h,
      cases hL ⟨_, ha, rfl⟩, } },
  { by_cases a.fst ≠ L ∨ A ≠ C,
    { refine spec.atom_cond.small_in L' (or.inl hL) _ _,
      { unfold small spec.domain,
        rw set.image_union,
        have : {a_1 ∈ litter_set L | (sum.inl a_1, C) ∈
          binary_condition.domain '' σ.val ∪ binary_condition.domain ''
            set.range (atom_to_cond B σ a A N hsmall ha)} = {a_1 ∈ litter_set L | (sum.inl a_1, C) ∈
              binary_condition.domain '' σ.val} ∪ {a_1 ∈ litter_set L | (sum.inl a_1, C) ∈
                binary_condition.domain '' set.range (atom_to_cond B σ a A N hsmall ha)},
        { ext,
          simp only [subtype.val_eq_coe, set.mem_sep_eq, set.mem_union_eq, set.mem_image, set.mem_range, set_coe.exists],
          split,
          { rintro ⟨hL, h | h⟩,
            { exact or.inl ⟨hL, h⟩ },
            { exact or.inr ⟨hL, h⟩ } },
          { rintro (⟨hL, h⟩ | ⟨hL, h⟩),
            { exact ⟨hL, or.inl h⟩ },
            { exact ⟨hL, or.inr h⟩ } } },
        rw this,
        convert lt_of_le_of_lt (cardinal.mk_union_le _ _) (cardinal.add_lt_of_lt κ_regular.aleph_0_le hLsmall
            (lt_of_eq_of_lt (cardinal.mk_emptyc _) κ_regular.pos)),
        simp only [binary_condition.domain, subtype.val_eq_coe, set.mem_sep_eq,
                  set.mem_image, set.mem_range, set_coe.exists,
    prod.mk.inj_iff],
        cases h,
        { refine funext (λ x, eq_iff_iff.2 ⟨_, λ h, by cases h⟩),
          rintro ⟨hx, ⟨⟨x', y⟩ | _, b⟩, ⟨_, ⟨ha, _⟩, hb1⟩, hb2, -⟩,
          { simp only [atom_to_cond, sum.elim_inl, subtype.coe_mk, prod.mk.inj_iff] at hb1 hb2,
            obtain ⟨⟨rfl, -⟩, -⟩ := hb1,
            subst hb2,
            exact pairwise_disjoint_litter_set a.fst L h ⟨ha, hx⟩, },
          { cases hb1 } },
        { refine set.ext (λ x, ⟨_, λ hx, by cases hx⟩),
          rintro ⟨hL, ⟨b1, b2⟩, ⟨_, _, h1⟩, -, h2⟩,
          have := congr_arg prod.snd h1,
          simp only [atom_to_cond] at h2 this,
          exact h (this.trans h2) } },
      { refine λ c d hcdu, or.rec (@hmaps c d) _ hcdu,
        rintro ⟨c, hcond⟩,
        cases hcond,
        simp only [ne.def, eq_self_iff_true, not_true, or_false] at h,
        refine ⟨λ hc, by cases pairwise_disjoint_litter_set _ _ h ⟨c.prop.1, hc⟩, _⟩,
        intro hL',
        cases litter_image_disjoint B σ A ha hL h ⟨(atom_map B σ a A N hsmall ha c).prop.1, hL'⟩, } },
    { classical,
      obtain ⟨rfl, rfl⟩ := and_iff_not_or_not.2 h,
      obtain rfl := (σ.prop.backward.one_to_one A).near_litter _ ha hL,
      refine spec.atom_cond.all N (or.inl ha)
        (λ x, dite ((sum.inl x.val, A) ∈ σ.val.domain)
          (λ hx, atom_value B σ A x hx)
          (λ hx, (atom_map B σ a A N hsmall ha ⟨x.val, x.prop, hx⟩).val))
        (λ y hy, _) (set.ext $ λ x, ⟨λ hx, _, λ hx, _⟩),
      { by_cases (sum.inl y, A) ∈ σ.val.domain,
        { rw dif_pos h,
          exact or.inl (atom_value_spec B σ A y h) },
        { rw dif_neg h,
          exact or.inr ⟨⟨y, hy, h⟩, rfl⟩ } },
      { by_cases (sum.inl x, A) ∈ σ.val.range,
        { obtain ⟨⟨⟨y, _⟩ | _, _⟩, hin, hxy⟩ := h; cases hxy,
          have hya : y ∈ litter_set a.fst := (hmaps hin).2 hx,
          use ⟨y, hya⟩,
          dsimp only,
          have : (sum.inl y, A) ∈ σ.val.domain := ⟨_, hin, rfl⟩,
          rw dif_pos this,
          exact (σ.prop.backward.one_to_one A).atom y (atom_value_spec B σ A y ⟨_, hin, rfl⟩) hin },
        { obtain ⟨d, hd⟩ := exists_atom_to_cond B σ a A N hsmall ha hx h,
          use ⟨coe d, d.prop.1⟩,
          dsimp only,
          rw dif_neg d.prop.2,
          simpa only [atom_to_cond, subtype.coe_eta, prod.mk.inj_iff,
                      eq_self_iff_true, true_and, and_true] using hd, } },
      { obtain ⟨y, rfl⟩ := hx,
        by_cases (sum.inl y.val, A) ∈ σ.val.domain,
        { simp_rw dif_pos h,
          exact (hmaps $ atom_value_spec B σ A y.val h).1 y.prop },
        { simp_rw dif_neg h,
          obtain ⟨c, hcy, hcN, hcnin⟩ := atom_to_cond_spec B σ a A N hsmall ha ⟨y.val, y.prop, h⟩,
          simp only [atom_to_cond, prod.mk.inj_iff, eq_self_iff_true, true_and, and_true] at hcy,
          rw ← hcy at hcN,
          exact hcN } } } },
end

lemma atom_union_atom_cond_backward (hc : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  ∀ L C, spec.atom_cond B (σ.val ∪ set.range (atom_to_cond B σ a A N hsmall ha))⁻¹ L C :=
begin
  intros L C,
  obtain ⟨L', hL, atom_map, hin, himg⟩ | ⟨hL, hLsmall⟩ | ⟨L', hL, hLsmall, hmaps⟩ := σ.prop.backward.atom_cond L C,
  { exact spec.atom_cond.all L' (or.inl hL) atom_map (λ a H, or.inl $ hin a H) himg },
  { by_cases N.fst = L,
    { subst h,
      refine spec.atom_cond.small_out _ _,
      { rintro ⟨⟨_ | ⟨x, y⟩, D⟩, hb | hb, hdom⟩; cases hdom,
        { exact hL ⟨_, hb, hdom⟩ },
        cases hb.some_spec, },
        rw spec.inv_domain at hLsmall ⊢,
        unfold spec.range,
        rw set.image_union,
        have : {a_1 ∈ litter_set N.fst | (sum.inl a_1, C) ∈
          binary_condition.range '' σ.val ∪ binary_condition.range '' set.range (atom_to_cond B σ a A N hsmall ha)} = {a_1 ∈ litter_set N.fst | (sum.inl a_1, C) ∈
            binary_condition.range '' σ.val} ∪ {a_1 ∈ litter_set N.fst | (sum.inl a_1, C) ∈
              binary_condition.range '' set.range (atom_to_cond B σ a A N hsmall ha)},
        { ext,
          simp only [subtype.val_eq_coe, set.mem_sep_eq, set.mem_union_eq, set.mem_image, set.mem_range, set_coe.exists],
          split,
          { rintro ⟨hL, h | h⟩,
            { exact or.inl ⟨hL, h⟩ },
            { exact or.inr ⟨hL, h⟩ } },
          { rintro (⟨hL, h⟩ | ⟨hL, h⟩),
            { exact ⟨hL, or.inl h⟩ },
            { exact ⟨hL, or.inr h⟩ } } },
        rw this,
        by_cases A = C,
        { subst h,
          refine lt_of_le_of_lt (cardinal.mk_union_le _ _) (cardinal.add_lt_of_lt κ_regular.aleph_0_le hLsmall _),
          unfold atom_to_cond,
          cases hL ⟨_, (σ.prop.backward.near_litter_cond N a.fst.to_near_litter A ha).some_spec.1, rfl⟩ },
        { convert lt_of_le_of_lt (cardinal.mk_union_le _ _) (cardinal.add_lt_of_lt κ_regular.aleph_0_le
              hLsmall $ lt_of_eq_of_lt (cardinal.mk_emptyc _) κ_regular.pos),
          refine set.ext (λ x, ⟨_, λ hx, hx.rec _⟩),
          rintro ⟨-, ⟨_, _⟩, ⟨_, hb⟩, hx⟩,
          unfold atom_to_cond at hb,
          cases hb, cases hx, cases h rfl } },
    { sorry } },
  { sorry }
end

lemma atom_union_near_litter_cond_forward (hc : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  ∀ N₁ N₂ C,
    spec.near_litter_cond B (σ.val ∪ set.range (atom_to_cond B σ a A N hsmall ha)) N₁ N₂ C :=
begin
  rintros N₁ N₂ C (h | h),
  { obtain ⟨M, hM₁, sd, hsd₁, hsd₂⟩ := σ.property.forward.near_litter_cond N₁ N₂ C h,
    exact ⟨M, or.inl hM₁, sd, λ a, or.inl (hsd₁ a), hsd₂⟩, },
  obtain ⟨d, hd⟩ := h,
  cases hd,
end

lemma atom_union_near_litter_cond_backward (hc : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  ∀ N₁ N₂ C,
    spec.near_litter_cond B (σ.val ∪ set.range (atom_to_cond B σ a A N hsmall ha))⁻¹ N₁ N₂ C :=
begin
  rintros N₁ N₂ C (h | h),
  { obtain ⟨M, hM₁, sd, hsd₁, hsd₂⟩ := σ.property.backward.near_litter_cond N₁ N₂ C h,
    exact ⟨M, or.inl hM₁, sd, λ a, or.inl (hsd₁ a), hsd₂⟩, },
  obtain ⟨d, hd⟩ := h,
  cases hd,
end

lemma atom_union_non_flexible_cond_forward (hc : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  spec.non_flexible_cond B (σ.val ∪ set.range (atom_to_cond B σ a A N hsmall ha)) :=
begin
  rintros β δ γ hγ hδ hγδ N₁ C t (ht | ht) ρ hρ,
  { exact σ.property.forward.non_flexible_cond hγ hδ hγδ N₁ C t ht ρ
      (struct_perm.satisfies_union_left _ _ _ hρ), },
  obtain ⟨d, hd⟩ := ht,
  cases hd,
end

lemma atom_union_non_flexible_cond_backward (hc : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  spec.non_flexible_cond B (σ.val ∪ set.range (atom_to_cond B σ a A N hsmall ha))⁻¹ :=
begin
  rintros β δ γ hγ hδ hγδ N₁ C t (ht | ht) ρ hρ,
  { exact σ.property.backward.non_flexible_cond hγ hδ hγδ N₁ C t ht ρ
      (struct_perm.satisfies_union_left _ _ _ hρ), },
  obtain ⟨d, hd⟩ := ht,
  cases hd,
end

lemma atom_union_support_closed_forward (hc : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  (σ.val ∪ set.range (atom_to_cond B σ a A N hsmall ha)).domain.support_closed B :=
begin
  intros β δ γ hγ hδ hγδ C t ht,
  rw spec.domain_union at ht ⊢,
  rw unary_spec.lower_union,
  cases ht,
  { exact supports_union_left (σ.property.forward.support_closed hγ hδ hγδ C t ht), },
  obtain ⟨⟨atoms | Ns, C⟩, ⟨d, hd₁⟩, hd₂⟩ := ht,
  { cases hd₂, },
  { cases hd₁, },
end

lemma atom_union_support_closed_backward (hc : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  (σ.val ∪ set.range (atom_to_cond B σ a A N hsmall ha)).range.support_closed B :=
begin
  intros β δ γ hγ hδ hγδ C t ht,
  rw spec.range_union at ht ⊢,
  rw unary_spec.lower_union,
  cases ht,
  { convert supports_union_left (σ.property.backward.support_closed hγ hδ hγδ C t
      (by { rw spec.inv_domain, exact ht })),
    rw spec.inv_domain, },
  obtain ⟨⟨atoms | Ns, C⟩, ⟨d, hd₁⟩, hd₂⟩ := ht,
  { cases hd₂, },
  { cases hd₁, },
end

lemma atom_union_flexible_cond (hc : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  ∀ C, spec.flexible_cond B (σ.val ∪ set.range (atom_to_cond B σ a A N hsmall ha)) C :=
begin
  intro C,
  obtain (⟨hdom, hrge⟩ | ⟨hdom, hrge⟩) := σ.property.flexible_cond C,
  { refine spec.flexible_cond.co_large _ _,
    { convert hdom, ext L, split,
      { rintro ⟨hC₁, hC₂⟩, rw spec.domain_union at hC₂,
        exact ⟨hC₁, λ h, hC₂ (set.mem_union_left _ h)⟩, },
      { rintro ⟨hC₁, hC₂⟩, refine ⟨hC₁, λ h, _⟩,
        rw spec.domain_union at h,
        cases h,
        { exact hC₂ h, },
        { obtain ⟨d, ⟨e, hd₁⟩, hd₂⟩ := h, cases hd₁, cases hd₂, } } },
    { convert hrge, ext L, split,
      { rintro ⟨hC₁, hC₂⟩, rw spec.range_union at hC₂,
        exact ⟨hC₁, λ h, hC₂ (set.mem_union_left _ h)⟩, },
      { rintro ⟨hC₁, hC₂⟩, refine ⟨hC₁, λ h, _⟩,
        rw spec.range_union at h,
        cases h,
        { exact hC₂ h, },
        { obtain ⟨d, ⟨e, hd₁⟩, hd₂⟩ := h, cases hd₁, cases hd₂, } } } },
  { refine spec.flexible_cond.all _ _,
    { intros L hL, rw spec.domain_union, exact or.inl (hdom L hL), },
    { intros L hL, rw spec.range_union, exact or.inl (hrge L hL), } },
end

/-- When we add the provided atoms from the atom map, we preserve allowability.

This lemma is going to be work, and we have three others just like it later.
Is there a way to unify all of the cases somehow, or at least avoid duplicating code?
At the moment, I can't see a way to use any less than eleven lemmas here, since the symmetry is
broken. -/
lemma atom_union_allowable (hc : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  spec.allowable_spec B (σ.val ∪ set.range (atom_to_cond B σ a A N hsmall ha)) := {
  forward := {
    one_to_one := atom_union_one_to_one_forward B σ a A N hc hsmall ha,
    atom_cond := atom_union_atom_cond_forward B σ a A N hc hsmall ha,
    near_litter_cond := atom_union_near_litter_cond_forward B σ a A N hc hsmall ha,
    non_flexible_cond := atom_union_non_flexible_cond_forward B σ a A N hc hsmall ha,
    support_closed := atom_union_support_closed_forward B σ a A N hc hsmall ha,
  },
  backward := {
    one_to_one := atom_union_one_to_one_backward B σ a A N hc hsmall ha,
    atom_cond := atom_union_atom_cond_backward B σ a A N hc hsmall ha,
    near_litter_cond := atom_union_near_litter_cond_backward B σ a A N hc hsmall ha,
    non_flexible_cond := atom_union_non_flexible_cond_backward B σ a A N hc hsmall ha,
    support_closed := by { rw spec.inv_domain,
      exact atom_union_support_closed_backward B σ a A N hc hsmall ha },
  },
  flexible_cond := atom_union_flexible_cond B σ a A N hc hsmall ha,
}

lemma atom_union_all_atoms_domain (hc : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) (b₁ b₂ : atom)
  (L : litter) (hb₁ : b₁ ∈ litter_set L) (C : extended_index B)
  (hσ : (⟨sum.inl ⟨b₁, b₂⟩, C⟩ : binary_condition B) ∈
    set.range (atom_to_cond B σ a A N hsmall ha)) :
  ∀ c ∈ litter_set L, ∃ d, (⟨sum.inl ⟨c, d⟩, C⟩ : binary_condition B) ∈
    σ.val ∪ set.range (atom_to_cond B σ a A N hsmall ha) :=
begin
  intros c hc,
  by_cases (⟨sum.inl c, C⟩ : support_condition B) ∈ σ.val.domain,
  { exact ⟨atom_value B σ C c h, or.inl (atom_value_spec B σ C c h)⟩, },
  obtain ⟨d, hd⟩ := hσ,
  have hd : b₁ = d,
  { unfold atom_to_cond at hd,
    have hd' := congr_arg prod.fst hd, have := congr_arg prod.fst (sum.inl.inj hd'),
    cases this, refl, },
  subst hd,
  have hL : L = a.fst := by { cases hb₁, obtain ⟨d, hd₁, hd₂⟩ := d, exact hd₁, },
  subst hL,
  have hC : A = C := by { cases hd, refl },
  subst hC,
  generalize he : atom_to_cond B σ a A N hsmall ha ⟨c, hc, h⟩ = e,
  obtain ⟨⟨e₁, e₂⟩ | Ns, E⟩ := e,
  { refine ⟨e₂, or.inr ⟨⟨c, hc, h⟩, _⟩⟩,
    cases he, exact he, },
  { unfold atom_to_cond at he, simpa only [prod.mk.inj_iff, false_and] using he, },
end

/-- The image of an element of a near-litter lies in the resulting near-litter. -/
lemma atom_union_mem (hc : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (b₁ b₂ : atom) (C : extended_index B)
  (hσ : (⟨sum.inl ⟨b₁, b₂⟩, C⟩ : binary_condition B) ∈
    set.range (atom_to_cond B σ a A N hsmall ha)) :
  b₂ ∈ (N.snd : set atom) :=
begin
  obtain ⟨d, hd⟩ := hσ,
  have : b₁ = d,
  { unfold atom_to_cond at hd,
    have hd' := congr_arg prod.fst hd, have := congr_arg prod.fst (sum.inl.inj hd'),
    cases this, refl, },
  subst this,
  obtain ⟨N', h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N', h₁, h₂, h₃⟩ :=
    atom_union_atom_cond_forward B σ a A N hc hsmall ha a.fst A,
  { obtain this | ⟨e, he⟩ := h₂ d d.property.left,
    { exfalso, exact d.property.right ⟨_, this, rfl⟩, },
    rw (atom_to_cond_eq B σ a A N hsmall ha hd he).left,
    rw (atom_union_one_to_one_backward B σ a A N hc hsmall ha A).near_litter
      a.fst.to_near_litter (or.inl hc) h₁,
    exact ((set.range_eq_iff _ _).mp h₃.symm).left _, },
  { exfalso, refine h₁ _, rw spec.domain_union, exact or.inl ⟨_, ha, rfl⟩, },
  { have : A = C,
    { cases hd, refl, },
    subst this,
    have := h₃ d d.property.left b₂ (or.inr ⟨d, hd⟩),
    rwa (atom_union_one_to_one_backward B σ a A N hc hsmall ha A).near_litter
        a.fst.to_near_litter (or.inl hc) h₁, }
end

/-- The atom map only ever maps to the intersection of `N` with its corresponding litter, `N.fst`.
In particular, we prove that if some atom `c` lies in the litter we're mapping to, it lies in the
precise near-litter we are mapping to as well. -/
lemma atom_union_mem' (hc : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (b₁ b₂ : atom) (C : extended_index B)
  (hσ : (⟨sum.inl ⟨b₁, b₂⟩, C⟩ : binary_condition B) ∈ set.range (atom_to_cond B σ a A N hsmall ha))
  (c : atom) (hc₁ : c ∈ litter_set b₂.fst) (hc₂ : (sum.inl c, A) ∉ σ.val.range) :
  c ∈ (N.snd : set atom) :=
begin
  contrapose hc₂,
  rw set.not_not_mem,

  suffices hb₂ : b₂.fst = N.fst,
  { rw hb₂ at hc₁,
    obtain ⟨M, hM, symm_diff, hS₁, hS₂⟩ :=
      σ.property.backward.near_litter_cond N a.fst.to_near_litter A hc,
    refine ⟨_, hS₁ ⟨c, or.inl ⟨hc₁, hc₂⟩⟩, rfl⟩, },

  obtain ⟨d, hd⟩ := hσ,
  have : b₁ = d,
  { unfold atom_to_cond at hd,
    have hd' := congr_arg prod.fst hd, have := congr_arg prod.fst (sum.inl.inj hd'),
    cases this, refl, },
  subst this,

  obtain ⟨M, hM, symm_diff, hS₁, hS₂⟩ :=
    σ.property.backward.near_litter_cond N a.fst.to_near_litter A hc,
  by_contradiction hb₂,
  have := hS₁ ⟨b₂, or.inr ⟨atom_union_mem B σ a A N hc hsmall ha d b₂ C ⟨d, hd⟩, hb₂⟩⟩,
  obtain ⟨e, he₁, he₂, he₃⟩ := atom_to_cond_spec B σ a A N hsmall ha d,
  rw hd at he₁,
  cases he₁,
  refine he₃ ⟨_, this, rfl⟩,
end

lemma atom_union_all_atoms_range (hc : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) (b₁ b₂ : atom)
  (L : litter) (hb₂ : b₂ ∈ litter_set L) (C : extended_index B)
  (hσ : (⟨sum.inl ⟨b₁, b₂⟩, C⟩ : binary_condition B) ∈
    set.range (atom_to_cond B σ a A N hsmall ha)) :
  ∀ c ∈ litter_set L, ∃ d, (⟨sum.inl ⟨d, c⟩, C⟩ : binary_condition B) ∈
    σ.val ∪ set.range (atom_to_cond B σ a A N hsmall ha) :=
begin
  have b₂_mem := atom_union_mem B σ a A N hc hsmall ha _ _ _ hσ,
  obtain ⟨d, hd⟩ := hσ,
  have : b₁ = d,
  { unfold atom_to_cond at hd,
    have hd' := congr_arg prod.fst hd, have := congr_arg prod.fst (sum.inl.inj hd'),
    cases this, refl, },
  subst this,
  have : A = C,
  { cases hd, refl, },
  subst this,
  have : N.fst = L,
  { cases hb₂,
    by_contradiction,
    obtain ⟨M, hM, symm_diff, hS₁, hS₂⟩ :=
      σ.property.backward.near_litter_cond N a.fst.to_near_litter A ‹_›,
    rw spec.inr_mem_inv at hM,
    have mem_symm_diff : b₂ ∈ litter_set N.fst ∆ N.snd := or.inr ⟨b₂_mem, ne.symm h⟩,
    have hS₁' := hS₁ ⟨b₂, mem_symm_diff⟩,
    rw spec.inl_mem_inv at hS₁',
    have : symm_diff ⟨b₂, mem_symm_diff⟩ = d :=
      (atom_union_one_to_one_forward B σ a A N hc hsmall ha A).atom b₂
        (or.inl hS₁') (or.inr ⟨_, hd⟩),
    refine d.property.right _,
    rw [subtype.val_eq_coe, ← this],
    exact ⟨_, hS₁', rfl⟩, },
  subst this,

  intros c hc,
  by_cases (⟨sum.inl c, A⟩ : support_condition B) ∈ σ.val.range,
  { obtain ⟨⟨⟨d₁, d₂⟩ | Ns, D⟩, hc₁, hc₂⟩ := h; cases hc₂,
    exact ⟨d₁, or.inl hc₁⟩, },
  have : c ∈ N.snd.val,
  { convert atom_union_mem' B σ a A N ‹_› hsmall ha d b₂ A ⟨d, hd⟩ _ _ h, convert hc, },
  refine ⟨(atom_map B σ a A N hsmall ha).inv_fun ⟨c, this, h⟩,
    or.inr ⟨(atom_map B σ a A N hsmall ha).inv_fun ⟨c, this, h⟩, _⟩⟩,
  unfold atom_to_cond,
  rw ← equiv.to_fun_as_coe,
  rw equiv.right_inv _,
  refl,
end

/-- When we add the atoms from the atom map, the resulting permutation "carefully extends" `σ`.
The atom conditions hold because `σ` is allowable and the `near_litter_cond` is satisfied - in
particular, the atoms in the symmetric difference between `N` and `N.fst.to_near_litter` are already
given in `σ`, so do not appear in the `atom_to_cond` map. -/
lemma le_atom_union (hc : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  σ ≤ ⟨σ.val ∪
    set.range (atom_to_cond B σ a A N hsmall ha), atom_union_allowable B σ a A N hc hsmall ha⟩ := {
  subset := set.subset_union_left _ _,
  all_flex_domain := begin
    intros L N' C hN' hσ₁ hσ₂,
    cases set.mem_or_mem_of_mem_union hσ₂,
    { exfalso, exact hσ₁ h, },
    simpa only [atom_to_cond, set.mem_range, prod.mk.inj_iff, false_and, exists_false] using h,
  end,
  all_flex_range := begin
    intros L N' C hN' hσ₁ hσ₂,
    cases set.mem_or_mem_of_mem_union hσ₂,
    { exfalso, exact hσ₁ h, },
    simpa only [atom_to_cond, set.mem_range, prod.mk.inj_iff, false_and, exists_false] using h,
  end,
  all_atoms_domain := begin
    intros b₁ b₂ L hb₁ C hC₁ hC₂ c hc',
    cases hC₂,
    { exfalso, exact hC₁ hC₂, },
    exact atom_union_all_atoms_domain B σ a A N hc hsmall ha b₁ b₂ L hb₁ C hC₂ c hc',
  end,
  all_atoms_range := begin
    intros b₁ b₂ L hb₁ C hC₁ hC₂ c hc',
    cases hC₂,
    { exfalso, exact hC₁ hC₂, },
    exact atom_union_all_atoms_range B σ a A N hc hsmall ha b₁ b₂ L hb₁ C hC₂ c hc',
  end,
}

/-- If everything that constrains an atom lies in `σ`, we can add the atom to `σ`, giving a new
allowable partial permutation `ρ ≥ σ`. -/
lemma exists_ge_atom (hσ : ∀ c, c ≺ (⟨sum.inl a, A⟩ : support_condition B) → c ∈ σ.val.domain) :
  ∃ ρ ≥ σ, (⟨sum.inl a, A⟩ : support_condition B) ∈ ρ.val.domain :=
begin
  by_cases haσ : (⟨sum.inl a, A⟩ : support_condition B) ∈ σ.val.domain,
  { exact ⟨σ, le_rfl, haσ⟩ },
  obtain ⟨⟨_ | ⟨_, N⟩, A⟩, hc₁, hc₂⟩ := hσ (⟨sum.inr a.fst.to_near_litter, A⟩ : support_condition B)
    (constrains.mem_litter a.fst a rfl _); cases hc₂,
  obtain hsmall | ⟨N', atom_map, hσ₁, hσ₂, hN'⟩ := σ.property.forward.atom_cond a.fst A,
  swap, { exfalso, exact haσ ⟨_, hσ₂ a rfl, rfl⟩, },
  have := equiv_not_mem_atom B σ a A N hsmall hc₁,
  exact ⟨_, le_atom_union B σ a A N hc₁ hsmall hc₁, _,
    set.mem_union_right _ ⟨⟨a, rfl, haσ⟩, rfl⟩, rfl⟩,
end

end exists_ge_atom

section exists_ge_near_litter

/-!
Suppose that for a near-litter, its associated litter is already defined in `σ`, along with all of
the atoms in the symmetric difference with that litter. Then, the place the litter is supposed to
map to is already defined, and we simply add that to `σ`.
-/

variables (σ : allowable_partial_perm B) (N : near_litter) (A : extended_index B)

lemma _root_.cardinal.mk_sdiff_le {α : Type u} (S T : set α) : #(S \ T : set α) ≤ #S :=
⟨⟨λ s, ⟨s, s.property.left⟩, λ s t hst, by simpa only [subtype.mk_eq_mk, subtype.coe_inj] using hst⟩⟩

private noncomputable def near_litter_image (hN : litter_set N.fst ≠ N.snd)
  (hNL : (sum.inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain) :
    near_litter :=
  ⟨(near_litter_value B σ A N.fst.to_near_litter hNL).fst,
    (near_litter_value B σ A N.fst.to_near_litter hNL).snd.val ∆
      set.range (λ (a : {a // a ∈ litter_set N.fst ∆ ↑(N.snd)}),
        atom_value B σ A a (ha a a.property)),
    begin
      rw [is_near_litter, is_near, small, ← symm_diff_assoc],
      exact lt_of_le_of_lt (mk_union_le _ _)
        (add_lt_of_lt κ_regular.aleph_0_le
          (lt_of_le_of_lt (cardinal.mk_sdiff_le _ _)
            (near_litter_value B σ A N.fst.to_near_litter hNL).snd.property)
          (lt_of_le_of_lt (cardinal.mk_sdiff_le _ _)
            (lt_of_le_of_lt mk_range_le N.snd.property))),
    end⟩

lemma near_litter_image_spec (hNin : (sum.inr N, A) ∈ σ.val.domain)
  (hN : litter_set N.fst ≠ N.snd)
  (hNL : (sum.inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain) :
  (sum.inr (N, near_litter_image B σ N A hN hNL ha), A) ∈ σ.val :=
begin
  unfold near_litter_image,
  obtain ⟨⟨_ | ⟨N, N'⟩, C⟩, hNN', heq⟩ := hNin, { cases heq },
  simp only [binary_condition.domain, sum.elim_inr, prod.mk.inj_iff] at heq,
  obtain ⟨h1, h2⟩ := heq, subst h1, subst h2,
  obtain ⟨⟨_ | ⟨L, M⟩, A⟩, hL, heq⟩ := hNL, { cases heq },
  simp only [binary_condition.domain, sum.elim_inr, prod.mk.inj_iff] at heq,
  obtain ⟨h1, h2⟩ := heq, subst h1, subst h2,
  obtain ⟨M', hM, symm, hsy, hsd⟩ := σ.prop.forward.near_litter_cond N N' A hNN',
  have := (σ.prop.backward.one_to_one A).near_litter _ hL hM,
  subst this,
  have : ∀ a, symm a = atom_value B σ A a ⟨_, hsy a, rfl⟩
    := λ b, (σ.prop.backward.one_to_one A).atom _ (hsy b) (atom_value_spec B σ A b ⟨_, hsy b, rfl⟩),
  have that := congr_arg set.range (funext this).symm,
  convert hNN',
  obtain ⟨N', atoms, hN'⟩ := N',
  dsimp only at hsd, subst hsd,
  have key : near_litter_value B σ A N.fst.to_near_litter ⟨_, hL, rfl⟩ = M :=
    (σ.prop.backward.one_to_one A).near_litter _
      (near_litter_value_spec B σ A N.fst.to_near_litter ⟨_, hL, rfl⟩) hL,
  have : (near_litter_value B σ A N.fst.to_near_litter ⟨_, hL, heq⟩).fst = N',
  { rw key,
    refine is_near_litter.unique M.2.2 _,
    unfold is_near_litter is_near small at hN' ⊢,
    rw ← symm_diff_assoc at hN',
    have : ∀ (S T : set atom), # (S ∆ T : set atom) ≤ # (S ∪ T : set atom),
    { unfold symm_diff,
      intros S T,
      refine cardinal.mk_le_mk_of_subset _,
      simp only [set.sup_eq_union, set.union_subset_iff],
      exact ⟨λ x hx, or.inl hx.1, λ x hx, or.inr hx.1⟩, },
    specialize this (litter_set N' ∆ M.snd.val ∆ set.range symm) (set.range symm),
    rw [symm_diff_assoc, symm_diff_self, symm_diff_bot] at this,
    exact lt_of_le_of_lt
      (this.trans (cardinal.mk_union_le _ _))
      (cardinal.add_lt_of_lt κ_regular.aleph_0_le hN' $ lt_of_le_of_lt cardinal.mk_range_le N.2.2) },
  subst this,
  exact sigma.mk.inj_iff.2 ⟨rfl, heq_of_eq $ subtype.mk_eq_mk.2 $ congr_arg2 _ (by rw key) that⟩
end

lemma near_litter_image_spec_reverse (hN : litter_set N.fst ≠ N.snd)
  (hNL : (sum.inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain)
  (hNin : (sum.inr (near_litter_image B σ N A hN hNL ha), A) ∈ σ.val.range) : (sum.inr (N, near_litter_image B σ N A hN hNL ha), A) ∈ σ.val :=
begin
  refine near_litter_image_spec B σ N A _ hN hNL ha,
  obtain ⟨⟨_ | ⟨M, M'⟩, A⟩, hM, hMr⟩ := hNin, { cases hMr },
  simp only [binary_condition.range, sum.elim_inr, prod.mk.inj_iff] at hMr, obtain ⟨h1, h2⟩ := hMr, subst h1, subst h2,
  refine ⟨_, hM, _⟩,
  simp only [binary_condition.domain, sum.elim_inr, prod.mk.inj_iff, eq_self_iff_true, and_true],
  obtain ⟨P, hP, symm, hsy, hsd⟩ := σ.prop.forward.near_litter_cond M _ A hM,
  have := (σ.prop.backward.one_to_one A).near_litter M hM (near_litter_image_spec B σ M A ⟨_, hM, rfl⟩ _ ⟨_, hP, rfl⟩ (λ a ha, ⟨_, hsy ⟨a, ha⟩, rfl⟩)),
  { sorry },
  { intro H,
    have : near_litter_image B σ N A hN hNL ha = near_litter_value B σ A M ⟨_, hM, rfl⟩ := (σ.prop.backward.one_to_one A).near_litter M hM (near_litter_value_spec B σ A M ⟨_, hM, rfl⟩),
    unfold near_litter_image at this,
    rw [← sigma.eta (near_litter_value B σ A M ⟨_, hM, rfl⟩), sigma.mk.inj_iff] at this,
    obtain ⟨h1, h2⟩ := this,
    sorry }
end

lemma near_litter_union_one_to_one_forward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (sum.inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain) :
  spec.one_to_one_forward B (σ.val ∪ {(sum.inr (N, near_litter_image B σ N A hN hNL ha), A)}) :=
begin
  refine λ C, ⟨λ a b hb c hc, _, λ M P hP Q hQ, _⟩,
  { simp only [set.mem_set_of_eq, subtype.val_eq_coe, set.union_singleton, set.mem_insert_iff,
               prod.mk.inj_iff, false_and, false_or] at hb hc,
    exact (σ.prop.forward.one_to_one C).atom a hb hc },
  { simp only [set.mem_set_of_eq, subtype.val_eq_coe, set.union_singleton,
               set.mem_insert_iff, prod.mk.inj_iff] at hP hQ,
    obtain ⟨⟨h1, h2⟩, h3⟩ | hP := hP; obtain ⟨⟨h1', h2'⟩, h3'⟩ | hQ := hQ,
    { exact h1.trans h1'.symm },
    { subst h1, subst h2, subst h3,
      exact (σ.prop.forward.one_to_one C).near_litter _ (near_litter_image_spec_reverse B σ P C hN hNL ha ⟨_, hQ, rfl⟩) hQ },
    { subst h1', subst h2', subst h3',
      exact (σ.prop.forward.one_to_one C).near_litter _ hP (near_litter_image_spec_reverse B σ Q C hN hNL ha ⟨_, hP, rfl⟩) },
    { exact (σ.prop.forward.one_to_one C).near_litter M hP hQ } }
end

lemma near_litter_union_one_to_one_backward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (sum.inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain) :
  spec.one_to_one_forward B (σ.val ∪ {(sum.inr (N, near_litter_image B σ N A hN hNL ha), A)})⁻¹ :=
begin
  refine λ C, ⟨λ a b hb c hc, _, λ M P hP Q hQ, _⟩,
  { simp only [set.mem_set_of_eq, subtype.val_eq_coe, set.union_singleton, set.mem_insert_iff,
               prod.mk.inj_iff, false_and, false_or, set.mem_inv] at hb hc,
    cases hb, cases hb,
    cases hc, cases hc,
    exact (σ.prop.backward.one_to_one C).atom a hb hc },
  { simp only [set.mem_set_of_eq, subtype.val_eq_coe, set.union_singleton,
               set.mem_insert_iff, prod.mk.inj_iff] at hP hQ,
    obtain ⟨⟨h1, h2⟩, h3⟩ | hP := hP; obtain ⟨⟨h1', h2'⟩, h3'⟩ | hQ := hQ,
    { simp at hP },
    { exact (σ.prop.backward.one_to_one A).near_litter N
        (near_litter_image_spec B σ N A ⟨_, hQ, rfl⟩ hN hNL ha) hQ },
    { exact (σ.prop.backward.one_to_one A).near_litter N hP
        (near_litter_image_spec B σ N A ⟨_, hP, rfl⟩ hN hNL ha) },
    { exact (σ.prop.backward.one_to_one C).near_litter M hP hQ } }
end

lemma near_litter_union_atom_cond_forward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (sum.inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain) :
  ∀ L C, spec.atom_cond B (σ.val ∪ {(sum.inr (N, near_litter_image B σ N A hN hNL ha), A)}) L C :=
begin
  intros L C,
  obtain ⟨L', hL, atom_map, hin, himg⟩ | ⟨hL, hLsmall⟩ | ⟨L', hL, hLsmall, hmaps⟩ := σ.prop.forward.atom_cond L C,
  { exact spec.atom_cond.all L' (or.inl hL) atom_map (λ a H, or.inl $ hin a H) himg },
  refine spec.atom_cond.small_out _ _,
  { rintro ⟨⟨_ | ⟨N, M⟩, _⟩, hb, hdom⟩; cases hdom,
    refine or.rec (λ h, hL ⟨_, h, rfl⟩) (λ h, _) hb,
    cases set.mem_singleton_iff.1 h,
    simpa only using hN },
  swap,
  refine spec.atom_cond.small_in L' (or.inl hL) _
      (λ a b hab, or.rec (λ h, hmaps h) (λ h, by cases h) hab),
  all_goals { convert hLsmall using 1,
    refine set.ext (λ x, ⟨λ hx, ⟨hx.1, _⟩, λ hx, ⟨hx.1, _⟩⟩),
    { obtain ⟨b, hb, hdom⟩ := hx.2,
      refine ⟨b, or.rec id (λ h, _) hb, hdom⟩,
      cases set.mem_singleton_iff.1 h,
      cases hdom },
    { obtain ⟨-, b, hb, hdom⟩ := hx,
      refine ⟨b, or.inl hb, hdom⟩ } }
end

lemma near_litter_union_atom_cond_backward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (sum.inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain) :
  ∀ L C, spec.atom_cond B (σ.val ∪ {(sum.inr (N, near_litter_image B σ N A hN hNL ha), A)})⁻¹ L C :=
begin
  intros L C,
  obtain ⟨L', hL, atom_map, hin, himg⟩ | ⟨hL, hLsmall⟩ | ⟨L', hL, hLsmall, hmaps⟩ := σ⁻¹.prop.forward.atom_cond L C,
  { exact spec.atom_cond.all L' (or.inl hL) atom_map (λ a H, or.inl $ hin a H) himg },
  sorry {
    refine spec.atom_cond.small_out _ _,
    { rintro ⟨⟨_ | ⟨N, M⟩, _⟩, hb, hdom⟩; cases hdom,
      refine or.rec (λ h, hL ⟨_, h, rfl⟩) (λ h, _) hb,
      simp only [has_inv.inv, set.mem_singleton_iff, sum.elim_inr, prod.mk.inj_iff] at h,
      obtain ⟨⟨rfl, hLM : L.to_near_litter = near_litter_image B σ M A hN hNL ha⟩, rfl⟩ := h,
      rw hLM at hL,
      sorry },
    convert hLsmall using 1,
    refine set.ext (λ x, ⟨λ hx, ⟨hx.1, _⟩, λ hx, ⟨hx.1, _⟩⟩),
    { obtain ⟨b, hb, hdom⟩ := hx.2,
      refine ⟨b, or.rec id (λ h, _) hb, hdom⟩,
      obtain ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ := b;
      simp only [set.mem_singleton_iff, has_inv.inv, sum.elim_inl, sum.elim_inr] at h; cases h,
      cases hdom },
    { obtain ⟨-, b, hb, hdom⟩ := hx,
      refine ⟨b, or.inl hb, hdom⟩ } },
  { refine spec.atom_cond.small_in L' (or.inl hL) _
      (λ a b hab, or.rec (λ h, hmaps h) (λ h, by cases h) hab),
    convert hLsmall using 1,
    refine set.ext (λ x, ⟨λ hx, ⟨hx.1, _⟩, λ hx, ⟨hx.1, _⟩⟩),
    { obtain ⟨b, hb, hdom⟩ := hx.2,
      refine ⟨b, or.rec id (λ h, _) hb, hdom⟩,
      obtain ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ := b;
      simp only [set.mem_singleton_iff, has_inv.inv, sum.elim_inl, sum.elim_inr] at h; cases h,
      cases hdom },
    { obtain ⟨-, b, hb, hdom⟩ := hx,
      refine ⟨b, or.inl hb, hdom⟩ } }
end

lemma near_litter_union_near_litter_cond_forward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (sum.inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain) :
  ∀ N₁ N₂ C, spec.near_litter_cond B
    (σ.val ∪ {(sum.inr (N, near_litter_image B σ N A hN hNL ha), A)}) N₁ N₂ C :=
begin
  rintros N₁ N₂ C (h | h),
  { obtain ⟨M, hM₁, sd, hsd₁, hsd₂⟩ := σ.property.forward.near_litter_cond N₁ N₂ C h,
    exact ⟨M, or.inl hM₁, sd, λ a, or.inl (hsd₁ a), hsd₂⟩, },
  cases h,
  obtain ⟨⟨atoms | ⟨N₃, N₄⟩, C⟩, hc₁, hc₂⟩ := hNL; cases hc₂,
  refine ⟨N₄, or.inl hc₁, λ a, atom_value B σ A a (ha a a.property), _, _⟩,
  { exact λ a, or.inl (atom_value_spec B σ A a (ha a a.property)), },
  { suffices : near_litter_value B σ A N.fst.to_near_litter ⟨_, hc₁, rfl⟩ = N₄,
    { convert rfl; rw this, },
    have := near_litter_value_spec B σ A N.fst.to_near_litter ⟨_, hc₁, rfl⟩,
    exact (σ.property.backward.one_to_one A).near_litter N.fst.to_near_litter this hc₁, }
end

lemma near_litter_union_near_litter_cond_backward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (sum.inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain) :
  ∀ N₁ N₂ C, spec.near_litter_cond B
    (σ.val ∪ {(sum.inr (N, near_litter_image B σ N A hN hNL ha), A)})⁻¹ N₁ N₂ C :=
begin
  rintros N₁ N₂ C (h | h),
  { obtain ⟨M, hM₁, sd, hsd₁, hsd₂⟩ := σ.property.backward.near_litter_cond N₁ N₂ C h,
    exact ⟨M, or.inl hM₁, sd, λ a, or.inl (hsd₁ a), hsd₂⟩, },
  dsimp only [set.mem_singleton_iff] at h,
  unfold has_inv.inv at h,
  simp only [sum.elim_inr, prod.mk.inj_iff] at h,
  cases h.left.left, have := h.left.right, subst this, cases h.right,
  refine ⟨N, or.inl sorry, sorry⟩,
end

lemma near_litter_union_non_flexible_cond_forward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (sum.inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain) :
  spec.non_flexible_cond B (σ.val ∪ {(sum.inr (N, near_litter_image B σ N A hN hNL ha), A)}) :=
begin
  rintros β δ γ hγ hδ hγδ N₁ C t (ht | ht) ρ hρ,
  { exact σ.property.forward.non_flexible_cond hγ hδ hγδ N₁ C t ht ρ
      (struct_perm.satisfies_union_left _ _ _ hρ), },
  dsimp only [set.mem_singleton_iff] at ht,
  cases ht, exfalso, exact hN rfl,
end

lemma near_litter_union_non_flexible_cond_backward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (sum.inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain) :
  spec.non_flexible_cond B (σ.val ∪ {(sum.inr (N, near_litter_image B σ N A hN hNL ha), A)})⁻¹ :=
begin
  rintros β δ γ hγ hδ hγδ N₁ C t (ht | ht) ρ hρ,
  { exact σ.property.backward.non_flexible_cond hγ hδ hγδ N₁ C t ht ρ
      (struct_perm.satisfies_union_left _ _ _ hρ), },
  unfold has_inv.inv at ht,
  simp only [sum.elim_inr, set.mem_singleton_iff, prod.mk.inj_iff] at ht,
  exfalso, -- This isn't true because N is never a litter.
  sorry
end

lemma near_litter_union_support_closed_forward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (sum.inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain) :
  (σ.val ∪ {(sum.inr (N, near_litter_image B σ N A hN hNL ha), A)}).domain.support_closed B :=
begin
  intros β δ γ hγ hδ hγδ C t ht,
  rw spec.domain_union at ht ⊢,
  rw unary_spec.lower_union,
  cases ht,
  { exact supports_union_left (σ.property.forward.support_closed hγ hδ hγδ C t ht), },
  simp only [spec.domain, binary_condition.domain, set.image_singleton,
    set.mem_singleton_iff, sum.elim_inr, prod.mk.inj_iff] at ht,
  exfalso, cases ht.left, exact hN rfl,
end

lemma near_litter_union_support_closed_backward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (sum.inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain) :
  (σ.val ∪ {(sum.inr (N, near_litter_image B σ N A hN hNL ha), A)}).range.support_closed B :=
sorry

lemma near_litter_union_flexible_cond (hN : litter_set N.fst ≠ N.snd)
  (hNL : (sum.inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain)
  (image_not_flexible :
    ∀ L, litter_set L = (near_litter_image B σ N A hN hNL ha).snd.val → ¬ flexible L A) :
  ∀ C, spec.flexible_cond B (σ.val ∪ {(sum.inr (N, near_litter_image B σ N A hN hNL ha), A)}) C :=
begin
  intro C,
  obtain (⟨hdom, hrge⟩ | ⟨hdom, hrge⟩) := σ.property.flexible_cond C,
  { refine spec.flexible_cond.co_large _ _,
    { convert hdom, ext L, split; rintro ⟨hC₁, hC₂⟩; refine ⟨hC₁, λ h, _⟩,
      { rw spec.domain_union at hC₂, exact hC₂ (or.inl h), },
      { rw spec.domain_union at h,
        cases h,
        { exact hC₂ h, },
        { simp only [spec.domain, set.image_singleton, set.mem_singleton_iff,
            binary_condition.domain, sum.elim_inr] at h,
          cases h, exact hN rfl, } } },
    { convert hrge, ext L, split; rintro ⟨hC₁, hC₂⟩; refine ⟨hC₁, λ h, _⟩,
      { rw spec.range_union at hC₂, exact hC₂ (or.inl h), },
      { rw spec.range_union at h,
        cases h,
        { exact hC₂ h, },
        { simp only [spec.range, set.image_singleton, set.mem_singleton_iff,
            binary_condition.range, sum.elim_inr, prod.mk.inj_iff] at h,
          obtain ⟨h₁, h₂⟩ := h, cases h₂,
          refine image_not_flexible L _ hC₁, rw ← h₁, refl, } } } },
  { refine spec.flexible_cond.all _ _,
    { intros L hL, rw spec.domain_union, exact or.inl (hdom L hL), },
    { intros L hL, rw spec.range_union, exact or.inl (hrge L hL), }, }
end

lemma near_litter_union_allowable (hN : litter_set N.fst ≠ N.snd)
  (hNL : (sum.inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain)
  (image_not_flexible :
    ∀ L, litter_set L = (near_litter_image B σ N A hN hNL ha).snd.val → ¬ flexible L A) :
  spec.allowable_spec B (σ.val ∪ {(sum.inr (N, near_litter_image B σ N A hN hNL ha), A)}) := {
  forward := {
    one_to_one := near_litter_union_one_to_one_forward B σ N A hN hNL ha,
    atom_cond := near_litter_union_atom_cond_forward B σ N A hN hNL ha,
    near_litter_cond := near_litter_union_near_litter_cond_forward B σ N A hN hNL ha,
    non_flexible_cond := near_litter_union_non_flexible_cond_forward B σ N A hN hNL ha,
    support_closed := near_litter_union_support_closed_forward B σ N A hN hNL ha,
  },
  backward := {
    one_to_one := near_litter_union_one_to_one_backward B σ N A hN hNL ha,
    atom_cond := near_litter_union_atom_cond_backward B σ N A hN hNL ha,
    near_litter_cond := near_litter_union_near_litter_cond_backward B σ N A hN hNL ha,
    non_flexible_cond := near_litter_union_non_flexible_cond_backward B σ N A hN hNL ha,
    support_closed := by { rw spec.inv_domain,
      exact near_litter_union_support_closed_backward B σ N A hN hNL ha },
  },
  flexible_cond := near_litter_union_flexible_cond B σ N A hN hNL ha image_not_flexible,
}

/-- We take the additional hypothesis that the near-litter that we're mapping do does not happen
to be a flexible litter. This will always be true, but it is convenient to assume at this point. -/
lemma le_near_litter_union (hN : litter_set N.fst ≠ N.snd)
  (hNL : (sum.inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain)
  (image_not_flexible :
    ∀ L, litter_set L = (near_litter_image B σ N A hN hNL ha).snd.val → ¬ flexible L A) :
  σ ≤ ⟨σ.val ∪ {(sum.inr (N, near_litter_image B σ N A hN hNL ha), A)},
    near_litter_union_allowable B σ N A hN hNL ha image_not_flexible⟩ := {
  subset := set.subset_union_left _ _,
  all_flex_domain := begin
    intros L N' C hN' hσ₁ hσ₂,
    cases set.mem_or_mem_of_mem_union hσ₂,
    { exfalso, exact hσ₁ h, },
    { exfalso, cases h, exact hN rfl, },
  end,
  all_flex_range := begin
    intros L N' C hN' hσ₁ hσ₂,
    cases set.mem_or_mem_of_mem_union hσ₂,
    { exfalso, exact hσ₁ h, },
    { exfalso,
      rw set.mem_singleton_iff at h,
      have : C = A,
      { cases congr_arg prod.snd h, refl },
      subst this,
      have the_congr := congr_arg prod.fst h,
      have := congr_arg prod.snd (sum.inr.inj the_congr),
      refine image_not_flexible L _ hN',
      dsimp only at this, rw ← this,
      refl, },
  end,
  all_atoms_domain := begin
    intros b₁ b₂ L hb₁ C hC₁ hC₂ c hc',
    cases hC₂,
    { exfalso, exact hC₁ hC₂, },
    { exfalso, simpa only [set.mem_singleton_iff, prod.mk.inj_iff, false_and] using hC₂, },
  end,
  all_atoms_range := begin
    intros b₁ b₂ L hb₁ C hC₁ hC₂ c hc',
    cases hC₂,
    { exfalso, exact hC₁ hC₂, },
    { exfalso, simpa only [set.mem_singleton_iff, prod.mk.inj_iff, false_and] using hC₂, },
  end,
}

/-- If everything that constrains a near litter lies in `σ`, we can add the near litter to `σ`,
giving a new allowable partial permutation `ρ ≥ σ`. -/
lemma exists_ge_near_litter (hN : litter_set N.fst ≠ N.snd)
  (hσ : ∀ c, c ≺ (⟨sum.inr N, A⟩ : support_condition B) → c ∈ σ.val.domain) :
  ∃ ρ ≥ σ, (⟨sum.inr N, A⟩ : support_condition B) ∈ ρ.val.domain :=
begin
  have hNL := hσ (sum.inr N.fst.to_near_litter, A) (constrains.near_litter N hN A),
  have ha := λ a ha, hσ (sum.inl a, A) (constrains.symm_diff N a ha A),
  by_cases image_not_flexible :
    ∀ L, litter_set L = (near_litter_image B σ N A hN hNL ha).snd.val → ¬ flexible L A,
  { exact ⟨_, le_near_litter_union B σ N A hN hNL ha image_not_flexible,
    ⟨_, set.mem_union_right _ rfl, rfl⟩⟩, },
  { -- Seek a contradiction (discuss this with Peter).
    push_neg at image_not_flexible,
    obtain ⟨L, hL₁, hL₂⟩ := image_not_flexible,
    sorry }
end

end exists_ge_near_litter

section exists_ge_flexible

/-!
When we want to add an `A`-flexible litter to `σ`, we will just add all of them in an arbitrary
bijection. This will always exist because the sets are both of size `μ`. This will create a
*rough bijection*. This is not necessarily compatible with `σ`, because we may already have
specified where certain atoms in these litters are mapped to or from.

To remedy this, for each `A`-flexible litter we create a *precise atom bijection* mapping all of the
unassigned atoms in the domain of `σ` to all of the unassigned atoms in the range of `σ` in the
litter obtained under the rough bijection.

We extend `σ` by saying that each `A`-flexible litter is mapped to the image of the precise atom
bijection map, together with the image of all of the atoms that were already specified. This is a
near-litter, which is near to the litter obtained using the rough bijection. The same procedure is
done in the reverse direction with the same bijections, so that all of the `A`-flexible litters are
now defined in this new allowable partial permutation.
-/

variables {B} {A : extended_index B}

section rough_bijection

variable (A)

/-- A bijection of the remaining `A`-flexible litters in an allowable partial permutation `σ`.
This is a bijection of *rough images*; we have to then take into account all of the exceptions that
have already been established in `σ`. -/
def rough_bijection (dom rge : unary_spec B) :=
  {L : litter // flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ dom} ≃
  {L : litter // flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ rge}

variables {dom rge : unary_spec B} {A}

@[simp] lemma equiv.symm_trans {α β γ : Type*} (f : α ≃ β) (g : β ≃ γ) :
  (f.trans g).symm = (g.symm).trans f.symm := rfl

/-- The inverse of a rough bijection is a rough bijection for the inverse permutation. -/
def rough_bijection.inv (bij : rough_bijection A dom rge) :
  rough_bijection A rge dom :=
bij.symm

@[simp] lemma rough_bijection.inv_to_fun
  (bij : rough_bijection A dom rge)
  (L : {L : litter | flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ dom}) :
  (bij.inv.to_fun (bij.to_fun L) : litter) = L :=
begin
  unfold rough_bijection.inv equiv.symm, dsimp only,
  rw bij.left_inv L,
end

@[simp] lemma rough_bijection.to_fun_inv
  (bij : rough_bijection A dom rge)
  (L : {L : litter | flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ rge}) :
  (bij.to_fun (bij.inv.to_fun L) : litter) = L :=
begin
  unfold rough_bijection.inv equiv.symm, dsimp only,
  rw bij.right_inv L,
end

@[simp] lemma rough_bijection.inv_inv (bij : rough_bijection A dom rge) :
  bij.inv.inv = bij :=
begin
  ext, refl,
end

def rough_bijection.inv' {σ : allowable_partial_perm B}
  (bij : rough_bijection A σ.val.domain σ.val.range) :
  rough_bijection A σ⁻¹.val.domain σ⁻¹.val.range := {
  to_fun := λ L, ⟨bij.inv_fun ⟨L, L.2.1, by simpa only [inv_def, spec.inv_domain] using L.2.2⟩,
    (bij.inv_fun _).2.1,
    (by simpa only [inv_def, spec.inv_range] using (bij.inv_fun _).2.2)⟩,
  inv_fun := λ L, ⟨bij.to_fun ⟨L, L.2.1, by simpa only [inv_def, spec.inv_range] using L.2.2⟩,
    (bij.to_fun _).2.1,
    (by simpa only [inv_def, spec.inv_domain] using (bij.to_fun _).2.2)⟩,
  left_inv := begin
    rintro ⟨L, hL₁, hL₂⟩,
    simp only [subtype.coe_mk, equiv.inv_fun_as_coe, subtype.coe_eta, equiv.to_fun_as_coe,
      equiv.apply_symm_apply],
  end,
  right_inv := begin
    rintro ⟨L, hL₁, hL₂⟩,
    simp only [subtype.coe_mk, equiv.to_fun_as_coe, subtype.coe_eta, equiv.inv_fun_as_coe,
      equiv.symm_apply_apply],
  end
}

@[simp] lemma rough_bijection.inv'_to_fun {σ : allowable_partial_perm B}
  {bij : rough_bijection A σ.val.domain σ.val.range} {L} :
  (bij.inv'.to_fun L : litter) =
    bij.inv_fun ⟨L, L.2.1, by simpa only [inv_def, spec.inv_domain] using L.2.2⟩ :=
by simp only [rough_bijection.inv', subtype.coe_mk]

@[simp] lemma rough_bijection.inv'_to_fun_mk {σ : allowable_partial_perm B}
  {bij : rough_bijection A σ.val.domain σ.val.range} {L hL} :
  (bij.inv'.to_fun ⟨L, hL⟩ : litter) =
    bij.inv_fun ⟨L, hL.1, by simpa only [inv_def, spec.inv_domain] using hL.2⟩ :=
by simp only [rough_bijection.inv', subtype.coe_mk]

end rough_bijection

variable {σ : allowable_partial_perm B}

lemma small_of_not_mem_spec
  (L : {L : litter | flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ σ.val.domain}) :
  small {a ∈ litter_set L | (sum.inl a, A) ∈ σ.val.domain} :=
begin
  obtain ⟨N, h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N, hN, h₁, h₂⟩ := σ.property.forward.atom_cond L A,
  { cases L.property.2 ⟨_, h₁, rfl⟩, },
  { exact h₂ },
  { exact h₁ },
end

lemma small_of_rough_bijection
  (bij : rough_bijection A σ.val.domain σ.val.range)
  (L : {L : litter // flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ σ.val.domain}) :
  small {a ∈ litter_set (bij.to_fun L) | (sum.inl a, A) ∈ σ.val.range} :=
begin
  obtain ⟨N, h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N, hN, h₁, h₂⟩ := σ.property.backward.atom_cond
    (bij.to_fun L) A,
  { exfalso, rw spec.inr_mem_inv at h₁,
    obtain ⟨hC, hn⟩ := (bij.to_fun L).property, exact hn ⟨_, h₁, rfl⟩ },
  { rw spec.inv_domain at h₂, exact h₂, },
  { rw spec.inv_domain at h₁, exact h₁, }
end

section precise_atom_bijection

variables {dom rge : unary_spec B}

/-- Suppose a flexible litter `L` is mapped to another flexible litter `L₁` under the rough
bijection defined above. We construct a bijection between the atoms not yet specified in `L` and
`L₁`. This yields a precise near-litter image of each flexible litter `L`. -/
def rough_bijection.precise_atom_bijection
  (bij : rough_bijection A dom rge)
  (L : {L : litter | flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ dom}) :=
  ↥{a ∈ litter_set L | (sum.inl a, A) ∉ dom} ≃
  ↥{a ∈ litter_set (bij.to_fun L) | (sum.inl a, A) ∉ rge}

/-- The inverse of a rough bijection is a rough bijection for the inverse permutation. -/
def rough_bijection.precise_atom_bijection.inv
  {bij : rough_bijection A dom rge}
  {L : {L : litter | flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ dom}}
  (abij : bij.precise_atom_bijection L) :
    bij.inv.precise_atom_bijection (bij.to_fun L) := {
  to_fun := λ a, ⟨abij.inv_fun a,
    (by simpa only [rough_bijection.inv_to_fun] using (abij.inv_fun a).prop.left),
    (abij.inv_fun a).prop.right⟩,
  inv_fun := λ a, abij.to_fun ⟨a,
    (by simpa only [rough_bijection.inv_to_fun] using a.prop.left),
    a.prop.right⟩,
  left_inv := begin
    rintro ⟨a, ha₁, ha₂⟩,
    simp only [equiv.inv_fun_as_coe, subtype.coe_mk, subtype.coe_eta, equiv.to_fun_as_coe,
      equiv.apply_symm_apply],
  end,
  right_inv := begin
    rintro ⟨a, ha₁, ha₂⟩,
    simp only [subtype.coe_mk, equiv.to_fun_as_coe, equiv.inv_fun_as_coe, equiv.symm_apply_apply,
      subtype.mk_eq_mk],
  end,
}

def rough_bijection.precise_atom_bijection.inv' {σ : allowable_partial_perm B}
  {bij : rough_bijection A σ.val.domain σ.val.range}
  {L : {L : litter | flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ σ.val.range}}
  (abij : bij.precise_atom_bijection (bij.inv_fun L)) :
    bij.inv'.precise_atom_bijection
      ⟨L, L.2.1, by simpa only [inv_def, spec.inv_domain] using L.2.2⟩ := {
  to_fun := λ a, ⟨abij.inv_fun ⟨a,
    by simpa only [equiv.inv_fun_as_coe, equiv.to_fun_as_coe, equiv.apply_symm_apply] using a.2.1,
    by simpa only [inv_def, spec.inv_domain] using a.2.2⟩,
    begin
      convert (abij.inv_fun ⟨a, _, _⟩).2.1 using 2,
      simp_rw [rough_bijection.inv'_to_fun_mk, subtype.coe_eta],
    end,
    begin
      convert (abij.inv_fun ⟨a, _, _⟩).2.2 using 2,
      rw [inv_def, spec.inv_range],
    end⟩,
  inv_fun := λ a, ⟨abij.to_fun ⟨a,
    by simpa only [rough_bijection.inv'_to_fun_mk, subtype.coe_eta] using a.2.1,
    by simpa only [inv_def, spec.inv_range] using a.2.2⟩,
    begin
      convert (abij.to_fun ⟨a, _, _⟩).2.1 using 2,
      rw [bij.right_inv, subtype.coe_mk],
    end,
    begin
      convert (abij.to_fun ⟨a, _, _⟩).2.2 using 2,
      rw [inv_def, spec.inv_domain],
    end⟩,
  left_inv := begin
    rintro ⟨a, ha₁, ha₂⟩,
    simp only [subtype.coe_eta, subtype.coe_mk, equiv.inv_fun_as_coe, equiv.to_fun_as_coe,
      equiv.apply_symm_apply, subtype.mk_eq_mk],
  end,
  right_inv := begin
    rintro ⟨a, ha₁, ha₂⟩,
    simp only [equiv.inv_fun_as_coe, equiv.to_fun_as_coe, subtype.coe_eta, subtype.coe_mk,
      equiv.symm_apply_apply, subtype.mk_eq_mk],
  end,
}

end precise_atom_bijection

/-- If the image of this atom has already been specified by `σ`, return the value that was already
given. Otherwise, return the image generated by `precise_image_bijection`. -/
private noncomputable def precise_atom_image {dom rge}
  (bij : rough_bijection A dom rge)
  (L : {L : litter | flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ dom})
  (abij : bij.precise_atom_bijection L)
  (atom_value : {a : litter_set L // (sum.inl a.val, A) ∈ dom} → atom)
  (a : atom) (ha : a ∈ litter_set L) : atom :=
@dite _ ((sum.inl a, A) ∈ dom) (classical.dec _)
  (λ h, atom_value ⟨⟨a, ha⟩, h⟩)
  (λ h, abij.to_fun ⟨a, ha, h⟩)

lemma precise_atom_image_range {dom rge}
  (bij : rough_bijection A dom rge)
  (L : {L : litter | flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ dom})
  (abij : bij.precise_atom_bijection L)
  (atom_value : {a : litter_set L // (sum.inl a.val, A) ∈ dom} → atom) :
  set.range (λ (a : litter_set L), precise_atom_image bij L abij atom_value a a.property) =
    (litter_set (bij.to_fun L) ∩ {a | (sum.inl a, A) ∉ rge}) ∪
    set.range atom_value :=
begin
  unfold precise_atom_image,
  ext a,
  split,
  { rintro ⟨b, hb⟩, dsimp only at hb,
    split_ifs at hb,
    { simp_rw subtype.coe_eta at hb, exact or.inr ⟨⟨b, h⟩, hb⟩, },
    { rw ← hb,
      exact or.inl (abij.to_fun ⟨b, _⟩).property, } },
  { rintro (⟨ha₁, ha₂⟩ | ⟨b, hb⟩),
    { rw set.mem_set_of at ha₂,
      set b := abij.inv_fun ⟨a, ha₁, ha₂⟩ with hb,
      refine ⟨⟨b, b.property.left⟩, _⟩,
      dsimp only,
      split_ifs,
      { exfalso, exact b.property.right h, },
      { simp only [hb, equiv.inv_fun_as_coe, subtype.coe_mk,
          subtype.coe_eta, equiv.to_fun_as_coe, equiv.apply_symm_apply], } },
    { refine ⟨b, _⟩,
      dsimp only,
      split_ifs,
      { simp_rw subtype.coe_eta, exact hb, },
      { exfalso, exact h b.property, } } }
end

/-- The precise image of a flexible litter under the new allowable permutation. -/
private def precise_litter_image_aux {dom rge}
  (bij : rough_bijection A dom rge)
  (L : {L : litter | flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ dom})
  (abij : bij.precise_atom_bijection L)
  (atom_value : {a : litter_set L // (sum.inl a.val, A) ∈ dom} → atom)
  (h₁ : # ↥(litter_set ↑(bij.to_fun L) \ {a : atom | (sum.inl a, A) ∉ rge}) < # κ)
  (h₂ : # {a : litter_set L // (sum.inl a.val, A) ∈ dom} < # κ) : near_litter :=
⟨(bij.to_fun L),
  set.range (λ (a : litter_set L), precise_atom_image bij L abij atom_value a a.property),
  begin
    rw precise_atom_image_range,
    unfold is_near_litter is_near small symm_diff,
    refine lt_of_le_of_lt (cardinal.mk_union_le _ _) (cardinal.add_lt_of_lt κ_regular.aleph_0_le _ _),
    { rw [← set.sup_eq_union, sdiff_sup, ← set.inf_eq_inter, sdiff_inf_self_left],
      exact lt_of_le_of_lt (cardinal.mk_le_mk_of_subset $ set.inter_subset_left _ _) h₁, },
    { rw [← set.sup_eq_union, sup_sdiff, ← set.inf_eq_inter, inf_sdiff, sdiff_self, bot_inf_eq,
        bot_sup_eq],
      refine lt_of_le_of_lt (cardinal.mk_le_mk_of_subset $ @sdiff_le _ _ (litter_set _) _) _,
      exact lt_of_le_of_lt cardinal.mk_range_le h₂, },
end⟩

private lemma precise_litter_image_aux_inj
  {bij : rough_bijection A σ.val.domain σ.val.range}
  {L₁ L₂ : {L : litter | flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ σ.val.domain}}
  {abij₁ : bij.precise_atom_bijection L₁} {abij₂ : bij.precise_atom_bijection L₂}
  {atom_value₁ : {a : litter_set L₁ // (sum.inl a.val, A) ∈ σ.val.domain} → atom}
  {atom_value₂ : {a : litter_set L₂ // (sum.inl a.val, A) ∈ σ.val.domain} → atom}
  {h₁ h₂ h₃ h₄} :
  precise_litter_image_aux bij L₁ abij₁ atom_value₁ h₁ h₂ =
  precise_litter_image_aux bij L₂ abij₂ atom_value₂ h₃ h₄ →
    L₁ = L₂ :=
begin
  intro h,
  have := congr_arg sigma.fst h,
  simpa only [precise_litter_image_aux, subtype.coe_inj, equiv.to_fun_as_coe,
    embedding_like.apply_eq_iff_eq] using this,
end

private noncomputable def precise_litter_image
  (bij : rough_bijection A σ.val.domain σ.val.range)
  (L : {L : litter | flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ σ.val.domain})
  (abij : bij.precise_atom_bijection L) : near_litter :=
precise_litter_image_aux bij L abij (λ ⟨⟨a, ha⟩, ha'⟩, atom_value B σ A a ha')
  (begin
    convert small_of_rough_bijection bij L,
    ext a, split,
    { rintro ⟨ha₁, ha₂⟩, simp only [set.mem_set_of_eq, set.not_not_mem] at ha₂, exact ⟨ha₁, ha₂⟩, },
    { rintro ⟨ha₁, ha₂⟩, exact ⟨ha₁, function.eval ha₂⟩, }
  end)
  (begin
    convert small_of_not_mem_spec L using 1, rw cardinal.mk_sep, refl,
  end)

private noncomputable def precise_litter_inverse_image
  (bij : rough_bijection A σ.val.domain σ.val.range)
  (L : {L : litter | flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ σ.val.range})
  (abij : bij.inv.precise_atom_bijection L) :
  near_litter :=
precise_litter_image_aux bij.inv L abij
  (λ ⟨⟨a, ha⟩, ha'⟩, atom_value B σ⁻¹ A a (by simpa only [inv_def, spec.inv_domain] using ha'))
  (begin
    convert small_of_rough_bijection bij.inv'
      ⟨L.1, L.2.1, by simpa only [inv_def, spec.inv_domain] using L.2.2⟩,
    ext a, split,
    { rintro ⟨ha₁, ha₂⟩, simp only [set.mem_set_of_eq, set.not_not_mem] at ha₂,
      sorry /- exact ⟨ha₁, ha₂⟩, -/ },
    { rintro ⟨ha₁, ha₂⟩,
      sorry /- exact ⟨ha₁, function.eval ha₂⟩, -/ }
  end)
  (begin
    convert small_of_not_mem_spec ⟨L.1, L.2.1, _⟩ using 1,
    sorry, sorry, sorry
  end)

private lemma precise_litter_image_inj
  {bij : rough_bijection A σ.val.domain σ.val.range}
  {L₁ L₂ : {L : litter | flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ σ.val.domain}}
  (abij₁ : bij.precise_atom_bijection L₁) (abij₂ : bij.precise_atom_bijection L₂) :
  precise_litter_image bij L₁ abij₁ = precise_litter_image bij L₂ abij₂ → L₁ = L₂ :=
precise_litter_image_aux_inj

private lemma precise_litter_inverse_image_inj
  {bij : rough_bijection A σ.val.domain σ.val.range}
  {L₁ L₂ : {L : litter | flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ σ.val.range}}
  (abij₁ : bij.inv.precise_atom_bijection L₁) (abij₂ : bij.inv.precise_atom_bijection L₂) :
  precise_litter_inverse_image bij L₁ abij₁ = precise_litter_inverse_image bij L₂ abij₂ → L₁ = L₂ :=
sorry

private def new_flexible_litters
  (bij : rough_bijection A σ.val.domain σ.val.range)
  (abij : ∀ L, bij.precise_atom_bijection L) :
  spec B :=
{c | ∃ (L : {L : litter | flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ σ.val.domain}),
  c = (sum.inr (L.1.to_near_litter, precise_litter_image bij L (abij L)), A)}

private def new_inverse_flexible_litters
  (bij : rough_bijection A σ.val.domain σ.val.range)
  (abij : ∀ L, bij.precise_atom_bijection L) :
  spec B :=
{c | ∃ L, c = (sum.inr (precise_litter_inverse_image bij _ (abij L).inv,
  (bij.to_fun L).1.to_near_litter), A)}

variables (bij : rough_bijection A σ.val.domain σ.val.range)
  (abij : ∀ L, bij.precise_atom_bijection L)

lemma flexible_union_one_to_one :
  spec.one_to_one_forward B
    (σ.val ∪ new_flexible_litters bij abij ∪ new_inverse_flexible_litters bij abij) :=
begin
  intro C,
  split,
  { rintros b a₁ ((ha₁ | ha₁) | ha₁) a₂ ha₂,
    { obtain ((ha₂ | ha₂) | ha₂) := ha₂,
      { exact (σ.property.forward.one_to_one C).atom b ha₁ ha₂, },
      { simpa only [new_flexible_litters, set.mem_set_of_eq, prod.mk.inj_iff, false_and,
          exists_false] using ha₂, },
      { simpa only [new_inverse_flexible_litters, set.mem_set_of_eq, prod.mk.inj_iff, false_and,
          exists_false] using ha₂, }, },
    { simpa only [new_flexible_litters, set.mem_set_of_eq, prod.mk.inj_iff, false_and,
          exists_false] using ha₁, },
    { simpa only [new_inverse_flexible_litters, set.mem_set_of_eq, prod.mk.inj_iff, false_and,
        exists_false] using ha₁, }, },
  { rintros N M₁ ((hM₁ | hM₁) | hM₁) M₂ ((hM₂ | hM₂) | hM₂),
    { exact (σ.property.forward.one_to_one C).near_litter N hM₁ hM₂, },
    { exfalso,
      obtain ⟨N', hN'₁, hN'₂⟩ := σ.property.backward.near_litter_cond _ _ C hM₁,
      obtain ⟨L', hL'⟩ := hM₂, cases hL',
      refine (bij.to_fun L').property.right ⟨_, hN'₁, _⟩,
      congr', },
    { exfalso,
      obtain ⟨L', hL'⟩ := hM₂, cases hL',
      refine (bij.to_fun L').property.right ⟨_, hM₁, _⟩,
      congr', },
    { exfalso,
      sorry },
    { obtain ⟨L₁, hL₁⟩ := hM₁, obtain ⟨L₂, hL₂⟩ := hM₂,
      cases precise_litter_image_inj _ _
        ((prod.ext_iff.1 $ sum.inr_injective (prod.ext_iff.1 hL₁).1).2.symm.trans
          (prod.ext_iff.1 $ sum.inr_injective (prod.ext_iff.1 hL₂).1).2),
      cases hL₁, cases hL₂, refl, },
    { obtain ⟨L₁, hL₁⟩ := hM₁, obtain ⟨L₂, hL₂⟩ := hM₂,
      sorry },
    { obtain ⟨L₁, hL₁⟩ := hM₁,
      obtain ⟨N', hN'₁, hN'₂⟩ := σ.property.backward.near_litter_cond _ _ C hM₂,
      sorry },
    { sorry },
    { obtain ⟨L₁, hL₁⟩ := hM₁, obtain ⟨L₂, hL₂⟩ := hM₂,
      unfold precise_litter_inverse_image at hL₁ hL₂,
      have := precise_litter_inverse_image_inj (abij L₁).inv (abij L₂).inv _,
      rw [equiv.to_fun_as_coe, embedding_like.apply_eq_iff_eq] at this,
      cases this, cases hL₁, cases hL₂, refl,
      { have := litter.to_near_litter_injective
          ((prod.ext_iff.1 $ sum.inr_injective (prod.ext_iff.1 hL₁).1).2.symm.trans
            (prod.ext_iff.1 $ sum.inr_injective (prod.ext_iff.1 hL₂).1).2),
        rw [subtype.val_inj, equiv.to_fun_as_coe, embedding_like.apply_eq_iff_eq] at this,
        cases this, refl, }, }, }
end

lemma flexible_union_atoms_eq (L : litter) (C : extended_index B) :
  {a ∈ litter_set L | (sum.inl a, C) ∈
    (σ.val ∪ new_flexible_litters bij abij ∪ new_inverse_flexible_litters bij abij).domain} =
  {a ∈ litter_set L | (sum.inl a, C) ∈ σ.val.domain} :=
begin
  ext a,
  simp only [spec.domain_union, new_flexible_litters, new_inverse_flexible_litters,
    subtype.val_eq_coe, set.mem_set_of_eq, set_coe.exists, subtype.coe_mk, equiv.to_fun_as_coe,
    set.mem_union_eq, set.mem_sep_iff],
  refine and_congr_right (λ ha, _),
  split,
  { rintro ((h | ⟨⟨as | Ns, C⟩, ⟨L, hL, hc⟩, h⟩) | ⟨⟨as | Ns, C⟩, ⟨L, hL, hc⟩, h⟩),
    { exact h, },
    { cases hc, },
    { cases h, },
    { cases hc, },
    { cases h, } },
  { intro h, exact or.inl (or.inl h), },
end

lemma flexible_union_atom_cond :
  ∀ L C, spec.atom_cond B
    (σ.val ∪ new_flexible_litters bij abij ∪ new_inverse_flexible_litters bij abij) L C :=
begin
  intros L C,
  obtain ⟨N, h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N, hN, h₁, h₂⟩ := σ.prop.forward.atom_cond L C,
  { exact spec.atom_cond.all N
      (or.inl $ or.inl h₁) atom_map (λ a H, or.inl $ or.inl $ h₂ a H) h₃, },
  { by_cases A = C,
    { subst h,
      by_cases flexible L A,
      { refine spec.atom_cond.small_in _ (or.inl $ or.inr ⟨⟨L, h, h₁⟩, rfl⟩) _ _,
        { rw flexible_union_atoms_eq, exact h₂, },
        { rintros a ha b ((hab | ⟨L', hL'⟩) | ⟨L', hL'⟩),
          { refine ⟨⟨a, ha⟩, _⟩,
            unfold precise_atom_image,
            rw dif_pos _,
            exact atom_value_eq_of_mem _ _ _ _ _ hab, },
          { cases hL', },
          { cases hL', }, }, },
      { refine spec.atom_cond.small_out _ _,
        { contrapose! h₁, rw [spec.domain_union, spec.domain_union] at h₁,
          obtain ((_ | _) | _) := h₁,
          { exact h₁, },
          { obtain ⟨_, ⟨L', rfl⟩, h₁⟩ := h₁, cases h₁, cases h L'.2.1, },
          { obtain ⟨_, ⟨L', rfl⟩, h₁⟩ := h₁,
            suffices : L = L',
            { subst this, cases h L'.2.1, },
            have := congr_arg prod.fst h₁,
            simp only [binary_condition.domain, sum.elim_inr] at this,
            convert (congr_arg sigma.fst this).symm,
            { rw [inv_def, spec.inv_range], },
            { rw [inv_def, spec.inv_range], },
            { rw [inv_def, spec.inv_range], },
            { simp_rw [inv_def, spec.inv_range], refl, },
            { rw subtype.heq_iff_coe_eq _,
              rw rough_bijection.inv_to_fun,
              rw [inv_def, spec.inv_range], intro, refl, }, }, },
        { rw flexible_union_atoms_eq, exact h₂, }, }, },
    { refine spec.atom_cond.small_out _ _,
      { contrapose! h₁, rw [spec.domain_union, spec.domain_union] at h₁,
        obtain ((_ | _) | _) := h₁,
        { exact h₁, },
        { obtain ⟨_, ⟨L', rfl⟩, h₁⟩ := h₁, cases h₁, cases h rfl, },
        { obtain ⟨_, ⟨L', rfl⟩, h₁⟩ := h₁, cases congr_arg prod.snd h₁, cases h rfl, } },
      convert h₂ using 1,
      refine set.ext (λ a, ⟨_, λ ha, ⟨ha.1, _⟩⟩),
      { rintro ⟨hL, ⟨⟨x, y⟩ | _, b⟩, (hxy | hxy) | hxy, ha⟩; cases ha,
        { exact ⟨hL, _, hxy, rfl⟩ },
        all_goals { obtain ⟨_, _, _, _, h⟩ := hxy, } },
      { simp only [spec.domain_union, set.mem_union_eq],
        exact or.inl (or.inl ha.2), } } },
  { refine spec.atom_cond.small_in N (or.inl $ or.inl hN) _ _,
    { rw flexible_union_atoms_eq, exact h₁ },
    { rintros a ha b ((hab | ⟨L', hL'⟩) | ⟨L', hL'⟩),
      { exact h₂ a ha b hab, },
      { cases hL', },
      { cases hL', }, }, }
end

lemma flexible_union_near_litter_cond :
  ∀ N₁ N₂ C, spec.near_litter_cond B
    (σ.val ∪ new_flexible_litters bij abij ∪ new_inverse_flexible_litters bij abij) N₁ N₂ C :=
sorry

lemma unpack_coh_cond ⦃β : Λ⦄
  ⦃γ : type_index⦄
  ⦃δ : Λ⦄
  (hγβ : γ < ↑β)
  (hδβ : δ < β)
  (hδγ : γ ≠ ↑δ)
  (hp : path ↑B ↑β)
  (ht : tangle_path ↑(lt_index.mk' hγβ (B.path.comp hp)))
  (hallp : allowable_path B ) :
  (derivative ((hp.cons (coe_lt_coe.mpr hδβ)).cons (bot_lt_coe _)))
        ((allowable_path_to_struct_perm B) hallp) •
      (f_map_path hγβ hδβ ht).to_near_litter =
    (f_map_path hγβ hδβ
       (allowable_derivative_path {index := ↑β, path := B.path.comp hp} hγβ
            (allowable_derivative_path_comp B hp hallp) •
          ht)).to_near_litter :=
begin
  sorry,
end

lemma flexible_union_non_flexible_cond :
  spec.non_flexible_cond B
    (σ.val ∪ new_flexible_litters bij abij ∪ new_inverse_flexible_litters bij abij) :=
begin
  unfold spec.non_flexible_cond,
  intros hb hg hd hgb hdb hdg hNl hp ht hf hallp h1,
  unfold struct_perm.satisfies at h1,
  unfold struct_perm.satisfies_cond at h1,
  have h := h1 _ hf,
  dsimp at h,
  rw ← h,
  exact unpack_coh_cond hgb hdb hdg hp ht hallp,
end

lemma flexible_union_support_closed :
  (σ.val ∪ new_flexible_litters bij abij ∪ new_inverse_flexible_litters bij abij)
    .domain.support_closed B :=
sorry

lemma flexible_union_flexible_cond :
  ∀ C, spec.flexible_cond B
    (σ.val ∪ new_flexible_litters bij abij ∪ new_inverse_flexible_litters bij abij) C :=
begin
  intro C,
  by_cases (C = A),
  { subst h,
    refine spec.flexible_cond.all _ _,
    { intros L hL,
      by_cases h : ((sum.inr L.to_near_litter, C) ∈ σ.val.domain);
      rw [spec.domain_union, spec.domain_union, set.mem_union, set.mem_union],
      { left, left, exact h, },
      { left, right,
        unfold new_flexible_litters,
        refine ⟨_, _, _⟩,
        { exact (sum.inr (L.to_near_litter, precise_litter_image bij ⟨L, hL, h⟩
                  (abij ⟨L, hL, h⟩)), C), },
        { simp only [subtype.val_eq_coe, set.mem_set_of_eq, set_coe.exists, subtype.coe_mk,
                      prod.mk.inj_iff, eq_self_iff_true, and_true, exists_and_distrib_left],
          use L,
          exact ⟨rfl, ⟨⟨hL, h⟩, rfl⟩⟩, },
        { unfold binary_condition.domain,
          rw sum.elim_inr, } } },
    { intros L hL,
      -- might want to switch naming around if it doesn't shorten code
      by_cases h : ((sum.inr L.to_near_litter, C) ∈ σ.val.range);
      rw [spec.range_union, spec.range_union, set.mem_union, set.mem_union],
      { left, left, exact h, },
      { right,
        unfold new_inverse_flexible_litters,
        refine ⟨_, _, _⟩,
        { exact (sum.inr (precise_litter_inverse_image bij (bij.to_fun (bij.inv_fun ⟨L, hL, h⟩))
            (abij (bij.inv_fun ⟨L, hL, h⟩)).inv,
            (bij.to_fun (bij.inv_fun ⟨L, hL, h⟩)).1.to_near_litter), C) },
        { simp only [subtype.val_eq_coe, set.mem_set_of_eq, equiv.to_fun_as_coe, set_coe.exists,
                      prod.mk.inj_iff, eq_self_iff_true, and_true],
          refine ⟨(bij.inv_fun ⟨L, hL, h⟩), ⟨(bij.inv_fun ⟨L, hL, h⟩).prop, _⟩⟩,
          rw subtype.coe_eta,
          exact ⟨rfl, rfl⟩, },
        { simp only [binary_condition.range, equiv.inv_fun_as_coe, equiv.to_fun_as_coe,
                      equiv.apply_symm_apply, sum.elim_inr], } } } },
  { obtain ⟨hdom, hrge⟩ := σ.prop.flexible_cond C,
    { refine spec.flexible_cond.co_large _ _,
      { convert hdom, ext,
        rw and.congr_right_iff,
        intro hx,
        rw not_iff_not,
        rw [spec.domain_union, spec.domain_union, set.mem_union, set.mem_union],
        split,
        { rintro ((h | ⟨b, hb₁, hb₂⟩) | h),
          { exact h, },
          { unfold new_flexible_litters at hb₁,
            rw set.mem_set_of at hb₁,
            obtain ⟨⟨L, hL₁, hL₂⟩, beq⟩ := hb₁,
            subst beq,
            cases hb₂,
            cases h rfl, },
          { sorry, } },
        { sorry }, },
      { sorry }, },
    { sorry, } }
end

def abij_inv :
  Π (L : {L : litter | flexible L A ∧ (sum.inr L.to_near_litter, A) ∉ σ⁻¹.val.domain}),
    bij.inv'.precise_atom_bijection L :=
λ L, (abij (bij.inv_fun ⟨L, by simpa only [inv_def, spec.inv_domain] using L.property⟩)).inv'

lemma new_flexible_litters_inv :
  (new_flexible_litters bij abij)⁻¹ = new_inverse_flexible_litters bij.inv' (abij_inv bij abij) :=
begin
  ext ⟨_ | ⟨N₁, N₂⟩, C⟩,
  { simp only [has_inv.inv, new_flexible_litters, new_inverse_flexible_litters, set.mem_set_of_eq,
    prod.mk.inj_iff, sum.elim_inl, exists_false, false_and], },
  sorry,
end

lemma new_inverse_flexible_litters_inv :
  (new_inverse_flexible_litters bij abij)⁻¹ = new_flexible_litters bij.inv' (abij_inv bij abij) :=
sorry

lemma forward_eq_backward :
  (σ.val ∪ new_flexible_litters bij abij ∪ new_inverse_flexible_litters bij abij)⁻¹ =
  σ⁻¹.val ∪ new_flexible_litters bij.inv' (abij_inv bij abij) ∪
    new_inverse_flexible_litters bij.inv' (abij_inv bij abij) :=
begin
  rw [spec.inv_union, spec.inv_union, inv_def, set.union_assoc, set.union_assoc,
    new_flexible_litters_inv, new_inverse_flexible_litters_inv],
  congr' 1, rw set.union_comm,
end

lemma flexible_union_allowable :
  spec.allowable_spec B
    (σ.val ∪ new_flexible_litters bij abij ∪ new_inverse_flexible_litters bij abij) := {
  forward := {
    one_to_one := flexible_union_one_to_one bij abij,
    atom_cond := flexible_union_atom_cond bij abij,
    near_litter_cond := flexible_union_near_litter_cond bij abij,
    non_flexible_cond := flexible_union_non_flexible_cond bij abij,
    support_closed := flexible_union_support_closed bij abij,
  },
  backward := {
    one_to_one :=
      by { convert flexible_union_one_to_one bij.inv' (abij_inv bij abij),
        rw forward_eq_backward bij abij, },
    atom_cond :=
      by { convert flexible_union_atom_cond bij.inv' (abij_inv bij abij),
        rw forward_eq_backward bij abij, },
    near_litter_cond :=
      by { convert flexible_union_near_litter_cond bij.inv' (abij_inv bij abij),
        rw forward_eq_backward bij abij, },
    non_flexible_cond :=
      by { convert flexible_union_non_flexible_cond bij.inv' (abij_inv bij abij),
        rw forward_eq_backward bij abij, },
    support_closed :=
      by { convert flexible_union_support_closed bij.inv' (abij_inv bij abij),
        rw forward_eq_backward bij abij, },
  },
  flexible_cond := flexible_union_flexible_cond bij abij,
}

lemma le_flexible_union :
  σ ≤ ⟨σ.val ∪ new_flexible_litters bij abij ∪ new_inverse_flexible_litters bij abij,
    flexible_union_allowable bij abij⟩ := {
  subset := by { simp_rw set.union_assoc, exact set.subset_union_left _ _, },
  all_flex_domain := begin
    intros L N' C hN' hσ₁ hσ₂ L' hL',
    split,
    { rw [spec.domain_union, spec.domain_union],
      by_cases (sum.inr L'.to_near_litter, C) ∈ σ.val.domain,
      { exact or.inl (or.inl h), },
      { have : A = C,
        { obtain ((_ | ⟨L₁, hL₁⟩) | ⟨L₁, hL₁⟩) := hσ₂,
          { cases hσ₁ hσ₂, },
          { exact (congr_arg prod.snd hL₁).symm, },
          { exact (congr_arg prod.snd hL₁).symm, }, },
        subst this,
        exact or.inl (or.inr ⟨_, ⟨⟨L', hL', h⟩, rfl⟩, rfl⟩), } },
    { sorry }
  end,
  all_flex_range := begin
    intros L N' C hN' hσ₁ hσ₂ L' hL',
    split,
    { rw [spec.domain_union, spec.domain_union],
      by_cases (sum.inr L'.to_near_litter, C) ∈ σ.val.domain,
      { exact or.inl (or.inl h), },
      { have : A = C,
        { obtain ((_ | ⟨L₁, hL₁⟩) | ⟨L₁, hL₁⟩) := hσ₂,
          { cases hσ₁ hσ₂, },
          { exact (congr_arg prod.snd hL₁).symm, },
          { exact (congr_arg prod.snd hL₁).symm, }, },
        subst this,
        exact or.inl (or.inr ⟨_, ⟨⟨L', hL', h⟩, rfl⟩, rfl⟩), } },
    { sorry }
  end,
  all_atoms_domain := begin
    rintros a b L ha C hσ₁ ((hσ₂ | hσ₂) | hσ₂),
    { cases hσ₁ hσ₂, },
    { simpa only [new_flexible_litters, set.mem_set_of_eq, prod.mk.inj_iff,
        false_and, exists_false] using hσ₂, },
    { simpa only [new_inverse_flexible_litters, set.mem_set_of_eq, prod.mk.inj_iff,
        false_and, exists_false] using hσ₂, }
  end,
  all_atoms_range := begin
    rintros a b L ha C hσ₁ ((hσ₂ | hσ₂) | hσ₂),
    { cases hσ₁ hσ₂, },
    { simpa only [new_flexible_litters, set.mem_set_of_eq, prod.mk.inj_iff,
        false_and, exists_false] using hσ₂, },
    { simpa only [new_inverse_flexible_litters, set.mem_set_of_eq, prod.mk.inj_iff,
        false_and, exists_false] using hσ₂, }
  end,
}

/-- Nothing constrains a flexible litter, so we don't have any hypothesis about the fact that all
things that constrain it lie in `σ` already. -/
lemma exists_ge_flexible {L : litter} (hL : flexible L A) :
  ∃ ρ ≥ σ, (⟨sum.inr L.to_near_litter, A⟩ : support_condition B) ∈ ρ.val.domain :=
begin
  by_cases (sum.inr L.to_near_litter, A) ∈ σ.val.domain,
  { exact ⟨σ, le_rfl, h⟩, },
  obtain ⟨hdom, hrge⟩ | ⟨hdom, hrge⟩ := σ.property.flexible_cond A,
  swap, { exfalso, exact h (hdom L hL), },
  have bij : rough_bijection A σ.val.domain σ.val.range :=
    (cardinal.eq.mp $ eq.trans hdom.symm hrge).some,
  have abij : ∀ L, bij.precise_atom_bijection L,
  { refine λ L, (cardinal.eq.mp _).some,
    rw [cardinal.mk_sep, cardinal.mk_sep],
    transitivity #κ,
    { have := cardinal.mk_sum_compl {a : litter_set L | (sum.inl a.val, A) ∈ σ.val.domain},
      rw mk_litter_set at this,
      refine cardinal.eq_of_add_eq_of_aleph_0_le this _ κ_regular.aleph_0_le,
      convert (small_of_not_mem_spec L) using 1, rw cardinal.mk_sep, },
    { have := cardinal.mk_sum_compl
        {a : litter_set (bij.to_fun L) | (sum.inl a.val, A) ∈ σ.val.range},
      rw mk_litter_set at this, symmetry,
      refine cardinal.eq_of_add_eq_of_aleph_0_le this _ κ_regular.aleph_0_le,
      convert (small_of_rough_bijection bij L) using 1, rw cardinal.mk_sep, },
  },
  refine ⟨_, le_flexible_union bij abij, _⟩,
  rw [spec.domain_union, spec.domain_union],
  left, right,
  unfold new_flexible_litters,
  refine ⟨_, ⟨⟨L, hL, ‹_›⟩, rfl⟩, rfl⟩,
end

end exists_ge_flexible

section exists_ge_non_flexible

/-!
For a non-flexible litter `L = f_{γδ}^A(t)`, assume the designated support for `t` already lies in
`σ`. Then, look at `σ` restricted to `γ` - this is allowable by the restriction lemma, and by the
inductive freedom of action assumption extends to `π'`, a `γ`-allowable permutation. We can map `t`
using `π'` to find where `L` is supposed to be sent under `π`. We then add this result to `σ`.
-/

variables {B} {σ : allowable_partial_perm B}
  ⦃β : Λ⦄ ⦃γ : type_index⦄ ⦃δ : Λ⦄

/-- Since the designated support of `t` is included in `σ`, any allowable permutation `π'` that
satisfies `σ` at the lower level gives the same result for the image of `f_map_path hγ hδ t`.
This means that although `π` was chosen arbitrarily, its value is not important, and we could have
chosen any other permutation and arrived at the same value for the image of `f_map_path hγ hδ t`.

Don't prove this unless we need it - it sounds like an important mathematical point but potentially
not for the formalisation itself. -/
lemma non_flexible_union_unique (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
  (C : path (B : type_index) β)
  (t : tangle_path ((lt_index.mk' hγ (B.path.comp C)) : le_index α))
  (π : allowable_path (lt_index.mk' (coe_lt_coe.mpr hδ) (B.path.comp C) : le_index α))
  (hπ : (allowable_path_to_struct_perm _ π).satisfies $ σ.val.lower (C.cons $ coe_lt_coe.mpr hδ)) :
  ∀ (π' : allowable_path (lt_index.mk' (coe_lt_coe.mpr hδ) (B.path.comp C) : le_index α))
    (hπ' : (allowable_path_to_struct_perm _ π').satisfies $
      σ.val.lower (C.cons $ coe_lt_coe.mpr hδ)),
    struct_perm.derivative (path.cons path.nil $ bot_lt_coe _)
      (allowable_path_to_struct_perm _ π) • (f_map_path hγ hδ t).to_near_litter =
    struct_perm.derivative (path.cons path.nil $ bot_lt_coe _)
      (allowable_path_to_struct_perm _ π') • (f_map_path hγ hδ t).to_near_litter :=
sorry

private noncomputable def new_non_flexible_constraint (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
  {C : path (B : type_index) β}
  (t : tangle_path ((lt_index.mk' hγ (B.path.comp C)) : le_index α))
  {π : allowable_path (lt_index.mk' (coe_lt_coe.mpr hδ) (B.path.comp C) : le_index α)}
  (hπ : (allowable_path_to_struct_perm _ π).satisfies $ σ.val.lower (C.cons $ coe_lt_coe.mpr hδ)) :
    binary_condition B :=
  (sum.inr ((f_map_path hγ hδ t).to_near_litter,
      struct_perm.derivative (path.cons path.nil $ bot_lt_coe _)
        (allowable_path_to_struct_perm _ π) • (f_map_path hγ hδ t).to_near_litter),
      (C.cons $ coe_lt_coe.mpr hδ).cons (bot_lt_coe _))

variables (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
  {C : path (B : type_index) β}
  (t : tangle_path ((lt_index.mk' hγ (B.path.comp C)) : le_index α))
  {π : allowable_path (lt_index.mk' (coe_lt_coe.mpr hδ) (B.path.comp C) : le_index α)}
  (hπ : (allowable_path_to_struct_perm _ π).satisfies $ σ.val.lower (C.cons $ coe_lt_coe.mpr hδ))

lemma non_flexible_union_one_to_one_forward :
  spec.one_to_one_forward B (σ.val ∪ {new_non_flexible_constraint hγ hδ hγδ t hπ}) :=
sorry

lemma non_flexible_union_one_to_one_backward :
  spec.one_to_one_forward B (σ.val ∪ {new_non_flexible_constraint hγ hδ hγδ t hπ})⁻¹ :=
sorry

lemma non_flexible_union_atom_cond_forward :
  ∀ L C, spec.atom_cond B (σ.val ∪ {new_non_flexible_constraint hγ hδ hγδ t hπ}) L C :=
sorry

lemma non_flexible_union_atom_cond_backward :
  ∀ L C, spec.atom_cond B (σ.val ∪ {new_non_flexible_constraint hγ hδ hγδ t hπ})⁻¹ L C :=
sorry

lemma non_flexible_union_near_litter_cond_forward :
  ∀ N₁ N₂ C, spec.near_litter_cond B
    (σ.val ∪ {new_non_flexible_constraint hγ hδ hγδ t hπ}) N₁ N₂ C :=
sorry

lemma non_flexible_union_near_litter_cond_backward :
  ∀ N₁ N₂ C, spec.near_litter_cond B
    (σ.val ∪ {new_non_flexible_constraint hγ hδ hγδ t hπ})⁻¹ N₁ N₂ C :=
sorry

lemma non_flexible_union_non_flexible_cond_forward :
  spec.non_flexible_cond B (σ.val ∪ {new_non_flexible_constraint hγ hδ hγδ t hπ}) :=
begin
  unfold spec.non_flexible_cond,
  intros hb hg hd hgb hdb hdg hNl hp ht hf hallp h1,
  unfold struct_perm.satisfies at h1,
  unfold struct_perm.satisfies_cond at h1,
  have h := h1 _ hf,
  dsimp at h,
  rw ← h,
  exact unpack_coh_cond hgb hdb hdg hp ht hallp,
end

lemma non_flexible_union_non_flexible_cond_backward :
  spec.non_flexible_cond B (σ.val ∪ {new_non_flexible_constraint hγ hδ hγδ t hπ})⁻¹ :=
sorry

lemma non_flexible_union_support_closed_forward :
  (σ.val ∪ {new_non_flexible_constraint hγ hδ hγδ t hπ}).domain.support_closed B :=
sorry

lemma non_flexible_union_support_closed_backward :
  (σ.val ∪ {new_non_flexible_constraint hγ hδ hγδ t hπ}).range.support_closed B :=
sorry

lemma non_flexible_union_flexible_cond :
  ∀ C, spec.flexible_cond B (σ.val ∪ {new_non_flexible_constraint hγ hδ hγδ t hπ}) C :=
sorry

lemma non_flexible_union_allowable :
  spec.allowable_spec B (σ.val ∪ {new_non_flexible_constraint hγ hδ hγδ t hπ}) := {
  forward := {
    one_to_one := non_flexible_union_one_to_one_forward hγ hδ hγδ t hπ,
    atom_cond := non_flexible_union_atom_cond_forward hγ hδ hγδ t hπ,
    near_litter_cond := non_flexible_union_near_litter_cond_forward hγ hδ hγδ t hπ,
    non_flexible_cond := non_flexible_union_non_flexible_cond_forward hγ hδ hγδ t hπ,
    support_closed := non_flexible_union_support_closed_forward hγ hδ hγδ t hπ,
  },
  backward := {
    one_to_one := non_flexible_union_one_to_one_backward hγ hδ hγδ t hπ,
    atom_cond := non_flexible_union_atom_cond_backward hγ hδ hγδ t hπ,
    near_litter_cond := non_flexible_union_near_litter_cond_backward hγ hδ hγδ t hπ,
    non_flexible_cond := non_flexible_union_non_flexible_cond_backward hγ hδ hγδ t hπ,
    support_closed := by { rw spec.inv_domain,
      exact non_flexible_union_support_closed_backward hγ hδ hγδ t hπ },
  },
  flexible_cond := non_flexible_union_flexible_cond hγ hδ hγδ t hπ,
}

lemma le_non_flexible_union :
  σ ≤ ⟨_, non_flexible_union_allowable hγ hδ hγδ t hπ⟩ := {
  subset := set.subset_union_left _ _,
  all_flex_domain := begin
    rintros L N' C' hN' hσ₁ (hσ₂ | hσ₂),
    { cases hσ₁ hσ₂, },
    { simp only [new_non_flexible_constraint, set.mem_singleton_iff, prod.mk.inj_iff] at hσ₂,
      exfalso,
      cases hN' hγ hδ hγδ C t,
      { exact h (litter.to_near_litter_inj hσ₂.left.left), },
      { exact h hσ₂.right, } }
  end,
  all_flex_range := begin
    rintros L N' C' hN' hσ₁ (hσ₂ | hσ₂),
    { cases hσ₁ hσ₂, },
    { simp only [new_non_flexible_constraint, set.mem_singleton_iff, prod.mk.inj_iff] at hσ₂,
      exfalso,
      cases hN' hγ hδ hγδ C t,
      { -- This is the unpacked coherence condition on L and f.
        -- We need to change C and t to be the correct parameters here.
        sorry },
      { exact h hσ₂.right, } }
  end,
  all_atoms_domain := begin
    rintros a b L ha C hσ₁ (hσ₂ | hσ₂),
    { cases hσ₁ hσ₂, },
    { simpa only [new_non_flexible_constraint, set.mem_singleton_iff, prod.mk.inj_iff,
        false_and] using hσ₂, }
  end,
  all_atoms_range := begin
    rintros a b L ha C hσ₁ (hσ₂ | hσ₂),
    { cases hσ₁ hσ₂, },
    { simpa only [new_non_flexible_constraint, set.mem_singleton_iff, prod.mk.inj_iff,
        false_and] using hσ₂, }
  end,
}

lemma exists_ge_non_flexible (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
  {C : path (B : type_index) β}
  (t : tangle_path ((lt_index.mk' hγ (path.comp B.path C)) : le_index α))
  (hσ : ∀ c, c ≺ (sum.inr (f_map_path hγ hδ t).to_near_litter,
    (C.cons $ coe_lt_coe.mpr hδ).cons (bot_lt_coe _)) →
    c ∈ σ.val.domain)
  (foa : ∀ (B : lt_index α), freedom_of_action (B : le_index α)) :
  ∃ ρ ≥ σ, (sum.inr (f_map_path hγ hδ t).to_near_litter,
    (C.cons $ coe_lt_coe.mpr hδ).cons (bot_lt_coe _)) ∈
    ρ.val.domain :=
begin
  have hS : ∀ (c : support_condition γ), c ∈ (designated_support_path t).carrier →
    (c.fst, (C.cons hγ).comp c.snd) ∈ σ.val.domain :=
  λ (c : support_condition γ) (hc : c ∈ (designated_support_path t).carrier),
    hσ ⟨c.fst, path.comp (path.cons C hγ) c.snd⟩ (constrains.f_map hγ hδ hγδ C t c hc),
  have := lower_allowable B σ.val σ.property (C.cons $ coe_lt_coe.mpr hδ)
    ((coe_lt_coe.mpr hδ).trans_le (le_of_path C)),
  obtain ⟨π, hπ⟩ := foa (lt_index.mk' (coe_lt_coe.mpr hδ) (B.path.comp C))
    ⟨σ.val.lower (C.cons $ coe_lt_coe.mpr hδ), this⟩,
  have := struct_perm.derivative (path.cons path.nil $ bot_lt_coe _)
    (allowable_path_to_struct_perm _ π) • (f_map_path hγ hδ t).to_near_litter,
  refine ⟨_, le_non_flexible_union hγ hδ hγδ t hπ, _⟩,
  rw spec.domain_union,
  right, simp only [spec.domain, set.image_singleton, set.mem_singleton_iff], refl,
end

end exists_ge_non_flexible

lemma total_of_maximal_aux (σ : allowable_partial_perm B) (hσ : ∀ ρ ≥ σ, ρ = σ)
  (foa : ∀ (B : lt_index α), freedom_of_action (B : le_index α)) :
  Π (c : support_condition B), c ∈ σ.val.domain
| ⟨sum.inl a, A⟩ := begin
    obtain ⟨ρ, hρ₁, hρ₂⟩ := exists_ge_atom B σ a A (λ c hc, total_of_maximal_aux c),
    rw hσ ρ hρ₁ at hρ₂,
    exact hρ₂,
  end
| ⟨sum.inr N, A⟩ := begin
    by_cases hnl : litter_set N.fst = N.snd,
    { -- This is a litter.
      have hind : ∀ c (hc : c ≺ ⟨sum.inr N, A⟩), c ∈ σ.val.domain := λ c hc, total_of_maximal_aux c,
      obtain ⟨L, N, hN⟩ := N,
      dsimp only at hnl, rw subtype.coe_mk at hnl, subst hnl,
      by_cases flexible L A,
      { -- This litter is flexible.
        obtain ⟨ρ, hρ₁, hρ₂⟩ := exists_ge_flexible h,
        rw hσ ρ hρ₁ at hρ₂,
        exact hρ₂, },
      { -- This litter is non-flexible.
        unfold flexible at h,
        push_neg at h,
        obtain ⟨β, δ, γ, hγ, hδ, hγδ, C, t, hL, hA⟩ := h,
        cases hA,
        cases hL,
        obtain ⟨ρ, hρ₁, hρ₂⟩ := exists_ge_non_flexible hγ hδ hγδ t hind foa,
        rw hσ ρ hρ₁ at hρ₂,
        exact hρ₂, }, },
    { -- This is a near-litter.
      obtain ⟨ρ, hρ₁, hρ₂⟩ := exists_ge_near_litter B σ N A hnl (λ c hc, total_of_maximal_aux c),
      rw hσ ρ hρ₁ at hρ₂,
      exact hρ₂, }
  end
using_well_founded { dec_tac := `[assumption] }

/-- Any maximal allowable partial permutation under `≤` is total. -/
lemma total_of_maximal (σ : allowable_partial_perm B) (hσ : ∀ ρ ≥ σ, ρ = σ)
  (foa : ∀ (B : lt_index α), freedom_of_action (B : le_index α)) : σ.val.total :=
set.eq_univ_of_forall (total_of_maximal_aux B σ hσ foa)

/-- Any maximal allowable partial permutation under `≤` is co-total. -/
lemma co_total_of_maximal (σ : allowable_partial_perm B) (hσ : ∀ ρ ≥ σ, ρ = σ)
  (foa : ∀ (B : lt_index α), freedom_of_action (B : le_index α)) : σ.val.co_total :=
begin
  refine spec.co_total_of_inv_total σ.val (total_of_maximal B σ⁻¹ _ foa),
  intros ρ hρ,
  convert congr_arg has_inv.inv (hσ ρ⁻¹ _),
  rw inv_inv,
  convert inv_le B σ⁻¹ ρ hρ,
  rw inv_inv,
end

variable (α)

/-- The hypothesis that we are in the synthesised context at `α`.
This allows us to combine a set of allowable permutations at all lower paths into an allowable
permutation at level `α`
This may not be the best way to phrase the assumption - the definition is subject to change when
we actually create a proof of the proposition. -/
def synthesised_context : Prop := Π (σ : allowable_partial_perm ⟨α, path.nil⟩)
  (hσ₁ : σ.val.total)
  (hσ₂ : σ.val.co_total)
  (foa : ∀ (B : lt_index α), freedom_of_action (B : le_index α))
  (lower_allowable_spec :
    ∀ (B : proper_lt_index α), spec.allowable_spec (B : le_index α) (σ.val.lower B.path))
  (exists_lower_allowable :
    ∀ (B : proper_lt_index α), ∃ (π : allowable_path (B : le_index α)),
      ((allowable_path_to_struct_perm (B : le_index α)) π).satisfies (σ.val.lower B.path)),
  ∃ (π : allowable_path ⟨α, path.nil⟩),
    ((allowable_path_to_struct_perm ⟨α, path.nil⟩) π).satisfies σ.val

variable {α}

/-- Any allowable partial permutation extends to an allowable permutation at level `α`, given that
it is total and co-total. This is `total-allowable-partial-perm-actual` in the blueprint. -/
lemma extends_to_allowable_of_total (σ : allowable_partial_perm ⟨α, path.nil⟩)
  (hσ₁ : σ.val.total) (hσ₂ : σ.val.co_total)
  (foa : ∀ (B : lt_index α), freedom_of_action (B : le_index α))
  (syn : synthesised_context α) :
  ∃ (π : allowable_path ⟨α, path.nil⟩), (allowable_path_to_struct_perm _ π).satisfies σ.val :=
begin
  have lower_allowable_spec :
    ∀ (B : proper_lt_index α), (σ.val.lower B.path).allowable_spec (B : le_index α),
  { intro B,
    have := lower_allowable ⟨α, path.nil⟩ σ.val σ.property B.path
      (coe_lt_coe.mpr (B.index_lt.trans_le (coe_le_coe.mp $ le_of_path B.path'))),
    rw path.nil_comp at this,
    exact this, },
  have exists_lower_allowable : ∀ (B : proper_lt_index α), ∃ (π : allowable_path (B : le_index α)),
    (allowable_path_to_struct_perm (B : le_index α) π).satisfies (σ.val.lower B.path) :=
    λ B, foa B ⟨σ.val.lower B.path, lower_allowable_spec B⟩,
  exact syn σ hσ₁ hσ₂ foa lower_allowable_spec exists_lower_allowable,
end

end allowable_partial_perm

/-- The *freedom of action theorem*. If freedom of action holds at all lower levels and paths (all
`B : lt_index` in our formulation), it holds at level `α`. -/
theorem freedom_of_action_propagates
  (foa : ∀ (B : lt_index α), freedom_of_action (B : le_index α))
  (syn : allowable_partial_perm.synthesised_context α) :
  freedom_of_action ⟨α, path.nil⟩ :=
begin
  intro σ,
  obtain ⟨ρ, -, hσρ, hρ⟩ := allowable_partial_perm.maximal_perm ⟨α, path.nil⟩ σ,
  have : ∀ (τ : allowable_partial_perm ⟨α, path.nil⟩), τ ≥ ρ → τ = ρ :=
    λ τ hτ, subtype.val_inj.mp
      (set.eq_of_subset_of_subset (hρ τ (le_trans hσρ hτ) hτ).subset hτ.subset),
  have ρ_total := allowable_partial_perm.total_of_maximal ⟨α, path.nil⟩ ρ this foa,
  have ρ_co_total := allowable_partial_perm.co_total_of_maximal ⟨α, path.nil⟩ ρ this foa,
  obtain ⟨π, hπ⟩ := ρ.extends_to_allowable_of_total ρ_total ρ_co_total foa syn,
  exact ⟨π, struct_perm.satisfies_mono _ σ.val ρ.val hσρ.subset hπ⟩,
end

end con_nf
