import phase2.basic

/-!
# The freedom of action theorem

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
-/

open function quiver

universe u

namespace con_nf
variables [params.{u}]

open struct_perm

/- The following code may not be relevant for the newest way we're implementing the FoA theorem.

/-- An α-local bijection associates to each extended type index `A` a domain of atoms,
and defines an injection from that domain to itself.
It must satisfy two conditions, that the map is really an injection, and that the
intersection of the domain with any litter is small. -/
structure local_bijection (α : Λ) :=
(domain (A : extended_index α) : set atom)
(to_fun (A) : equiv.perm (domain A))
(litter_inter (A) (i : litter) : small $ domain A ∩ litter_set i)

instance (α : Λ) : has_coe_to_fun (local_bijection α) (λ π₀, Π A, π₀.domain A → π₀.domain A) :=
⟨λ π₀ A, (π₀.to_fun A).to_fun⟩

/-- `a` is an exception of the near-litter permutation `f` if it is not sent to the corresponding
litter under either `f` or `f⁻¹`. -/
def near_litter_perm.exception (f : near_litter_perm) (a : atom) : Prop :=
f.atom_perm a ∉ litter_set (f.litter_perm a.1) ∨ f.atom_perm⁻¹ a ∉ litter_set (f.litter_perm⁻¹ a.1)

-/

/-- A *binary condition* is like a support condition but uses either two atoms or two near-litters
instead of one. A binary condition `⟨⟨x, y⟩, A⟩` represents the constraint `π_A(x) = y` on an
allowable permutation. -/
@[derive [inhabited, mul_action near_litter_perm, mul_action (struct_perm ‹Λ›)]]
def binary_condition (α : Λ) : Type u :=
((atom × atom) ⊕ (near_litter × near_litter)) × extended_index α

/-- Converts a binary condition `⟨⟨x, y⟩, A⟩` into the support condition `⟨x, A⟩`. -/
def binary_condition.domain {α : Λ} (cond : binary_condition α) : support_condition α :=
⟨cond.fst.elim (λ atoms, sum.inl atoms.fst) (λ Ns, sum.inr Ns.fst), cond.snd⟩

/-- Converts a binary condition `⟨⟨x, y⟩, A⟩` into the support condition `⟨y, A⟩`. -/
def binary_condition.range {α : Λ} (cond : binary_condition α) : support_condition α :=
⟨cond.fst.elim (λ atoms, sum.inl atoms.snd) (λ Ns, sum.inr Ns.snd), cond.snd⟩

/-- A *unary specification* is a set of support conditions. This can be thought of as either the
domain or range of a `spec`. -/
abbreviation unary_spec (α : Λ) : Type u := set (support_condition α)

/-- A *specification* of an allowable permutation is a set of binary conditions on the allowable
permutation. -/
abbreviation spec (α : Λ) : Type u := set (binary_condition α)

/-- The domain of a specification is the unary specification consisting of the domains of all
binary conditions in the specification. -/
def spec.domain {α : Λ} (σ : spec α) : unary_spec α := binary_condition.domain '' σ
/-- The range of a specification is the unary specification consisting of the ranges of all
binary conditions in the specification. -/
def spec.range {α : Λ} (σ : spec α) : unary_spec α := binary_condition.range '' σ

/-- A structural permutation *satisfies* a condition `⟨⟨x, y⟩, A⟩` if `π_A(x) = y`. -/
def struct_perm.satisfies_cond {α : Λ} (π : struct_perm α) (c : binary_condition α) : Prop :=
c.fst.elim
  (λ atoms, derivative c.snd π • atoms.fst = atoms.snd)
  (λ Ns, derivative c.snd π • Ns.fst = Ns.snd)

@[simp] lemma struct_perm.satisfies_cond_atoms {α : Λ} (π : struct_perm α) (a b : atom)
  (A : extended_index α) : π.satisfies_cond ⟨sum.inl ⟨a, b⟩, A⟩ ↔ derivative A π • a = b :=
by { unfold struct_perm.satisfies_cond, refl }

@[simp] lemma struct_perm.satisfies_cond_near_litters {α : Λ} (π : struct_perm α)
  (M N : near_litter) (A : extended_index α) :
  π.satisfies_cond ⟨sum.inr ⟨M, N⟩, A⟩ ↔ derivative A π • M = N :=
by { unfold struct_perm.satisfies_cond, refl }

/-- A structural permutation *satisfies* a specification if for all conditions `⟨⟨x, y⟩, A⟩` in the
specification, we have `π_A(x) = y`. -/
def struct_perm.satisfies {α : Λ} (π : struct_perm α) (σ : spec α) : Prop :=
∀ c ∈ σ, π.satisfies_cond c

/- There is an injection from the type of structural permutations to the type of specifications,
in such a way that any structural permutation satisfies its specification. We construct this
specification by simply drawing the graph of the permutation. It suffices to construct the graph of
atoms with each derivative; the graphs of near-litters is then implicit. -/
def struct_perm.to_spec {α : Λ} (π : struct_perm α) : spec α :=
set.range (λ (x : atom × extended_index α), ⟨sum.inl ⟨x.fst, derivative x.snd π • x.fst⟩, x.snd⟩)

/-- Any structural permutation satisfies its own specification. -/
lemma struct_perm.satisfies_to_spec {α : Λ} (π : struct_perm α) : π.satisfies π.to_spec := sorry

/-- The map from structural permutations to their specifications is injective. -/
lemma struct_perm.to_spec_injective (α : Λ) : injective (@struct_perm.to_spec _ α) := sorry

/-- We can extend any support condition to one of a higher proper type index `α` by providing a path
connecting the old extended index up to `α`. -/
def support_condition.extend_path {α β : Λ} (c : support_condition β)
  (A : path (α : type_index) β) : support_condition α := ⟨c.fst, A.comp c.snd⟩

/-- We can extend any binary condition to one of a higher proper type index `α` by providing a path
connecting the old extended index up to `α`. -/
def binary_condition.extend_path {α β : Λ} (c : binary_condition β)
  (A : path (α : type_index) β) : binary_condition α := ⟨c.fst, A.comp c.snd⟩

/-- We can lower a unary specification to a lower proper type index with respect to a path
`A : α ⟶ β` by only keeping support conditions whose paths begin with `A`. -/
def unary_spec.lower {α β : Λ} (σ : unary_spec α) (A : path (α : type_index) β) : unary_spec β :=
{c | c.extend_path A ∈ σ}

/-- We can lower a specification to a lower proper type index with respect to a path
`A : α ⟶ β` by only keeping binary conditions whose paths begin with `A`. -/
def spec.lower {α β : Λ} (σ : spec α) (A : path (α : type_index) β) : spec β :=
{c | c.extend_path A ∈ σ}

end con_nf
