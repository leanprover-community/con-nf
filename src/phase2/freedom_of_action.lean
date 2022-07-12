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

open function quiver with_bot cardinal
open_locale cardinal

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
@[derive [inhabited, mul_action near_litter_perm, mul_action (struct_perm ‹type_index›)]]
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

/-- A *unary specification* is a set of support conditions. This can be thought of as either the
domain or range of a `spec`. -/
abbreviation unary_spec (α : type_index) : Type u := set (support_condition α)

/-- A *specification* of an allowable permutation is a set of binary conditions on the allowable
permutation. -/
abbreviation spec (α : type_index) : Type u := set (binary_condition α)

/-- There are `< μ` unary specifications. TODO: is this lemma actually required? -/
lemma mk_unary_spec (α : type_index) : #(unary_spec α) < #μ := sorry
/-- There are `< μ` support specifications. -/
lemma mk_spec (α : type_index) : #(spec α) < #μ := sorry

instance (α : type_index) : has_inv (spec α) := ⟨λ σ, {c | c⁻¹ ∈ σ}⟩

/-- The domain of a specification is the unary specification consisting of the domains of all
binary conditions in the specification. -/
def spec.domain {α : type_index} (σ : spec α) : unary_spec α := binary_condition.domain '' σ
/-- The range of a specification is the unary specification consisting of the ranges of all
binary conditions in the specification. -/
def spec.range {α : type_index} (σ : spec α) : unary_spec α := binary_condition.range '' σ

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

/- There is an injection from the type of structural permutations to the type of specifications,
in such a way that any structural permutation satisfies its specification. We construct this
specification by simply drawing the graph of the permutation. It suffices to construct the graph of
atoms with each derivative; the graphs of near-litters is then implicit. -/
def struct_perm.to_spec {α : type_index} (π : struct_perm α) : spec α :=
set.range (λ (x : atom × extended_index α), ⟨sum.inl ⟨x.fst, derivative x.snd π • x.fst⟩, x.snd⟩)

/-- Any structural permutation satisfies its own specification. -/
lemma struct_perm.satisfies_to_spec {α : type_index} (π : struct_perm α) : π.satisfies π.to_spec :=
begin
  unfold struct_perm.satisfies struct_perm.to_spec struct_perm.satisfies_cond,
  rintros ⟨⟨x, y⟩ | ⟨x, y⟩, A⟩ ⟨⟨a, b⟩, ha⟩; simp only [prod.mk.inj_iff] at ha,
  { simp,
    rw [← ha.2, ← ha.1.1], exact ha.1.2 },
  cases ha.1
end

/-- The map from structural permutations to their specifications is injective. -/
lemma struct_perm.to_spec_injective (α : type_index) : injective (@struct_perm.to_spec _ α) := sorry

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
lemma unary_spec.lower_nil {α β γ : type_index} (σ : unary_spec α) :
  σ.lower path.nil = σ :=
begin
  unfold unary_spec.lower support_condition.extend_path,
  simp,
end

/-- The lowering map is functorial. -/
lemma unary_spec.lower_lower {α β γ : type_index} (σ : unary_spec α)
  (A : path (α : type_index) β) (B : path (β : type_index) γ) :
  (σ.lower A).lower B = σ.lower (path.comp A B) :=
begin
  unfold unary_spec.lower support_condition.extend_path,
  simp,
end

/-- We can lower a specification to a lower proper type index with respect to a path
`A : α ⟶ β` by only keeping binary conditions whose paths begin with `A`. -/
def spec.lower {α β : type_index} (σ : spec α) (A : path (α : type_index) β) : spec β :=
{c | c.extend_path A ∈ σ}

/-- Lowering along the empty path does nothing. -/
lemma spec.lower_nil {α β γ : type_index} (σ : spec α) :
  σ.lower path.nil = σ :=
begin
  unfold spec.lower binary_condition.extend_path,
  simp,
end

/-- The lowering map is functorial. -/
lemma spec.lower_lower {α β γ : type_index} (σ : spec α)
  (A : path (α : type_index) β) (B : path (β : type_index) γ) :
  (σ.lower A).lower B = σ.lower (path.comp A B) :=
begin
  unfold spec.lower binary_condition.extend_path,
  simp,
end

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
    Note that for this to type check, we must constrain `γ : Λ` not `γ : type_index` - this point
    may need revisiting later.
-/
@[mk_iff] inductive constrains : support_condition B → support_condition B → Prop
| mem_litter (L : litter) (a ∈ litter_set L) (A : extended_index B) :
    constrains ⟨sum.inr L.to_near_litter, A⟩ ⟨sum.inl a, A⟩
| near_litter (N : near_litter) (hN : litter_set N.fst ≠ N.snd) (A : extended_index B) :
    constrains ⟨sum.inr N.fst.to_near_litter, A⟩ ⟨sum.inr N, A⟩
| symm_diff (N : near_litter) (a ∈ litter_set N.fst ∆ N.snd) (A : extended_index B) :
    constrains ⟨sum.inl a, A⟩ ⟨sum.inr N, A⟩
| f_map {β δ : Λ} {γ : type_index} (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
    (A : path (B : type_index) β)
    (t : tangle_path ((lt_index.mk' hγ (path.comp B.path A)) : le_index α))
    (c ∈ (designated_support_path t).carrier) :
    constrains
      ⟨c.fst, path.comp (path.cons A hγ) c.snd⟩
      ⟨sum.inr (f_map_path
        (proper_lt_index.mk'
          (hδ.trans_le (coe_le_coe.mp $ le_of_path (path.comp B.path A))) path.nil) t)
        .to_near_litter, path.cons (path.cons A (coe_lt_coe.mpr hδ)) (bot_lt_coe _)⟩

/-! We declare new notation for the "constrains" relation on support conditions. -/
local infix ` ≺ `:50 := constrains _ _

/-- The `≺` relation is well-founded. By the conditions on orderings, if we have `⟨x, A⟩ ≺ ⟨y, B⟩`,
then `x < y` in `µ`, under the `to_tangle_path` or `typed_singleton_path` maps. -/
lemma constrains_wf : well_founded (constrains α B) := sorry

variables {α} {B}

/-- A litter and extended index is *flexible* if the associated support condition is a minimal
element with respect to the relation `≺`. In other words, it is not constrained by anything. -/
def flexible (L : litter) (A : extended_index B) : Prop := ∀ c, ¬ c ≺ ⟨sum.inr L.to_near_litter, A⟩

/-- A litter and extended index is flexible iff it is not of the form `f_{γ,δ}^A(x)` for some
`x ∈ τ_{γ:A}` with conditions defined as above. -/
lemma flexible_iff (L : litter) (A : extended_index B) :
flexible L A ↔ ∀ {β δ : Λ} {γ : type_index} (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
    (A : path (α : type_index) β) (t : tangle_path ((lt_index.mk' hγ A) : le_index α)),
L ≠ (f_map_path (proper_lt_index.mk' (hδ.trans_le (coe_le_coe.mp $ le_of_path A)) path.nil) t) :=
begin
  unfold flexible,
  split; intro h,
  { intros β δ γ hγ hδ hγδ A t ht,
    refine not_not.2 h _, push_neg,
    sorry },
  { intros c hc,
    rw constrains_iff at hc,
    obtain ⟨L, a, ha, A', hc, hA'⟩ | ⟨N, hN, A', hc, hA'⟩ | ⟨N, a, ha, A', hc, hA'⟩ | ⟨β, δ, γ, hγ, hδ, hγδ, A', t, ht, c', hc, h'⟩ := hc,
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
    exact h (congr_arg sigma.fst hLN) }
end

namespace unary_spec

/-- A unary specification is *support-closed* if whenever `⟨f_{γ,δ}^A(x), A⟩ ∈ σ`, `S_{γ:A}`
supports `x`. -/
def support_closed (σ : unary_spec B) : Prop :=
∀ ⦃β δ : Λ⦄ ⦃γ : type_index⦄ (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
  (A : path (B : type_index) β)
  (t : tangle_path ((lt_index.mk' hγ (path.comp B.path A)) : le_index α)),
  (⟨sum.inr (f_map_path (proper_lt_index.mk'
      (hδ.trans_le (coe_le_coe.mp $ le_of_path (path.comp B.path A))) path.nil) t)
    .to_near_litter, path.cons (path.cons A (coe_lt_coe.mpr hδ)) (bot_lt_coe _)⟩
      : support_condition B) ∈ σ →
      supports (allowable_path_to_struct_perm (lt_index.mk' hγ (path.comp B.path A) : le_index α))
        (σ.lower (path.cons A hγ)) t

-- TODO: In the following definitions, is `A` supposed to be an external parameter or included
-- in some kind of quantification?
-- Also, are the definitions even needed when defining things in terms of binary specifications?

/-- A unary specification is *local* if
* for all litters `L` such that `⟨L, A⟩ ∈ σ`, we have `⟨a, A⟩ ∈ σ` for `a ∈ L`, and
* for all litters `L` such that `⟨L, A⟩ ∉ σ`, we have `∥{a ∈ L | ⟨a, A⟩ ∈ σ}∥ < κ`.
TODO: The name "local" is reserved but I don't particularly like `litter_local` either.
-/
def litter_local (σ : unary_spec B) : Prop :=
∀ (L : litter) (A : extended_index B),
@ite _ ((⟨sum.inr L.to_near_litter, A⟩ : support_condition B) ∈ σ) (classical.dec _)
  (∀ a ∈ litter_set L, (⟨sum.inl a, A⟩ : support_condition B) ∈ σ)
  (small {a ∈ litter_set L | (⟨sum.inl a, A⟩ : support_condition B) ∈ σ})

def non_flex_small (σ : unary_spec B) : Prop :=
small {L : litter | ∀ (A : extended_index B), ¬flexible L A}

/-- A unary specification is *flex-small* if it contains either a small amount of flexible litters,
or all of the flexible litters. -/
@[mk_iff] inductive flex_small (σ : unary_spec B) : Prop
| small : small {L : litter | ∃ (A : extended_index B), flexible L A} → flex_small
| all : (∀ L A, flexible L A → (⟨sum.inr L.to_near_litter, A⟩ : support_condition B) ∈ σ) →
    flex_small

end unary_spec

namespace spec

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
@[mk_iff] structure one_to_one_path (σ : spec B) (A : extended_index B) : Prop :=
(left_atom         : ∀ b, {a | (⟨sum.inl ⟨a, b⟩, A⟩ : binary_condition B) ∈ σ}.subsingleton)
(right_atom        : ∀ a, {b | (⟨sum.inl ⟨a, b⟩, A⟩ : binary_condition B) ∈ σ}.subsingleton)
(left_near_litter  : ∀ N, {M | (⟨sum.inr ⟨M, N⟩, A⟩ : binary_condition B) ∈ σ}.subsingleton)
(right_near_litter : ∀ M, {N | (⟨sum.inr ⟨M, N⟩, A⟩ : binary_condition B) ∈ σ}.subsingleton)

/-- A specification is one-to-one if it is one-to-one on all paths. -/
def one_to_one (σ : spec B) : Prop := ∀ A, σ.one_to_one_path A

/-- The allowability condition on atoms.
In an absent litter, we must specify only `< κ`-many atoms.
In a present litter, we can specify either `< κ`-many atoms, or all of the atoms in the litter, and
in this case, almost all of them must be mapped to the right place.
Note that the `small` constructor does not depend on whether the litter is present or absent. -/
@[mk_iff] inductive atom_cond (σ : spec B) (L : litter) (A : extended_index B) : Prop
| small : small {a ∈ litter_set L | (⟨sum.inl a, A⟩ : support_condition B) ∈ σ.domain} → atom_cond
| all (N : near_litter) (atom_map : litter_set L → atom) :
    (⟨sum.inr ⟨L.to_near_litter, N⟩, A⟩ : binary_condition B) ∈ σ →
    (∀ a ∈ litter_set L, (⟨sum.inl ⟨a, atom_map ⟨a, ‹_›⟩⟩, A⟩ : binary_condition B) ∈ σ) →
    small {a : litter_set L | atom_map a ∈ N.snd.val} →
    atom_cond

/-- The allowability condition on near-litters.
If a near-litter is present, so are its litter and all atoms in the symmetric difference, and it is
mapped to the right place. -/
@[mk_iff] inductive near_litter_cond (σ : spec B) (N : near_litter) (A : extended_index B) : Prop
| absent : (∀ M, (⟨sum.inr ⟨N, M⟩, A⟩ : binary_condition B) ∉ σ) → near_litter_cond
| present (M₁ M₂ : near_litter) (atom_map : litter_set N.fst ∆ N.snd → atom) :
    (⟨sum.inr ⟨N, M₁⟩, A⟩ : binary_condition B) ∈ σ →
    (⟨sum.inr ⟨N.fst.to_near_litter, M₂⟩, A⟩ : binary_condition B) ∈ σ →
    (∀ a : litter_set N.fst ∆ N.snd, (⟨sum.inl ⟨a, atom_map a⟩, A⟩ : binary_condition B) ∈ σ) →
    M₁.snd.val = M₂.snd.val ∆ set.range atom_map →
    near_litter_cond

/-- This is the allowability condition for flexible litters.
Either all flexible litters are in both the domain and range (`all`), or there are `μ`-many not in
the domain and `μ`-many not in the range. -/
@[mk_iff] inductive flexible_cond (σ : spec B) : Prop
| co_large :
  #μ = #{L : litter | ∃ (A : extended_index B),
    flexible L A ∧ (⟨sum.inr L.to_near_litter, A⟩ : support_condition B) ∉ σ.domain} →
  #μ = #{L : litter | ∃ (A : extended_index B),
    flexible L A ∧ (⟨sum.inr L.to_near_litter, A⟩ : support_condition B) ∉ σ.range} →
  flexible_cond
| all :
  (∀ L A, flexible L A → (⟨sum.inr L.to_near_litter, A⟩ : support_condition B) ∈ σ.domain) →
  (∀ L A, flexible L A → (⟨sum.inr L.to_near_litter, A⟩ : support_condition B) ∈ σ.range) →
  flexible_cond

/-- The allowability condition on non-flexible litters.
Whenever `σ` contains some condition `⟨⟨f_{γ,δ}^A(g), N⟩, [-1,δ,A]⟩`, then every allowable
permutation extending `σ` has `N = f_{γ,δ}^A(ρ • g)`.
Note: Definition is incomplete, this won't type check until allowable.lean is refactored. -/
def non_flexible_cond (σ : spec B) : Prop :=
∀ ⦃β δ : Λ⦄ ⦃γ : type_index⦄ (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ) (N : near_litter)
  (A : path (B : type_index) β)
  (t : tangle_path ((lt_index.mk' hγ (path.comp B.path A)) : le_index α)),
  (⟨sum.inr ⟨(f_map_path (proper_lt_index.mk'
      (hδ.trans_le (coe_le_coe.mp $ le_of_path (path.comp B.path A))) path.nil) t).to_near_litter,
    N⟩, path.cons (path.cons A (coe_lt_coe.mpr hδ)) (bot_lt_coe _)⟩ : binary_condition B) ∈ σ →
  ∀ (ρ : allowable_path ⟨α, path.nil⟩), true /- ρ.to_struct_perm.satisfies σ -/ →
  N = (f_map_path (proper_lt_index.mk'
      (hδ.trans_le (coe_le_coe.mp $ le_of_path (path.comp B.path A))) path.nil)
      (allowable_derivative_nil_comp (path.cons (path.comp B.path A) hγ) ρ • t)).to_near_litter

variable (B)

structure allowable_spec (σ : spec B) : Prop :=
(domain_closed : σ.domain.support_closed)
(range_closed : σ.range.support_closed)
(one_to_one : σ.one_to_one)
(atom_cond : ∀ L A, σ.atom_cond L A)
(near_litter_cond : ∀ N A, σ.near_litter_cond N A)
(flexible_cond : σ.flexible_cond)
(non_flexible_cond : σ.non_flexible_cond)
(inv_non_flexible_cond : σ⁻¹.non_flexible_cond)

end spec

variable (B)

/-- An *allowable partial permutation* is a specification that is allowable as defined above. -/
def allowable_partial_perm := {σ : spec B // σ.allowable_spec B}

/-- The restriction lemma. If `σ` is a partial allowable permutation, then so is `σ` restricted to
a lower path `A`. The proof should be mostly straightforward. The non-trivial bit is the "co-large
or all" on flexible litters: in a proper restriction, `μ`-many non-flexible litters get freed up
and become flexible, so if it was “all”, it becomes "co-large". -/
lemma lower_allowable (σ : spec B) {β : Λ} (A : path (B : type_index) β) (hβ : (β : type_index) < B)
  (hσ : σ.allowable_spec B) : (σ.lower A).allowable_spec (le_index.mk β (path.cons B.path hβ)) :=
sorry

/-- We say that *freedom of action* holds along a path `B` if any partial allowable permutation `σ`
admits an allowable permutation `π` extending it. -/
def freedom_of_action : Prop := ∀ σ : allowable_partial_perm B,
∃ (π : allowable_path B), (allowable_path_to_struct_perm B π).satisfies σ.val

/-- The action lemma. If freedom of action holds, and `σ` is any allowable partial permutation
that supports some `α`-tangle `t`, then there exists a unique `α`-tangle `σ(t)` such that every
allowable permutation `π` extending `σ` maps `t` to `σ(t)`.

Proof: Freedom of action gives some extension `π`, and hence some candidate value; the support
condition implies that any two extensions agree. -/
lemma exists_tangle_of_supports (σ : allowable_partial_perm B) (t : tangle_path B)
  (ht : supports (allowable_path_to_struct_perm B) σ.val t) :
  ∃ s, ∀ π, (allowable_path_to_struct_perm B π).satisfies σ.val → π • t = s := sorry

namespace allowable_partial_perm

/--
We now define a preorder on partial allowable permutations.
`σ ≤ ρ` means:

* `σ` is a subset of `ρ`;
* if `ρ` has any new flexible litter, then it has all (in both domain and range);
* within each litter, if `ρ.domain` has any new atom, then it must have all
    atoms in that litter (and hence must also have the litter).

Note that the second condition is exactly the condition in `spec.flexible_cond.all`.
-/
structure perm_le (σ ρ : allowable_partial_perm B) : Prop :=
(subset : σ.val ⊆ ρ.val)
(all_flex (L : litter) (N : near_litter) (A : extended_index B) (hL : flexible L A)
  (hσ : (⟨sum.inr ⟨L.to_near_litter, N⟩, A⟩ : binary_condition B) ∉ σ.val)
  (hρ : (⟨sum.inr ⟨L.to_near_litter, N⟩, A⟩ : binary_condition B) ∈ ρ.val) :
  (∀ L A, flexible L A → (⟨sum.inr L.to_near_litter, A⟩ : support_condition B) ∈ ρ.val.domain) ∧
  (∀ L A, flexible L A → (⟨sum.inr L.to_near_litter, A⟩ : support_condition B) ∈ ρ.val.range))
(all_atoms (a b : atom) (L : litter) (ha : a ∈ litter_set L) (A : extended_index B)
  (hσ : (⟨sum.inl ⟨a, b⟩, A⟩ : binary_condition B) ∉ σ.val)
  (hρ : (⟨sum.inl ⟨a, b⟩, A⟩ : binary_condition B) ∈ ρ.val) :
  ∀ c ∈ litter_set L, ∃ d, (⟨sum.inl ⟨c, d⟩, A⟩ : binary_condition B) ∈ ρ.val)

instance has_le : has_le (allowable_partial_perm B) := ⟨perm_le B⟩

/-! We now prove that the claimed preorder really is a preorder. -/

lemma extends_refl (σ : allowable_partial_perm B) : σ ≤ σ :=
⟨set.subset.rfl,
 λ _ _ _ _ h1 h2, by cases h1 h2,
 λ _ _ _ _ _ h1 h2, by cases h1 h2⟩

lemma extends_trans (ρ σ τ : allowable_partial_perm B)
  (h₁ : ρ ≤ σ) (h₂ : σ ≤ τ) : ρ ≤ τ :=
begin
  obtain ⟨hsub, hflex, hatom⟩ := h₁,
  obtain ⟨hsub', hflex', hatom'⟩ := h₂,
  refine ⟨hsub.trans hsub', λ L N A hLA hnin hin, _, λ a b L hab A hnin hin, _⟩,
  { by_cases (sum.inr (L.to_near_litter, N), A) ∈ σ.val,
    { obtain ⟨h1, h2⟩ := hflex L N A hLA hnin h,
      split; intros L' A' hLA'; specialize h1 L' A' hLA'; specialize h2 L' A' hLA',
      { exact set.image_subset binary_condition.domain hsub' h1 },
      { exact set.image_subset binary_condition.range hsub' h2 } },
    { exact hflex' L N A hLA h hin } },
  { by_cases (sum.inl (a, b), A) ∈ σ.val,
    { intros c hc,
      obtain ⟨d, hd⟩ := hatom a b L hab A hnin h c hc,
      refine ⟨d, hsub' hd⟩ },
    { exact hatom' a b L hab A h hin } }
end

instance preorder : preorder (allowable_partial_perm B) := {
  le := perm_le B,
  le_refl := extends_refl B,
  le_trans := extends_trans B,
}

section zorn_setup

/-! To set up for Zorn's lemma, we need to show that the union of all allowable partial permutations
in a chain is an upper bound for the chain. In particular, we first show that it is allowable, and
then we show it extends all elements in the chain.

Non-trivial bit: the "small or all" conditions — these are enforced by the "if adding any, add all"
parts of the definition of ≤. -/

variables (c : set (allowable_partial_perm B))

lemma domain_closed_Union (hc : is_chain (≤) c) :
  unary_spec.support_closed (spec.domain ⋃₀ (subtype.val '' c)) := sorry

lemma range_closed_Union (hc : is_chain (≤) c) :
  unary_spec.support_closed (spec.range ⋃₀ (subtype.val '' c)) := sorry

lemma one_to_one_Union (hc : is_chain (≤) c) :
  spec.one_to_one ⋃₀ (subtype.val '' c) := sorry

lemma atom_cond_Union (hc : is_chain (≤) c) :
  ∀ L A, spec.atom_cond (⋃₀ (subtype.val '' c)) L A := sorry

lemma near_litter_cond_Union (hc : is_chain (≤) c) :
  ∀ N A, spec.near_litter_cond (⋃₀ (subtype.val '' c)) N A := sorry

lemma flexible_cond_Union (hc : is_chain (≤) c) :
  spec.flexible_cond ⋃₀ (subtype.val '' c) := sorry

-- Note: the non-flexible conditions can't be worked on yet, until allowable.lean compiles.

lemma non_flexible_cond_Union (hc : is_chain (≤) c) :
  spec.non_flexible_cond ⋃₀ (subtype.val '' c) := sorry

lemma inv_non_flexible_cond_Union (hc : is_chain (≤) c) :
  spec.non_flexible_cond (⋃₀ (subtype.val '' c))⁻¹ := sorry

variables (hc : is_chain (≤) c)

/-- The union of a chain of allowable partial permutations is allowable. -/
lemma allowable_Union :
  spec.allowable_spec B ⋃₀ (subtype.val '' c) := {
  domain_closed := domain_closed_Union B c hc,
  range_closed := range_closed_Union B c hc,
  one_to_one := one_to_one_Union B c hc,
  atom_cond := atom_cond_Union B c hc,
  near_litter_cond := near_litter_cond_Union B c hc,
  flexible_cond := flexible_cond_Union B c hc,
  non_flexible_cond := non_flexible_cond_Union B c hc,
  inv_non_flexible_cond := inv_non_flexible_cond_Union B c hc,
}

lemma mem_perm_le (σ : allowable_partial_perm B) (hσ : c ⊆ {ρ | σ ≤ ρ}) :
  σ ≤ ⟨⋃₀ (subtype.val '' c), allowable_Union B c hc⟩ := sorry

lemma maximal_Union (σ : allowable_partial_perm B) (hσ : c ⊆ {ρ | σ ≤ ρ}) :
  ∀ z ∈ c, z ≤ ⟨⋃₀ (subtype.val '' c), allowable_Union B c hc⟩ := sorry

end zorn_setup

/-- There is a maximal allowable partial permutation extending any given allowable partial
permutation. This result is due to Zorn's lemma. -/
lemma maximal_perm (σ : allowable_partial_perm B) :
  ∃ (ρ : allowable_partial_perm B) (h : σ ≤ ρ), ∀ τ (hτ₁ : σ ≤ τ) (hτ₂ : ρ ≤ τ), τ ≤ ρ :=
zorn_preorder₀ _ (λ c hc₁ hc₂,
  ⟨⟨⋃₀ (subtype.val '' c), allowable_Union B c hc₂⟩,
    mem_perm_le _ _ _ _ hc₁,
    maximal_Union _ _ _ σ hc₁⟩)

end allowable_partial_perm

end con_nf
