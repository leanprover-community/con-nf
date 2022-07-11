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

open function quiver with_bot

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
lemma struct_perm.satisfies_to_spec {α : Λ} (π : struct_perm α) : π.satisfies π.to_spec :=
begin
  unfold struct_perm.satisfies struct_perm.to_spec struct_perm.satisfies_cond,
  rintros ⟨⟨x, y⟩ | ⟨x, y⟩, A⟩ ⟨⟨a, b⟩, ha⟩; simp only [prod.mk.inj_iff] at ha,
  { simp,
    rw [← ha.2, ← ha.1.1], exact ha.1.2 },
  cases ha.1
end

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

/-- Lowering along the empty path does nothing. -/
lemma unary_spec.lower_nil {α β γ : Λ} (σ : unary_spec α) :
  σ.lower path.nil = σ :=
begin
  unfold unary_spec.lower support_condition.extend_path,
  simp,
end

/-- The lowering map is functorial. -/
lemma unary_spec.lower_lower {α β γ : Λ} (σ : unary_spec α)
  (A : path (α : type_index) β) (B : path (β : type_index) γ) :
  (σ.lower A).lower B = σ.lower (path.comp A B) :=
begin
  unfold unary_spec.lower support_condition.extend_path,
  simp,
end

/-- We can lower a specification to a lower proper type index with respect to a path
`A : α ⟶ β` by only keeping binary conditions whose paths begin with `A`. -/
def spec.lower {α β : Λ} (σ : spec α) (A : path (α : type_index) β) : spec β :=
{c | c.extend_path A ∈ σ}

/-- Lowering along the empty path does nothing. -/
lemma spec.lower_nil {α β γ : Λ} (σ : spec α) :
  σ.lower path.nil = σ :=
begin
  unfold spec.lower binary_condition.extend_path,
  simp,
end

/-- The lowering map is functorial. -/
lemma spec.lower_lower {α β γ : Λ} (σ : spec α)
  (A : path (α : type_index) β) (B : path (β : type_index) γ) :
  (σ.lower A).lower B = σ.lower (path.comp A B) :=
begin
  unfold spec.lower binary_condition.extend_path,
  simp,
end

variables (α : Λ) [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [phase_2_assumptions α]

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
@[mk_iff] inductive constrains : support_condition α → support_condition α → Prop
| mem_litter (L : litter) (a ∈ litter_set L) (A : extended_index α) :
    constrains ⟨sum.inr L.to_near_litter, A⟩ ⟨sum.inl a, A⟩
| near_litter (N : near_litter) (hN : litter_set N.fst ≠ N.snd) (A : extended_index α) :
    constrains ⟨sum.inr N.fst.to_near_litter, A⟩ ⟨sum.inr N, A⟩
| symm_diff (N : near_litter) (a ∈ litter_set N.fst ∆ N.snd) (A : extended_index α) :
    constrains ⟨sum.inl a, A⟩ ⟨sum.inr N, A⟩
| f_map {β δ : Λ} {γ : type_index} (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
    (A : path (α : type_index) β) (t : tangle_path ((lt_index.mk' hγ A) : le_index α))
    (c ∈ (designated_support_path t).carrier) :
    constrains
      ⟨c.fst, path.comp (path.cons A hγ) c.snd⟩
      ⟨sum.inr (f_map_path
        (proper_lt_index.mk' (hδ.trans_le (coe_le_coe.mp $ le_of_path A)) path.nil) t)
        .to_near_litter, path.cons (path.cons A (coe_lt_coe.mpr hδ)) (bot_lt_coe _)⟩

/-! We declare new notation for the "constrains" relation on support conditions. -/
local infix ` ≺ `:50 := constrains _

/-- The `≺` relation is well-founded. By the conditions on orderings, if we have `⟨x, A⟩ ≺ ⟨y, B⟩`,
then `x < y` in `µ`, under the `to_tangle_path` or `typed_singleton_path` maps. -/
lemma constrains_wf : well_founded (constrains α) := sorry

variable {α}

/-- A litter and extended index is *flexible* if the associated support condition is a minimal
element with respect to the relation `≺`. In other words, it is not constrained by anything. -/
def flexible (L : litter) (A : extended_index α) : Prop := ∀ c, ¬ c ≺ ⟨sum.inr L.to_near_litter, A⟩

/-- A litter and extended index is flexible iff it is not of the form `f_{γ,δ}^A(x)` for some
`x ∈ τ_{γ:A}` with conditions defined as above. -/
lemma flexible_iff (L : litter) (A : extended_index α) :
flexible L A ↔ ∀ {β δ : Λ} {γ : type_index} (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
    (A : path (α : type_index) β) (t : tangle_path ((lt_index.mk' hγ A) : le_index α)),
L ≠ (f_map_path (proper_lt_index.mk' (hδ.trans_le (coe_le_coe.mp $ le_of_path A)) path.nil) t) :=
sorry

/- def support_closed (σ : unary_spec α) : Prop :=
∀ {β γ δ : Λ} (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ) (A : path (α : type_index) β)
  (t : tangle_path ((proper_lt_index.mk' hγ A) : le_index α)),
  (⟨sum.inr (f_map_path
    (proper_lt_index.mk' (hδ.trans_le (coe_le_coe.mp $ le_of_path A)) path.nil) t)
    .to_near_litter, path.cons (path.cons A (coe_lt_coe.mpr hδ)) (bot_lt_coe _)⟩ :
      support_condition α) ∈ σ → _ -/

end con_nf
