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
lemma struct_perm.to_spec_injective (α : type_index) : injective (@struct_perm.to_spec _ α) :=
begin
  unfold injective,
  intros σ τ heq,
  unfold struct_perm.to_spec at heq,
  sorry, -- lemmas which require derivatives can't be fully unsorried right now (I think)
end

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
have : (derivative (A.comp x_snd)) π= (derivative x_snd) ((derivative A) π),
{
  sorry, -- problem with derivative def
},
rw this,
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
  (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ) (A : path (B : type_index) β)
  (t : tangle_path ((lt_index.mk' hγ (path.comp B.path A)) : le_index α)),
L ≠ (f_map_path hγ hδ t)

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
  exact h (congr_arg sigma.fst hLN)
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
In a present litter, we can specify either `< κ`-many atoms, or all of the atoms in the litter, and
in this case, almost all of them must be mapped to the right place.
Note that the `small` constructor does not depend on whether the litter is present or absent. -/
@[mk_iff] inductive atom_cond (σ : spec B) (L : litter) (A : extended_index B) : Prop
| small : small {a ∈ litter_set L | (⟨sum.inl a, A⟩ : support_condition B) ∈ σ.domain} → atom_cond
| all (N : near_litter) (atom_map : litter_set L → atom) :
    (⟨sum.inr ⟨L.to_near_litter, N⟩, A⟩ : binary_condition B) ∈ σ →
    (∀ a ∈ litter_set L, (⟨sum.inl ⟨a, atom_map ⟨a, ‹_›⟩⟩, A⟩ : binary_condition B) ∈ σ) →
    N.snd.val = set.range atom_map →
    atom_cond

/-- The allowability condition on near-litters.
If a near-litter is present, so are its litter and all atoms in the symmetric difference, and it is
mapped to the right place. -/
def near_litter_cond (σ : spec B) (N₁ N₂ : near_litter) (A : extended_index B) : Prop :=
(⟨sum.inr ⟨N₁, N₂⟩, A⟩ : binary_condition B) ∈ σ →
  ∃ M, (⟨sum.inr ⟨N₁.fst.to_near_litter, M⟩, A⟩ : binary_condition B) ∈ σ ∧
  ∃ (symm_diff : litter_set N₁.fst ∆ N₁.snd → atom),
    (∀ a : litter_set N₁.fst ∆ N₁.snd, (⟨sum.inl ⟨a, symm_diff a⟩, A⟩ : binary_condition B) ∈ σ) ∧
  N₂.snd.val = M.snd.val ∆ set.range symm_diff

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
(flexible_cond : σ.flexible_cond B)

end spec

variable (B)

namespace spec

/-- The inverse of an allowable specification is allowable. -/
lemma inv_allowable (σ : spec B) (hσ : σ.allowable_spec B) :
  σ⁻¹.allowable_spec B := {
  forward := hσ.backward,
  backward := by { rw inv_inv, exact hσ.forward },
  flexible_cond := begin
    obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := hσ.flexible_cond,
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

lemma allowable_partial_perm.inv_def (σ : allowable_partial_perm B) :
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
  obtain hsmall | ⟨N, atom_map, h1, h2, h3⟩ := hσ.forward.atom_cond L (A.comp C),
  { refine spec.atom_cond.small _,
    convert hsmall,
    unfold spec.domain binary_condition.domain,
    ext a,
    simp,
    split; rintro ⟨⟨x, y⟩, hx1, hx2, hx3⟩,
    { exact ⟨⟨x, A.comp y⟩, hx1, hx2, by rw ← hx3⟩ },
    dsimp only at hx3,
    rw hx3 at hx1 hx2,
    exact ⟨⟨x, C⟩, hx1, hx2, rfl⟩ },
  { exact spec.atom_cond.all N atom_map h1 h2 h3 }
end

lemma lower_near_litter_cond (hσ : σ.allowable_spec B) :
  ∀ N₁ N₂ C, (σ.lower A).near_litter_cond (le_index.mk β (path.comp B.path A)) N₁ N₂ C :=
λ N₁ N₂ C hN, hσ.forward.near_litter_cond N₁ N₂ (A.comp C) hN

lemma flexible_descends (he : extended_index (⟨β, B.path.comp A⟩ : le_index α)) (L : litter) :
flexible L he → flexible L (A.comp he) :=
begin
  intro hf,
  --have hs := unconstrained_of_flexible L he hf,
  unfold flexible at hf ⊢,
  simp,
  intros hb hd hg hgb hdb hdg hp htp heq,
  rw heq at hf,
  simp at hf,
  have h' := hf hgb hdb hdg,
  --LEMMA IS FALSE?
  sorry,
end

/-- Descending down a proper path `A`, `μ`-many litters become flexible. -/
lemma lower_flexible_co_large (hβ : (B : type_index) ≠ β) :
  #{L : litter // ∃ (C : extended_index (⟨β, B.path.comp A⟩ : le_index α)),
    flexible L C ∧ ¬ flexible L (A.comp C : extended_index B)} = #μ := sorry

/-- Using the previous lemma, at each lower level `A`, we have either `μ`-many flexible litters not
in the domain, or none at all (so the domain contains all flexible litters).
TODO: Is this actually true? -/
lemma lower_flexible_dichotomy
  (hdom : #μ = #{L : litter | ∃ (C : extended_index B),
    flexible L C ∧ (⟨sum.inr L.to_near_litter, C⟩ : support_condition B) ∉ σ.domain})
  (hβ : (B : type_index) ≠ β) :
  #{L : litter | ∃ (C : extended_index (⟨β, B.path.comp A⟩ : le_index α)),
    flexible L C ∧ (sum.inr L.to_near_litter, C) ∉ (σ.lower A).domain} = #μ ∨
  {L : litter | ∃ (C : extended_index (⟨β, B.path.comp A⟩ : le_index α)),
    flexible L C ∧ (sum.inr L.to_near_litter, C) ∉ (σ.lower A).domain} = ∅ := sorry

lemma lower_flexible_cond (hσ : σ.allowable_spec B) :
  (σ.lower A).flexible_cond (le_index.mk β (path.comp B.path A)) :=
begin
  obtain ⟨hdom, hrge⟩ | ⟨hdom, hrge⟩ := hσ.flexible_cond,
  { by_cases hβ : (B : type_index) = β,
    { obtain ⟨B_index, B⟩ := B,
      dsimp only [le_index_coe_def] at *,
      subst hβ,
      rw [path_nil A, spec.lower_nil σ],
      exact spec.flexible_cond.co_large hdom hrge,
      /- { rw hdom, refine cardinal.mk_subtype_mono _,
        intro L,
        intro h',
        cases h' with he hf',
        obtain ⟨hf,hin⟩ := hf',
        refine ⟨A.comp he,_⟩,
        split,
        {
          exact flexible_descends _ _ _ L hf,
        },
        { unfold spec.domain at hin ⊢,
          unfold binary_condition.domain at hin ⊢,
          simp at hin ⊢,
          intros hb h1 h2,
          have hin' := hin ⟨hb.fst,he⟩,
          dsimp at hin',
          rw h2 at hin',
          simp at hin',
          intro heq,
          refine hin' _,
          unfold spec.lower,
          unfold binary_condition.extend_path,
          obtain ⟨As|Ns,he'⟩ := hb; dsimp at heq; rw heq; rw heq at h1; dsimp; exact h1,
        }, }, -/
    },
    { -- Postponing until we have proven `lower_flexible_co_large`.
      sorry },
  },
  { refine spec.flexible_cond.all _ _,
    { intros L he hf,
      have hdom' := hdom L (A.comp he) _,
      { unfold spec.lower,
        unfold binary_condition.extend_path,
        unfold spec.domain at hdom' ⊢,
        dsimp at hdom' ⊢,
        obtain ⟨x, hx_1, hx_2⟩ := hdom',
        refine ⟨⟨x.fst, he⟩,_,_⟩,
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
        exact flexible_descends _ _ _ L hf,
      },
    },
    { intros L he hf,
      have hrge' := hrge L (A.comp he) _,
      { unfold spec.lower,
        unfold binary_condition.extend_path,
        unfold spec.range at hrge' ⊢,
        dsimp at hrge' ⊢,
        obtain ⟨x, hx_1, hx_2⟩ := hrge',
        refine ⟨⟨x.fst, he⟩,_,_⟩,
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
      exact flexible_descends _ _ _ L hf,
      },
    }
  },
end

-- Note: the non-flexible conditions can't be worked on yet, until allowable.lean compiles.

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
* if `ρ` has any new flexible litter, then it has all (in both domain and range);
* within each litter, if `ρ.domain` has any new atom, then it must have all
    atoms in that litter (and hence must also have the litter), and dually for the range.

Note that the second condition is exactly the condition in `spec.flexible_cond.all`.
-/
structure perm_le (σ ρ : allowable_partial_perm B) : Prop :=
(subset : σ.val ⊆ ρ.val)
(all_flex_domain (L : litter) (N : near_litter) (A : extended_index B) (hL : flexible L A)
  (hσ : (⟨sum.inr ⟨L.to_near_litter, N⟩, A⟩ : binary_condition B) ∉ σ.val)
  (hρ : (⟨sum.inr ⟨L.to_near_litter, N⟩, A⟩ : binary_condition B) ∈ ρ.val) :
  (∀ L' A', flexible L' A' →
    (⟨sum.inr L'.to_near_litter, A'⟩ : support_condition B) ∈ ρ.val.domain ∧
    (⟨sum.inr L'.to_near_litter, A'⟩ : support_condition B) ∈ ρ.val.range))
(all_flex_range (L : litter) (N : near_litter) (A : extended_index B) (hL : flexible L A)
  (hσ : (⟨sum.inr ⟨N, L.to_near_litter⟩, A⟩ : binary_condition B) ∉ σ.val)
  (hρ : (⟨sum.inr ⟨N, L.to_near_litter⟩, A⟩ : binary_condition B) ∈ ρ.val) :
  (∀ L' A', flexible L' A' →
    (⟨sum.inr L'.to_near_litter, A'⟩ : support_condition B) ∈ ρ.val.domain ∧
    (⟨sum.inr L'.to_near_litter, A'⟩ : support_condition B) ∈ ρ.val.range))
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
    { exact λ l a hla,
        ⟨set.image_subset binary_condition.domain hsub' (hflx_domain L N A hLA hnin h l a hla).1,
        set.image_subset binary_condition.range hsub' (hflx_domain L N A hLA hnin h l a hla).2⟩ },
    { exact hflx_domain' L N A hLA h hin } },
  { by_cases (sum.inr (N, L.to_near_litter), A) ∈ σ.val,
    { exact λ l a hla,
        ⟨set.image_subset binary_condition.domain hsub' (hflx_range L N A hLA hnin h l a hla).1,
        set.image_subset binary_condition.range hsub' (hflx_range L N A hLA hnin h l a hla).2⟩ },
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
          λ L N A hLA hnin hin L' A' hLA', _,
          λ L N A hLA hnin hin L' A' hLA', _,
          λ a b, h5 b a, λ a b, h4 b a⟩,
  { rw [this, spec.inv_domain, spec.inv_range],
    exact and.comm.1 (h3 L N A hLA hnin hin L' A' hLA') },
  { rw [this, spec.inv_domain, spec.inv_range],
    exact and.comm.1 (h2 L N A hLA hnin hin L' A' hLA') }
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
  /- sorries are here but will work on them tomorrow - not waiting on anything and no big problems,
     just not finished yet! -/
  intros L A,
  by_cases (∀ σ ∈ c, ∀ ρ ∈ c, ∀ a ∈ litter_set L,
      (⟨sum.inl a, A⟩ : support_condition B) ∈ σ.val.domain →
      (⟨sum.inl a, A⟩ : support_condition B) ∈ ρ.val.domain),
  { rcases set.eq_empty_or_nonempty c with hemp | ⟨⟨σ, hσ₁⟩, hσ₂⟩,
    { rw hemp,
      refine spec.atom_cond.small _,
      simp, },
    { cases hσ₁.forward.atom_cond L A with h₁ h₂,
      { refine spec.atom_cond.small _,
        convert h₁,
        refine funext (λ a, _),
        rw ← spec.sUnion_domain_eq_domain_sUnion,
        sorry, },
      { sorry, }, }, },
  { push_neg at h,
    sorry, },
end

lemma near_litter_cond_Union (hc : is_chain (≤) c) :
  ∀ N₁ N₂ A, spec.near_litter_cond B (⋃₀ (subtype.val '' c)) N₁ N₂ A :=
begin
  rintros N₁ N₂ A ⟨ρ, ⟨σ, hσ, hσρ⟩, hρ⟩,
  subst hσρ,
  have : σ.val ⊆ ⋃₀ (subtype.val '' c) := λ x h, ⟨σ, ⟨σ, hσ, rfl⟩, h⟩,
  obtain ⟨M, hM, symm_diff, h1, h2⟩ := σ.prop.forward.near_litter_cond N₁ N₂ A hρ,
  exact ⟨M, this hM, symm_diff, λ a, this (h1 a), h2⟩,
end

lemma flexible_cond_Union (hc : is_chain (≤) c) :
  spec.flexible_cond B ⋃₀ (subtype.val '' c) := sorry

-- Note: the non-flexible conditions can't be worked on yet, until allowable.lean compiles.

lemma non_flexible_cond_Union (hc : is_chain (≤) c) :
  spec.non_flexible_cond B ⋃₀ (subtype.val '' c) := sorry

lemma domain_closed_Union (hc : is_chain (≤) c) :
  unary_spec.support_closed B (spec.domain ⋃₀ (subtype.val '' c)) := sorry

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
    exact λ l a hla, ⟨
      set.image_subset binary_condition.domain (hsub σ hσ) (this l a hla).1,
      set.image_subset binary_condition.range (hsub σ hσ) (this l a hla).2⟩ },
  { have := hleq.3 L N A hLA hnin hρ,
    exact λ l a hla, ⟨
      set.image_subset binary_condition.domain (hsub σ hσ) (this l a hla).1,
      set.image_subset binary_condition.range (hsub σ hσ) (this l a hla).2⟩ },
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

end values

/-! The next few lemmas are discussed in "FoA proof sketch completion". -/

-- TODO: Generalise and improve the naming of the following lemmas.

section exists_ge_atom

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
    have := σ.property.forward.atom_cond a.fst A,
    -- The definition of atom_cond needs to be fixed.
    sorry },
  { exact ⟨_, atom_value_spec B σ A c c.property.right, rfl⟩, },
  { obtain ⟨hc, ⟨⟨⟨a₁, a₂⟩ | Ns, C⟩, hd₁, hd₂⟩⟩ := hc,
    { cases hd₂,
      refine ⟨⟨a₁, _, ⟨_, hd₁, rfl⟩⟩, (σ.property.backward.one_to_one A).atom a₁
        (atom_value_spec B σ A a₁ ⟨_, hd₁, rfl⟩) hd₁⟩,
      -- Again, I think this needs atom_cond.
      sorry, },
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
    { simp only [atom_to_cond, atom_map, subtype.coe_mk, prod.mk.inj_iff] at hy,
      obtain ⟨⟨h1, h2⟩, h3⟩ := hy,
      subst h1, subst h2, subst h3,
      -- seek contradiction: p = y -> false:
      -- have : (sum.inl p, A) ∈ σ.val.domain := ⟨_, hp, by simp only [binary_condition.domain, sum.elim_inl]⟩,
      sorry },
    { sorry },
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
sorry

lemma atom_union_atom_cond_backward (hc : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (hsmall : small {a ∈ litter_set a.fst | (sum.inl a, A) ∈ σ.val.domain})
  (ha : (sum.inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  ∀ L C, spec.atom_cond B (σ.val ∪ set.range (atom_to_cond B σ a A N hsmall ha))⁻¹ L C :=
sorry

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
  spec.flexible_cond B (σ.val ∪ set.range (atom_to_cond B σ a A N hsmall ha)) :=
begin
  obtain (⟨hdom, hrge⟩ | ⟨hdom, hrge⟩) := σ.property.flexible_cond,
  { refine spec.flexible_cond.co_large _ _,
    { convert hdom, ext L, split,
      { rintro ⟨C, hC₁, hC₂⟩, rw spec.domain_union at hC₂,
        exact ⟨C, hC₁, λ h, hC₂ (set.mem_union_left _ h)⟩, },
      { rintro ⟨C, hC₁, hC₂⟩, refine ⟨C, hC₁, λ h, _⟩,
        rw spec.domain_union at h,
        cases h,
        { exact hC₂ h, },
        { obtain ⟨d, ⟨e, hd₁⟩, hd₂⟩ := h, cases hd₁, cases hd₂, } } },
    { convert hrge, ext L, split,
      { rintro ⟨C, hC₁, hC₂⟩, rw spec.range_union at hC₂,
        exact ⟨C, hC₁, λ h, hC₂ (set.mem_union_left _ h)⟩, },
      { rintro ⟨C, hC₁, hC₂⟩, refine ⟨C, hC₁, λ h, _⟩,
        rw spec.range_union at h,
        cases h,
        { exact hC₂ h, },
        { obtain ⟨d, ⟨e, hd₁⟩, hd₂⟩ := h, cases hd₁, cases hd₂, } } } },
  { refine spec.flexible_cond.all _ _,
    { intros L C hL, rw spec.domain_union, exact or.inl (hdom L C hL), },
    { intros L C hL, rw spec.range_union, exact or.inl (hrge L C hL), } },
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

/-- The image of an element of a near-litter lies in the resulting near-litter.
TODO: Update the atom condition as required. -/
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
  obtain hsmall | ⟨M', a_map, hall₁, hall₂, hall₃⟩ :=
    atom_union_atom_cond_forward B σ a A N hc hsmall ha a.fst A,
  { -- I think we need to change the atom condition, since it was originally defined in terms
    -- of rough images. We need that in any case, the atoms are mapped inside the
    -- image of the near-litter.
    sorry },
  { obtain this | ⟨e, he⟩ := hall₂ d d.property.left,
    { exfalso, exact d.property.right ⟨_, this, rfl⟩, },
    rw (atom_to_cond_eq B σ a A N hsmall ha hd he).left,
    suffices : N = M',
    { rw this, exact ((set.range_eq_iff _ _).mp hall₃.symm).left _, },
    exact (atom_union_one_to_one_backward B σ a A N hc hsmall ha A).near_litter
      a.fst.to_near_litter (or.inl hc) hall₁, }
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
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain) : (sum.inr (N, near_litter_image B σ N A hN hNL ha), A) ∈ σ.val :=
begin
  unfold near_litter_image,
  obtain ⟨⟨_ | ⟨N, N'⟩, C⟩, hN', heq⟩ := hNin, { cases heq },
  simp only [binary_condition.domain, sum.elim_inr, prod.mk.inj_iff] at heq,
  obtain ⟨h1, h2⟩ := heq, subst h1, subst h2,
  obtain ⟨⟨_ | ⟨L, M⟩, A⟩, hL, heq⟩ := hNL, { cases heq },
  simp only [binary_condition.domain, sum.elim_inr, prod.mk.inj_iff] at heq,
  obtain ⟨h1, h2⟩ := heq, subst h1, subst h2,
  obtain ⟨M', hM, symm, hsy, hsd⟩ := σ.prop.forward.near_litter_cond N N' A hN',
  have := (σ.prop.backward.one_to_one A).near_litter _ hL hM,
  subst this,
  have : ∀ a : {a // a ∈ litter_set N.fst ∆ (N.snd : set atom)}, symm a = atom_value B σ A a ⟨_, hsy a, rfl⟩ := λ b, (σ.prop.backward.one_to_one A).atom _ (hsy b) (atom_value_spec B σ A b ⟨_, hsy b, rfl⟩),
  have that := congr_arg set.range (funext this),
  convert hN', clear hN',
  obtain ⟨N', atoms, hN'⟩ := N',
  dsimp only at hsd, subst hsd,
  have : (near_litter_value B σ A N.fst.to_near_litter ⟨_, hL, heq⟩).fst = N',
  { sorry },
  subst this,
  rw sigma.mk.inj_iff, split, refl, refine heq_of_eq _,
  rw subtype.mk_eq_mk, refine congr_arg2 _ _ that.symm,
  sorry
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
      -- have := (σ.prop.backward.one_to_one C).near_litter _ hQ (near_litter_value_spec B σ C Q ⟨_, hQ, rfl⟩),
      -- simp at this,
      obtain ⟨M, hM⟩ := σ.prop.forward.near_litter_cond _ _ C hQ,
      simp [near_litter_image] at hM,

      sorry },
    { sorry },
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
sorry

lemma near_litter_union_atom_cond_backward (hN : litter_set N.fst ≠ N.snd)
  (hNL : (sum.inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain) :
  ∀ L C, spec.atom_cond B (σ.val ∪ {(sum.inr (N, near_litter_image B σ N A hN hNL ha), A)})⁻¹ L C :=
sorry

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
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain) :
  spec.flexible_cond B (σ.val ∪ {(sum.inr (N, near_litter_image B σ N A hN hNL ha), A)}) :=
sorry

lemma near_litter_union_allowable (hN : litter_set N.fst ≠ N.snd)
  (hNL : (sum.inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain) :
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
  flexible_cond := near_litter_union_flexible_cond B σ N A hN hNL ha,
}

/-- We take the additional hypothesis that the near-litter that we're mapping do does not happen
to be a flexible litter. This will always be true, but it is convenient to assume at this point. -/
lemma le_near_litter_union (hN : litter_set N.fst ≠ N.snd)
  (hNL : (sum.inr N.fst.to_near_litter, A) ∈ σ.val.domain)
  (ha : ∀ (a : atom), a ∈ litter_set N.fst ∆ ↑(N.snd) → (sum.inl a, A) ∈ σ.val.domain)
  (image_not_flexible :
    ∀ L, litter_set L = (near_litter_image B σ N A hN hNL ha).snd.val → ¬ flexible L A) :
  σ ≤ ⟨σ.val ∪ {(sum.inr (N, near_litter_image B σ N A hN hNL ha), A)},
    near_litter_union_allowable B σ N A hN hNL ha⟩ := {
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
    sorry,
  end,
  all_atoms_range := begin
    intros b₁ b₂ L hb₁ C hC₁ hC₂ c hc',
    cases hC₂,
    { exfalso, exact hC₁ hC₂, },
    sorry,
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
    sorry }
end

end exists_ge_near_litter

/-- Nothing constrains a flexible litter, so we don't have any hypothesis about the fact that all
things that constrain it lie in `σ` already. -/
lemma exists_ge_flexible (σ : allowable_partial_perm B) (L : litter) (A : extended_index B)
  (hL : flexible L A) :
  ∃ ρ ≥ σ, (⟨sum.inr L.to_near_litter, A⟩ : support_condition B) ∈ ρ.val.domain :=
sorry

lemma exists_ge_non_flexible (σ : allowable_partial_perm B) (L : litter) (A : extended_index B)
  ⦃β : Λ⦄ ⦃γ : type_index⦄ ⦃δ : Λ⦄ (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
  (C : path (B : type_index) β)
  (t : tangle_path ((lt_index.mk' hγ (path.comp B.path C)) : le_index α))
  (hL : L = (f_map_path hγ hδ t))
  (hσ : ∀ c, c ≺ (⟨sum.inr L.to_near_litter, A⟩ : support_condition B) → c ∈ σ.val.domain) :
  ∃ ρ ≥ σ, (⟨sum.inr L.to_near_litter, A⟩ : support_condition B) ∈ ρ.val.domain :=
sorry

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
        obtain ⟨ρ, hρ₁, hρ₂⟩ := exists_ge_flexible B σ L A h,
        rw hσ ρ hρ₁ at hρ₂,
        exact hρ₂, },
      { -- This litter is non-flexible.
        unfold flexible at h,
        push_neg at h,
        obtain ⟨β, δ, γ, hγ, hδ, hγδ, C, t, hL⟩ := h,
        obtain ⟨ρ, hρ₁, hρ₂⟩ := exists_ge_non_flexible B σ L A hγ hδ hγδ C t hL hind,
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
