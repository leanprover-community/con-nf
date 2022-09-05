import phase2.basic
import phase2.freedom_of_action.spec

/-!
# Allowability

We say that a specification is *allowable* (`allowable`) if it satisfies a collection of
relatively permissive conditions. Essentially, we need to ensure that there are no obvious local
contradictions in the specification. For example, the one-to-one condition requires that if we
specify `π_A(a) = b`, we cannot also specify `π_A(a) = c` for some `c ≠ b`, and we cannot specify
`π_A(d) = b` for `d ≠ a` either.

More details on these conditions are discussed in depth later.

If a specification is allowable, we call it an *allowable partial permutation*
(`allowable_spec`).
-/

open quiver set sum with_bot
open_locale cardinal

universe u

namespace con_nf
variables [params.{u}]

open struct_perm

variables {α : Λ} [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [typed_positions.{}] [phase_2_assumptions α] {B : le_index α}

/-- A litter and extended index is *flexible* if it is not of the form `f_{γ,δ}^A(x)` for some
`x ∈ τ_{γ:A}` with conditions defined as above. Hence, it is not constrained by anything. -/
def flex (L : litter) (A : extended_index B) : Prop :=
∀ ⦃β : Λ⦄ ⦃γ : type_index⦄ ⦃δ : Λ⦄
  (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
  (C : path (B : type_index) β) (hC : A = (C.cons $ coe_lt_coe.mpr hδ).cons (bot_lt_coe _))
  (t : tangle_path ((lt_index.mk' hγ (B.path.comp C)) : le_index α)),
    L ≠ f_map_path hγ hδ t

/-- There are `μ`-many `A`-flexible litters for each extended index `A`. In fact, we can do better
than this - for each proper path `C` from some `β` to `B`, there are `μ`-many `C.comp A`-flexible
litters that are not `A`-flexible. However, at the moment, we don't need this fact. -/
@[simp] lemma mk_flex_litters (A : extended_index B) : #{L : litter // flex L A} = #μ :=
begin
  by_cases (B : type_index) = ⊥,
  { have H : ∀ L, flex L A,
    { intros L β γ δ hγ hδ hγδ C,
      have hγB := lt_of_lt_of_le hγ (le_of_path C),
      rw h at hγB,
      cases not_lt_bot hγB },
    rw ← mk_litter,
    rw cardinal.eq,
    exact ⟨⟨subtype.val, (λ L, ⟨L, H L⟩), (λ S, subtype.eta _ _), (λ L, rfl)⟩⟩ },
  refine le_antisymm _ _,
  { rw ← mk_litter,
    exact cardinal.mk_subtype_le _ },
  { rw cardinal.le_def,
    rw ← ne.def at h,
    rw with_bot.ne_bot_iff_exists at h,
    obtain ⟨B', hB'⟩ := h,
    refine ⟨⟨λ x, ⟨⟨⟨⊥, B'⟩, x⟩, λ β γ δ hγ hδ hγδ C hC t, _⟩, _⟩⟩,
    { intro h,
      unfold f_map_path at h,
      have := f_map_fst (proper_lt_index.mk' hδ (B.path.comp C)).index t,
      rw ← h at this,
      simp only [prod.mk.inj_iff] at this,
      cases this.2,
      refine not_lt_of_ge (le_of_path C) _,
      rw ← hB', exact coe_lt_coe.mpr hδ, },
    { intros x y h, cases h, refl, } }
end
local attribute [irreducible] litter

namespace unary_spec
variables (B)

/-- A unary specification is *support-closed* if whenever `⟨f_{γ,δ}^A(x), A⟩ ∈ σ`, `S_{γ:A}`
supports `x`. -/
def support_closed (σ : unary_spec B) : Prop :=
∀ ⦃β : Λ⦄ ⦃γ : type_index⦄ ⦃δ : Λ⦄ (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ)
    (A : path (B : type_index) β)
    (t : tangle_path (lt_index.mk' hγ (B.path.comp A) : le_index α)),
  (⟨inr (f_map_path hγ hδ t).to_near_litter, (A.cons $ coe_lt_coe.mpr hδ).cons $ bot_lt_coe _⟩
      : support_condition B) ∈ σ →
      supports (allowable_path (lt_index.mk' hγ (B.path.comp A) : le_index α))
        (σ.lower (A.cons hγ)) t

end unary_spec

namespace spec
variables {β : type_index}

/-!
We now set out the allowability conditions for specifications of permutations.
These are collected in the structure `allowable`, which may be treated as a proposition.
We say a specification is allowable if `allowable` holds.
-/

/--
A specification is *one-to-one* on a particular path `A` if
* `⟨a, b₁⟩, ⟨a, b₂⟩ ∈ σ` implies `b₁ = b₂`,
* `⟨a₁, b⟩, ⟨a₂, b⟩ ∈ σ` implies `a₁ = a₂`,
where `a, b` may be either atoms or near-litters.
-/
@[mk_iff] structure one_to_one_forward_path (σ : spec β) (A : extended_index β) : Prop :=
(atom        : ∀ b, {a | (⟨inl ⟨a, b⟩, A⟩ : binary_condition β) ∈ σ}.subsingleton)
(near_litter : ∀ N, {M | (⟨inr ⟨M, N⟩, A⟩ : binary_condition β) ∈ σ}.subsingleton)

/-- A specification is one-to-one if it is one-to-one on all paths. -/
def one_to_one_forward (σ : spec β) : Prop := ∀ A, σ.one_to_one_forward_path A

/-- If we lower a one-to-one specification along a path, it is still one-to-one.
This is one part of `total-1-1-restriction` in the blueprint. -/
lemma lower_one_to_one {β : type_index} (σ : spec B) (A : path (B : type_index) β) :
  σ.one_to_one_forward → (σ.lower A).one_to_one_forward :=
begin
  refine (λ ho he, ⟨_, _⟩); intros hz ha hb hc hd;  dsimp at hb hd,
  { exact (ho $ A.comp he).atom hz (by assumption) (by assumption) },
  { exact (ho $ A.comp he).near_litter hz (by assumption) (by assumption) }
end

/-- A specification is the graph of a structural permutation if it is one-to-one and total.
This is one direction of implication of `total-1-1-gives-perm` on the blueprint - the other
direction may not be needed. We may also require `hσ₃ : σ.co_total` or
`hσ₄ : σ⁻¹.one_to_one_forward` - but hopefully this isn't needed. -/
lemma graph_struct_perm (σ : spec B) (hσ₁ : σ.one_to_one_forward) (hσ₂ : σ.total) :
  ∃ (π : struct_perm B), π.to_spec = σ := sorry

/-- The allowability condition on atoms.
In an absent litter, we must specify only `< κ`-many atoms.
In a present litter, we can specify either `< κ`-many atoms and they are mapped to the right place,
or all of the atoms in the litter, and their range is exactly the image of the litter.
Note that the `small` constructor does not depend on whether the litter is present or absent. -/
@[mk_iff] inductive atom_cond (σ : spec β) (L : litter) (A : extended_index β) : Prop
| all
    (L' : near_litter) (hL : (⟨inr ⟨L.to_near_litter, L'⟩, A⟩ : binary_condition β) ∈ σ)
    (atom_map : litter_set L → atom) :
  (∀ a ∈ litter_set L, (⟨inl ⟨a, atom_map ⟨a, ‹_›⟩⟩, A⟩ : binary_condition β) ∈ σ) →
  L'.snd.val = range atom_map → atom_cond
| small_out
    (hL : (inr L.to_near_litter, A) ∉ σ.domain) :
  small {a ∈ litter_set L | (⟨inl a, A⟩ : support_condition β) ∈ σ.domain} → atom_cond
| small_in
    (L' : near_litter) (hL : (inr (L.to_near_litter, L'), A) ∈ σ) :
  small {a ∈ litter_set L | (⟨inl a, A⟩ : support_condition β) ∈ σ.domain} →
  (∀ ⦃a b : atom⦄ (hin : (inl (a, b), A) ∈ σ), a ∈ litter_set L ↔ b ∈ L'.snd.val) → atom_cond

/-- The allowability condition on near-litters.
If a near-litter is present, so are its litter and all atoms in the symmetric difference, and it is
mapped to the right place. -/
def near_litter_cond (σ : spec β) (N₁ N₂ : near_litter) (A : extended_index β) : Prop :=
(⟨inr ⟨N₁, N₂⟩, A⟩ : binary_condition β) ∈ σ →
  ∃ M, (⟨inr ⟨N₁.fst.to_near_litter, M⟩, A⟩ : binary_condition β) ∈ σ ∧
  ∃ (symm_diff : litter_set N₁.fst ∆ N₁.snd → atom),
    (∀ a : litter_set N₁.fst ∆ N₁.snd, (⟨inl ⟨a, symm_diff a⟩, A⟩ : binary_condition β) ∈ σ) ∧
  N₂.snd.val = M.snd.val ∆ range symm_diff

variables (B) {σ : spec B} {A : extended_index B}

/-- This is the allowability condition for flexible litters of a given extended index.
Either all flexible litters are in both the domain and range (`all`), or there are `μ`-many not in
the domain and `μ`-many not in the range. -/
@[mk_iff] inductive flex_cond (σ : spec B) (A : extended_index B) : Prop
| co_large :
  #μ = #{L | flex L A ∧ (inr L.to_near_litter, A) ∉ σ.domain} →
  #μ = #{L | flex L A ∧ (inr L.to_near_litter, A) ∉ σ.range} →
  flex_cond
| all :
  (∀ L, flex L A → (inr L.to_near_litter, A) ∈ σ.domain) →
  (∀ L, flex L A → (inr L.to_near_litter, A) ∈ σ.range) →
  flex_cond

-- TODO: This instance feels unnecessary and really shouldn't be needed.
-- Is there a better way of writing `non_flex_cond` so that the instance is inferred?
instance (β : Λ) (γ : type_index) (hγ : γ < β) (A : path (B : type_index) β) :
mul_action (allowable_path (le_index.cons ⟨β, B.path.comp A⟩ hγ))
  (tangle_path (lt_index.mk' hγ (B.path.comp A) : le_index α)) :=
core_tangle_data.allowable_action

/-- The allowability condition on non-flexible litters.
Whenever `σ` contains some condition `⟨⟨f_{γ,δ}^A(g), N⟩, [-1,δ,A]⟩`, then every allowable
permutation extending `σ` has `N = f_{γ,δ}^A(ρ • g)`. -/
def non_flex_cond (σ : spec B) : Prop :=
∀ ⦃β : Λ⦄ ⦃γ : type_index⦄ ⦃δ : Λ⦄ (hγ : γ < β) (hδ : δ < β) (hγδ : γ ≠ δ) (N : near_litter)
  (A : path (B : type_index) β)
  (t : tangle_path ((lt_index.mk' hγ (B.path.comp A)) : le_index α)),
  (⟨inr ⟨(f_map_path hγ hδ t).to_near_litter,
    N⟩, (A.cons $ coe_lt_coe.mpr hδ).cons $ bot_lt_coe _⟩ : binary_condition B) ∈ σ →
  ∀ (ρ : allowable_path (⟨β, B.path.comp A⟩ : le_index α)),
    ρ.to_struct_perm.satisfies (lower A σ) → N.fst = f_map_path hγ hδ (ρ.derivative hγ • t)

/-- A specification is *allowable* in the forward direction if it satisfies the following
conditions. -/
structure forward_allowable (σ : spec B) : Prop :=
(one_to_one : σ.one_to_one_forward)
(atom_cond : ∀ L A, σ.atom_cond L A)
(near_litter_cond : ∀ N₁ N₂ A, σ.near_litter_cond N₁ N₂ A)
(non_flex_cond : σ.non_flex_cond B)
(support_closed : σ.domain.support_closed B)

/-- A specification is *allowable* if it is allowable in the forward and backward directions. -/
protected structure allowable (σ : spec B) : Prop :=
(forward : σ.forward_allowable B)
(backward : σ⁻¹.forward_allowable B)
(flex_cond : ∀ A, σ.flex_cond B A)

@[simp] lemma Union_eq_true {α : Type*} {p : Prop} {s : set α} (h : p) :
  (⋃ (h : p), s) = s :=
by { classical, rw Union_eq_if, rwa if_pos, }

@[simp] lemma Union_eq_false {α : Type*} {p : Prop} {s : set α} (h : ¬p) :
  (⋃ (h : p), s) = ∅ :=
by { classical, rw Union_eq_if, rwa if_neg, }

variables {B}

lemma flex_cond.inv : σ.flex_cond B A → σ⁻¹.flex_cond B A
| (flex_cond.co_large h₀ h₁) := flex_cond.co_large (by rwa domain_inv) (by rwa range_inv)
| (flex_cond.all h₀ h₁) := flex_cond.all (by rwa domain_inv) (by rwa range_inv)

@[simp] lemma flex_cond_inv : σ⁻¹.flex_cond B A ↔ σ.flex_cond B A :=
⟨λ h, by simpa only [inv_inv] using h.inv, flex_cond.inv⟩

/-- The inverse of an allowable specification is allowable. -/
lemma allowable.inv (hσ : σ.allowable B) : σ⁻¹.allowable B :=
{ forward := hσ.backward,
  backward := by { rw inv_inv, exact hσ.forward },
  flex_cond := λ A, (hσ.flex_cond A).inv }

@[simp] lemma allowable_inv : σ⁻¹.allowable B ↔ σ.allowable B :=
⟨λ h, by simpa only [inv_inv] using h.inv, allowable.inv⟩

end spec

open spec

variables (B)

/-- An *allowable partial permutation* is a specification that is allowable as defined above. -/
def allowable_spec := {σ : spec B // σ.allowable B}

variables {B}

namespace allowable_spec

instance has_inv : has_inv (allowable_spec B) := ⟨λ σ, ⟨σ.val⁻¹, σ.2.inv⟩⟩

@[simp] lemma val_inv (π : allowable_spec B) : π⁻¹.val = π.val⁻¹ := rfl

instance : has_involutive_inv (allowable_spec B) :=
subtype.val_injective.has_involutive_inv _ val_inv

end allowable_spec

variable (B)

/-- We say that *freedom of action* holds along a path `B` if any partial allowable permutation `σ`
admits an allowable permutation `π` extending it. -/
def freedom_of_action : Prop :=
∀ σ : allowable_spec B, ∃ π : allowable_path B, π.to_struct_perm.satisfies σ.val

variable {B}

lemma eq_of_support_eq (t : tangle_path B) (S : support B (allowable_path B) t)
  (π₁ π₂ : allowable_path B) (hπ : ∀ c ∈ S, π₁ • c = π₂ • c) : π₁ • t = π₂ • t :=
begin
  have := S.supports (π₂⁻¹ * π₁) _,
  rw [mul_smul, inv_smul_eq_iff] at this, exact this,
  intros c hc,
  rw [mul_smul, inv_smul_eq_iff], exact hπ c hc,
end

/-- If an allowable partial permutation `σ` supports some `α`-tangle `t`, any permutations extending
`σ` must map `t` to the same value. -/
lemma eq_of_supports (σ : allowable_spec B) (t : tangle_path B)
  (ht : supports (allowable_path B) σ.val.domain t) (π₁ π₂ : allowable_path B)
  (hπ₁ : π₁.to_struct_perm.satisfies σ.val) (hπ₂ : π₂.to_struct_perm.satisfies σ.val) :
  π₁ • t = π₂ • t :=
begin
  refine eq_of_support_eq t ⟨σ.val.domain, ht⟩ π₁ π₂ _,
  intros c hc,
  change c ∈ σ.val.domain at hc, rw mem_domain at hc,
  obtain ⟨⟨⟨a₁, a₂⟩ | ⟨N₁, N₂⟩, C⟩, hd, rfl⟩ := hc;
  { specialize hπ₁ hd, specialize hπ₂ hd,
    unfold satisfies_cond at hπ₁ hπ₂,
    simp only [sum.elim_inl, sum.elim_inr] at hπ₁ hπ₂,
    simp only [binary_condition.domain_mk, map_inl, map_inr],
    rw prod.eq_iff_fst_eq_snd_eq, split,
    { simp only [has_smul.smul, has_smul.comp.smul, map_inl, map_inr],
      exact hπ₁.trans hπ₂.symm, },
    { refl, } },
end

/-- The action lemma. If freedom of action holds, and `σ` is any allowable partial permutation
that supports some `α`-tangle `t`, then there exists a unique `α`-tangle `σ(t)` such that every
allowable permutation `π` extending `σ` maps `t` to `σ(t)`.

Freedom of action gives some extension `π`, and hence some candidate value; the support condition
implies that any two extensions agree. We use the above lemma for the second part. -/
lemma exists_tangle_of_supports (σ : allowable_spec B) (t : tangle_path B)
  (foa : freedom_of_action B) (ht : supports (allowable_path B) σ.val.domain t) :
  ∃ s, ∀ π : allowable_path B, π.to_struct_perm.satisfies σ.val → π • t = s :=
⟨(foa σ).some • t, λ π₁ hπ₁, eq_of_supports σ t ht π₁ (foa σ).some hπ₁ (foa σ).some_spec⟩

end con_nf
