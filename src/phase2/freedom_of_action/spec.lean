import mathlib.transfer
import phase2.basic
import order.copy

/-!
# Specifications

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
-/

open function quiver set sum
open_locale cardinal

universe u

namespace con_nf
variables [params.{u}]

open struct_perm

section
variables {α β γ : type_index}

/-- A *binary condition* is like a support condition but uses either two atoms or two near-litters
instead of one. A binary condition `⟨⟨x, y⟩, A⟩` represents the constraint `π_A(x) = y` on an
allowable permutation. -/
def binary_condition (α : type_index) : Type u :=
((atom × atom) ⊕ (near_litter × near_litter)) × extended_index α

namespace binary_condition

/-- The "identity" equivalence between
`(atom × atom ⊕ near_litter × near_litter) × extended_index α` and
`binary_condition α`. -/
def to_condition : (atom × atom ⊕ near_litter × near_litter) × extended_index α
  ≃ binary_condition α := equiv.refl _

/-- The "identity" equivalence between `binary_condition α` and
`(atom × atom ⊕ near_litter × near_litter) × extended_index α`. -/
def of_condition : binary_condition α ≃
  (atom × atom ⊕ near_litter × near_litter) × extended_index α := equiv.refl _

noncomputable instance struct_perm_mul_action : mul_action (struct_perm α) (binary_condition α) :=
{ smul := λ π c, ⟨derivative c.snd π • c.fst, c.snd⟩,
  one_smul := by { rintro ⟨atoms | Ns, A⟩; unfold has_smul.smul; simp },
  mul_smul := begin
    rintro π₁ π₂ ⟨atoms | Ns, A⟩; unfold has_smul.smul;
    rw derivative_mul; dsimp; rw [mul_smul, mul_smul],
  end }

noncomputable instance struct_perm_mul_action' {B : le_index α}
  {β : Λ} {γ : type_index} {hγ : γ < β} (A : path (B : type_index) β) :
  mul_action (struct_perm ((lt_index.mk' hγ (B.path.comp A)) : le_index α).index)
    (binary_condition γ) :=
binary_condition.struct_perm_mul_action

@[simp] lemma smul_to_condition (π : struct_perm α)
  (x : (atom × atom ⊕ near_litter × near_litter) × extended_index α) :
  π • to_condition x = to_condition ⟨derivative x.2 π • x.1, x.2⟩ := rfl

/-- The binary condition representing the inverse permutation. If `π_A(x) = y`, then `π_A⁻¹(y) = x`.
-/
instance (α : type_index) : has_involutive_inv (binary_condition α) :=
{ inv := λ c, ⟨c.1.map prod.swap prod.swap, c.2⟩,
  inv_inv := by rintro ⟨⟨a₁, a₂⟩ | ⟨N₁, N₂⟩, i⟩; refl }

@[simp] lemma inv_def (c : binary_condition α) :
  c⁻¹ = ⟨c.1.map prod.swap prod.swap, c.2⟩ := rfl

/-- Converts a binary condition `⟨⟨x, y⟩, A⟩` into the support condition `⟨x, A⟩`. -/
def domain : binary_condition α → support_condition α := prod.map (sum.map prod.fst prod.fst) id

/-- Converts a binary condition `⟨⟨x, y⟩, A⟩` into the support condition `⟨y, A⟩`. -/
def range : binary_condition α → support_condition α := prod.map (sum.map prod.snd prod.snd) id

@[simp] lemma domain_mk (x : (atom × atom) ⊕ (near_litter × near_litter)) (A : extended_index α) :
  domain (x, A) = (x.map prod.fst prod.fst, A) := rfl

@[simp] lemma range_mk (x : (atom × atom) ⊕ (near_litter × near_litter)) (A : extended_index α) :
  range (x, A) = (x.map prod.snd prod.snd, A) := rfl

@[simp] lemma domain_inv (c : binary_condition α) : c⁻¹.domain = c.range :=
by obtain ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ := c; refl

@[simp] lemma range_inv (c : binary_condition α) : c⁻¹.range = c.domain :=
by obtain ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ := c; refl

end binary_condition

/-- There are `μ` binary conditions. -/
lemma mk_binary_condition (α : type_index) : #(binary_condition α) = #μ :=
begin
  have h := μ_strong_limit.is_limit.aleph_0_le,
  rw [binary_condition, ← cardinal.mul_def, ← cardinal.add_def, ← cardinal.mul_def,
      ← cardinal.mul_def, mk_atom, mk_near_litter, cardinal.mul_eq_self h, cardinal.add_eq_self h],
  exact cardinal.mul_eq_left h (le_trans (mk_extended_index α) (le_of_lt (lt_trans Λ_lt_κ κ_lt_μ)))
      (mk_extended_index_ne_zero α),
end

/-- A *unary specification* is a set of support conditions. This can be thought of as either the
domain or range of a `spec`. -/
abbreviation unary_spec (α : type_index) : Type u := set (support_condition α)

/-- A *specification* of an allowable permutation is a set of binary conditions on the allowable
permutation.

We make this a custom structure (rather than simply `set (binary_condition α)`) to make
`σ⁻¹.domain = σ.range` and `σ⁻¹.range = σ.domain` definitionally equal. This would already be the
case if Lean had definitional eta reduction for structures. -/
structure spec (α : type_index) : Type u :=
(carrier : set (binary_condition α))
(domain range : unary_spec α)
(image_domain' : binary_condition.domain '' carrier = domain)
(image_range' : binary_condition.range '' carrier = range)

namespace spec
variables {σ τ : spec α} {c d : binary_condition α}

attribute [protected] range

instance : set_like (spec α) (binary_condition α) :=
{ coe := carrier,
  coe_injective' := λ s t h,
    by { cases s, cases t, dsimp at h, subst h, congr'; exact ‹_ = _›.symm.trans ‹_› } }

@[ext] lemma ext : (∀ c, c ∈ σ ↔ c ∈ τ) → σ = τ := set_like.ext

@[simps] def equiv_set : spec α ≃ set (binary_condition α) :=
{ to_fun := coe,
  inv_fun := λ s, { carrier := s,
                    domain := binary_condition.domain '' s,
                    range := binary_condition.range '' s,
                    image_domain' := rfl,
                    image_range' := rfl },
  left_inv := λ _, set_like.coe_injective rfl,
  right_inv := λ _, rfl }

@[simp] lemma image_domain (σ : spec α) :
  binary_condition.domain '' (σ : set (binary_condition α)) = σ.domain := σ.image_domain'

@[simp] lemma image_range (σ : spec α) :
  binary_condition.range '' (σ : set (binary_condition α)) = σ.range := σ.image_range'

instance : complete_distrib_lattice (spec α) :=
equiv_set.complete_distrib_lattice.copy
/- le  -/ _ rfl
/- top -/ _ rfl
/- bot -/ ⟨∅, ∅, ∅, image_empty _, image_empty _⟩ (set_like.coe_injective rfl)
/- sup -/ (λ x y, ⟨x ∪ y, x.domain ∪ y.domain, x.range ∪ y.range,
            by simp_rw [←image_domain, image_union], by simp_rw [←image_range, image_union]⟩)
              (funext $ λ _, funext $ λ _, set_like.coe_injective rfl)
/- inf -/ _ rfl
/- Sup -/ (λ s, ⟨⋃ x ∈ s, ↑x, ⋃ x ∈ s, spec.domain x, ⋃ x ∈ s, spec.range x,
            by simp_rw [image_Union, image_domain], by simp_rw [image_Union, image_range]⟩)
              (funext $ λ _, set_like.coe_injective rfl)
/- Inf -/ _ rfl

@[simp] lemma coe_bot : ((⊥ : spec α) : set $ binary_condition α) = ∅ := rfl
@[simp] lemma coe_top : ((⊤ : spec α) : set $ binary_condition α) = univ := rfl
@[simp] lemma coe_sup (σ τ : spec α) : (↑(σ ⊔ τ) : set $ binary_condition α) = σ ∪ τ := rfl
@[simp] lemma coe_inf (σ τ : spec α) : (↑(σ ⊓ τ) : set $ binary_condition α) = σ ∩ τ := rfl
@[simp] lemma coe_Sup (s : set $ spec α) : (↑(Sup s) : set $ binary_condition α) = ⋃ x ∈ s, ↑x :=
rfl

@[simp] lemma coe_mk (carrier : set (binary_condition α))
  (domain range : unary_spec α)
  (image_domain' : binary_condition.domain '' carrier = domain)
  (image_range' : binary_condition.range '' carrier = range) :
  ((⟨carrier, domain, range, image_domain', image_range'⟩ : spec α) : set (binary_condition α))
    = carrier := rfl
@[simp] lemma mem_mk (carrier : set (binary_condition α))
  (domain range : unary_spec α)
  (image_domain' : binary_condition.domain '' carrier = domain)
  (image_range' : binary_condition.range '' carrier = range)
  (c : binary_condition α) :
  c ∈ (⟨carrier, domain, range, image_domain', image_range'⟩ : spec α) ↔ c ∈ carrier := iff.rfl

@[simp] lemma mem_sup : c ∈ σ ⊔ τ ↔ c ∈ σ ∨ c ∈ τ := iff.rfl
@[simp] lemma mem_inf : c ∈ σ ⊓ τ ↔ c ∈ σ ∧ c ∈ τ := iff.rfl
@[simp] lemma mem_Sup {s : set $ spec α} : c ∈ Sup s ↔ ∃ σ ∈ s, c ∈ σ := mem_Union₂

@[simp] lemma mem_domain {a : support_condition α} {σ : spec α} :
  a ∈ σ.domain ↔ ∃ cond : binary_condition α, cond ∈ σ ∧ cond.domain = a :=
by simp_rw [←image_domain, mem_image, set_like.mem_coe]

@[simp] lemma mem_range {a : support_condition α} {σ : spec α} :
  a ∈ σ.range ↔ ∃ cond : binary_condition α, cond ∈ σ ∧ cond.range = a :=
by simp_rw [←image_range, mem_image, set_like.mem_coe]

lemma mem_domain_of_mem {c : binary_condition α} {σ : spec α} :
  c ∈ σ → binary_condition.domain c ∈ σ.domain :=
by { intro h, rw mem_domain, exact ⟨_, h, rfl⟩ }

lemma mem_range_of_mem {c : binary_condition α} {σ : spec α} :
  c ∈ σ → binary_condition.range c ∈ σ.range :=
by { intro h, rw mem_range, exact ⟨_, h, rfl⟩ }

lemma inl_mem_domain {σ : spec α} {a : atom × atom} {A : extended_index α} :
  (inl a, A) ∈ σ → (inl a.1, A) ∈ σ.domain :=
mem_domain_of_mem

lemma inr_mem_domain {σ : spec α} {N : near_litter × near_litter} {A : extended_index α} :
  (inr N, A) ∈ σ → (inr N.1, A) ∈ σ.domain :=
mem_domain_of_mem

lemma inl_mem_range {σ : spec α} {a : atom × atom} {A : extended_index α} :
  (inl a, A) ∈ σ → (inl a.2, A) ∈ σ.range :=
mem_range_of_mem

lemma inr_mem_range {σ : spec α} {N : near_litter × near_litter} {A : extended_index α} :
  (inr N, A) ∈ σ → (inr N.2, A) ∈ σ.range :=
mem_range_of_mem

@[simp] lemma domain_bot : (⊥ : spec α).domain = ∅ := rfl
@[simp] lemma range_bot : (⊥ : spec α).range = ∅ := rfl

@[simp] lemma domain_sup (σ τ : spec α) : (σ ⊔ τ).domain = σ.domain ∪ τ.domain := rfl
@[simp] lemma range_sup (σ τ : spec α) : (σ ⊔ τ).range = σ.range ∪ τ.range := rfl

lemma domain_Sup (S : set (spec α)) : (Sup S).domain = ⋃ s ∈ S, domain s := rfl
lemma range_Sup (S : set (spec α)) : (Sup S).range = ⋃ s ∈ S, spec.range s := rfl

instance : has_singleton (binary_condition α) (spec α) :=
⟨λ c, ⟨{c}, {c.domain}, {c.range}, image_singleton, image_singleton⟩⟩

@[simp] lemma mem_singleton : c ∈ ({d} : spec α) ↔ c = d := iff.rfl
@[simp] lemma coe_singleton : (({c} : spec α) : set $ binary_condition α) = {c} := rfl
@[simp] lemma domain_singleton : ({c} : spec α).domain = {c.domain} := rfl
@[simp] lemma range_singleton : ({c} : spec α).range = {c.range} := rfl

instance : has_inv (spec α) :=
⟨λ σ, { carrier := σ⁻¹,
  domain := σ.range,
  range := σ.domain,
  image_domain' := by rw [←image_range, ←image_inv, image_comm binary_condition.domain_inv,
    image_image],
  image_range' := by rw [←image_domain, ←image_inv, image_comm binary_condition.range_inv,
    image_image] }⟩

@[simp] lemma inv_mk (carrier domain range image_domain image_range) :
  (⟨carrier, domain, range, image_domain, image_range⟩ : spec α)⁻¹ =
    ⟨carrier⁻¹, range, domain,
      by rw [←image_range, ←image_inv, image_comm binary_condition.domain_inv, image_image],
      by rw [←image_domain, ←image_inv, image_comm binary_condition.range_inv, image_image]⟩ := rfl

instance : has_involutive_inv (spec α) :=
{ inv := has_inv.inv,
  inv_inv := by { rintro ⟨_, _, _, _, _⟩, simp } }

@[simp] lemma mem_inv : c ∈ σ⁻¹ ↔ c⁻¹ ∈ σ := iff.rfl
@[simp] lemma inv_mem_inv : c⁻¹ ∈ σ⁻¹ ↔ c ∈ σ :=
⟨λ h, by rwa [mem_inv, inv_inv] at h, λ h, by rwa [mem_inv, inv_inv]⟩
@[simp] lemma coe_inv (σ : spec α) : (↑(σ⁻¹) : set $ binary_condition α) = σ⁻¹ := rfl
@[simp] lemma domain_inv (σ : spec α) : σ⁻¹.domain = σ.range := rfl
@[simp] lemma range_inv (σ : spec α) : σ⁻¹.range = σ.domain := rfl

lemma le_iff_subset (σ τ : spec α) : σ ≤ τ ↔ σ.carrier ⊆ τ.carrier := iff.rfl

@[simp] lemma inv_le_inv (σ τ : spec α) : σ⁻¹ ≤ τ⁻¹ ↔ σ ≤ τ :=
⟨λ h x hx, inv_mem_inv.mp (h (inv_mem_inv.mpr hx)),
  λ h x hx, inv_mem_inv.mp (h (inv_mem_inv.mpr hx))⟩

@[simp] lemma inl_mem_inv (σ : spec α) (a : atom × atom) (A : extended_index α) :
  (inl a, A) ∈ σ⁻¹ ↔ (inl a.swap, A) ∈ σ :=
mem_inv

@[simp] lemma inr_mem_inv (σ : spec α) (N : near_litter × near_litter) (A : extended_index α) :
  (inr N, A) ∈ σ⁻¹ ↔ (inr N.swap, A) ∈ σ :=
mem_inv

lemma sup_inv (σ τ : spec α) : (σ ⊔ τ)⁻¹ = σ⁻¹ ⊔ τ⁻¹ :=
by { ext, simp only [mem_inv, mem_sup] }

lemma Sup_inv (S : set (spec α)) : (Sup S)⁻¹ = Sup (has_inv.inv '' S) :=
begin
  ext,
  simp only [mem_inv, mem_Sup, exists_prop, image_inv, set.mem_inv],
  split; rintro ⟨σ, h⟩; exact ⟨σ⁻¹, by simp only [h, inv_inv, mem_inv, and_self]⟩,
end

end spec

namespace struct_perm
variables {π : struct_perm α} {σ ρ : spec α}

/-- A structural permutation *satisfies* a condition `⟨⟨x, y⟩, A⟩` if `π_A(x) = y`. -/
def satisfies_cond (π : struct_perm α) (c : binary_condition α) :=
c.fst.elim
  (λ atoms, derivative c.snd π • atoms.fst = atoms.snd)
  (λ Ns, derivative c.snd π • Ns.fst = Ns.snd)

@[simp] lemma satisfies_cond_atoms (a b : atom) (A : extended_index α) :
  π.satisfies_cond ⟨inl ⟨a, b⟩, A⟩ ↔ derivative A π • a = b :=
iff.rfl

@[simp] lemma satisfies_cond_near_litters (M N : near_litter) (A : extended_index α) :
  π.satisfies_cond ⟨inr ⟨M, N⟩, A⟩ ↔ derivative A π • M = N :=
iff.rfl

/-- A structural permutation *satisfies* a specification if for all conditions `⟨⟨x, y⟩, A⟩` in the
specification, we have `π_A(x) = y`. -/
def satisfies (π : struct_perm α) (σ : spec α) : Prop := ∀ ⦃c⦄, c ∈ σ → π.satisfies_cond c

lemma satisfies.mono (h : σ ≤ ρ) (hρ : π.satisfies ρ) : π.satisfies σ := λ c hc, hρ $ h hc

/-- There is an injection from the type of structural permutations to the type of specifications,
in such a way that any structural permutation satisfies its specification. We construct this
specification by simply drawing the graph of the permutation on atoms and near-litters. -/
def to_spec (π : struct_perm α) : spec α :=
spec.equiv_set.symm $
  range (λ x : atom × extended_index α, ⟨inl ⟨x.fst, derivative x.snd π • x.fst⟩, x.snd⟩) ∪
  range (λ x : near_litter × extended_index α, ⟨inr ⟨x.fst, derivative x.snd π • x.fst⟩, x.snd⟩)

/-- Any structural permutation satisfies its own specification. -/
lemma satisfies_to_spec (π : struct_perm α) : π.satisfies π.to_spec :=
begin
  rintro ⟨⟨x, y⟩ | ⟨x, y⟩, A⟩ (hxy | hxy);
  simpa only [mem_range, prod.mk.inj_iff, prod.exists, exists_eq_right, exists_eq_left,
    sum.elim_inl, sum.elim_inr, false_and, exists_false] using hxy,
end

/-- The map from structural permutations to their specifications is injective. -/
lemma to_spec_injective : ∀ (α : type_index), injective (@to_spec _ α)
| ⊥ := λ σ τ h, ext_bot _ _ $ λ a, begin
    simp only [to_spec, embedding_like.apply_eq_iff_eq, ext_iff] at h,
    simpa only [prod.mk.inj_iff, exists_eq_right, derivative_nil, exists_eq_left, exists_false,
      or_false, eq_self_iff_true, true_iff, prod.exists, mem_union_eq, mem_range, iff_true]
        using h ⟨inl ⟨a, τ • a⟩ , path.nil⟩,
  end
| (α : Λ) := λ σ τ h, of_coe.injective $ funext $ λ β, funext $ λ hβ, to_spec_injective β $
    set_like.ext $ begin
    rintro ⟨x_fst, x_snd⟩,
    simp only [to_spec, embedding_like.apply_eq_iff_eq, ext_iff] at h ⊢,
    specialize h ⟨x_fst, (@path.cons type_index con_nf.quiver ↑α ↑α β path.nil hβ).comp x_snd⟩,
    simp only [spec.equiv_set, prod.mk.inj_iff, exists_eq_right, prod.exists, mem_union_eq,
               mem_range, equiv.coe_fn_symm_mk, ←derivative_derivative, derivative_cons_nil] at h ⊢,
    cases x_fst,
    { simpa only [spec.mem_mk, mem_union_eq, mem_range, prod.mk.inj_iff, prod.exists,
                  exists_eq_right, exists_false, or_false] using h },
    { simpa only [prod.exists, spec.mem_mk, mem_union_eq, mem_set_of_eq, mem_range,
                  prod.mk.inj_iff, prod.exists, exists_false, exists_eq_right, false_or] using h }
  end
using_well_founded { dec_tac := `[assumption] }

end struct_perm

/-- We can extend any support condition to one of a higher proper type index `α` by providing a path
connecting the old extended index up to `α`. -/
def support_condition.extend_path (c : support_condition β) (A : path (α : type_index) β) :
  support_condition α := ⟨c.fst, A.comp c.snd⟩

namespace binary_condition

/-- We can extend any binary condition to one of a higher proper type index `α` by providing a path
connecting the old extended index up to `α`. -/
def extend_path (c : binary_condition β) (A : path α β) : binary_condition α :=
⟨c.fst, A.comp c.snd⟩

@[simp] lemma extend_path_inv (c : binary_condition β) (A : path α β) :
  c⁻¹.extend_path A = (c.extend_path A)⁻¹ := rfl

end binary_condition

namespace unary_spec

/-- We can lower a unary specification to a lower proper type index with respect to a path
`A : α ⟶ β` by only keeping support conditions whose paths begin with `A`. -/
def lower (σ : unary_spec α) (A : path α β) : unary_spec β := {c | c.extend_path A ∈ σ}

/-- Lowering along the empty path does nothing. -/
@[simp] lemma lower_nil (σ : unary_spec α) : σ.lower path.nil = σ :=
by simp only
  [unary_spec.lower, support_condition.extend_path, path.nil_comp, prod.mk.eta, set_of_mem_eq]

/-- The lowering map is functorial. -/
@[simp] lemma lower_lower (σ : unary_spec α) (A : path α β) (B : path β γ) :
  (σ.lower A).lower B = σ.lower (A.comp B) :=
by simp only [unary_spec.lower, support_condition.extend_path, mem_set_of_eq, path.comp_assoc]

@[simp] lemma lower_union (σ τ : unary_spec α) (A : path α β) :
  (σ ∪ τ).lower A = σ.lower A ∪ τ.lower A :=
by ext ⟨x | x, y⟩; simp only [unary_spec.lower, mem_union_eq, mem_set_of_eq]

@[simp] lemma lower_sUnion (c : set (unary_spec α)) (A : path α β) :
  lower (⋃₀ c) A = ⋃ s ∈ c, lower s A :=
by { ext, simp only [lower, mem_Union, mem_set_of_eq, mem_sUnion] }

@[simp] lemma lower_Union {ι : Sort*} {f : ι → unary_spec α} (A : path α β) :
  lower (⋃ i, f i) A = ⋃ i, lower (f i) A :=
by { ext, simp only [lower, mem_Union, mem_set_of_eq] }

end unary_spec

namespace spec
variables {A : path α β} {σ : spec α} {c : binary_condition β}

/-- We can lower a specification to a lower proper type index with respect to a path
`A : α ⟶ β` by only keeping binary conditions whose paths begin with `A`. -/
def lower (A : path α β) (σ : spec α) : spec β := {
  carrier := {c | c.extend_path A ∈ σ},
  domain := {c | c.extend_path A ∈ σ.domain},
  range := {c | c.extend_path A ∈ σ.range},
  image_domain' := set.ext $ λ x, begin
    split,
    { rintro ⟨⟨_, C⟩, hx, rfl⟩,
      exact mem_domain.2 ⟨_, hx, rfl⟩ },
    { intro hx,
      cases x with x C,
      simp only [mem_domain, mem_set_of_eq] at hx,
      obtain ⟨⟨b, _⟩, hb, hdom⟩ := hx,
      simp only [support_condition.extend_path, binary_condition.domain, prod.map_mk, id.def, prod.mk.inj_iff] at hdom,
      cases hdom.2,
      exact ⟨⟨b, C⟩, hb, by simp only [binary_condition.domain, prod.map_mk, id.def, prod.mk.inj_iff, eq_self_iff_true, and_true, hdom]⟩, }
  end,
  image_range' := set.ext $ λ x, begin
    split,
    { rintro ⟨⟨_, C⟩, hx, rfl⟩,
      exact mem_range.2 ⟨_, hx, rfl⟩ },
    { intro hx,
      cases x with x C,
      simp only [mem_range, mem_set_of_eq] at hx,
      obtain ⟨⟨b, _⟩, hb, hdom⟩ := hx,
      simp only [support_condition.extend_path, binary_condition.range, prod.map_mk, id.def, prod.mk.inj_iff] at hdom,
      cases hdom.2,
      exact ⟨⟨b, C⟩, hb, by simp only [binary_condition.range, prod.map_mk, id.def, prod.mk.inj_iff, eq_self_iff_true, and_true, hdom]⟩, }
  end,
}

@[simp] lemma coe_lower (A : path α β) (σ : spec α) :
  (σ.lower A : set (binary_condition β)) = {c | c.extend_path A ∈ σ} := rfl

@[simp] lemma mem_lower : c ∈ σ.lower A ↔ c.extend_path A ∈ σ := iff.rfl

/-- Lowering along the empty path does nothing. -/
@[simp] lemma lower_nil (σ : spec α) : σ.lower path.nil = σ :=
set_like.ext $ λ _, by simp only [binary_condition.extend_path, path.nil_comp, prod.mk.eta,
  mem_lower]

/-- The lowering map is functorial. -/
@[simp] lemma lower_lower (A : path α β) (B : path β γ) (σ : spec α) :
  (σ.lower A).lower B = σ.lower (A.comp B) :=
set_like.ext $ λ _, by simp only [binary_condition.extend_path, path.comp_assoc, mem_lower]

@[simp] lemma lower_sup (σ τ : spec α) (A : path α β) : (σ ⊔ τ).lower A = σ.lower A ⊔ τ.lower A :=
set_like.ext $ λ _, by simp only [mem_lower, mem_sup]

@[simp] lemma lower_inv (σ : spec α) (A : path α β) : σ⁻¹.lower A = (σ.lower A)⁻¹ :=
set_like.ext $ λ _, by simpa only [mem_lower, mem_inv, binary_condition.inv_def]

end spec

/-- Lowering a specification corresponds exactly to forming the derivative of the corresponding
structural permutation. -/
lemma struct_perm.spec_lower_eq_derivative (π : struct_perm α) (A : path α β) :
  π.to_spec.lower A = (struct_perm.derivative A π).to_spec :=
begin
  ext,
  simp only [spec.mem_lower, struct_perm.to_spec, mem_union_eq, mem_range, prod.exists,
    mem_set_of_eq],
  cases c,
  simp only [binary_condition.extend_path, prod.mk.inj_iff, exists_eq_right],
  split; rintro (⟨⟨s, D⟩, h⟩ | ⟨⟨s, D⟩, h⟩),

  refine or.inl ⟨(s, c_snd), _⟩,
  swap 2,
  refine or.inr ⟨(s, c_snd), _⟩,
  swap 3,
  refine or.inl ⟨(s, A.comp c_snd), _⟩,
  swap 4,
  refine or.inr ⟨(s, A.comp c_snd), _⟩,
  all_goals { dsimp only at h ⊢,
    try { rw derivative_derivative },
    try { rw derivative_derivative at h },
    cases h,
    refl },
end

namespace spec
variables {A : path α β} {σ : spec α}

/-- A specification is total if it specifies where every element in its domain goes. -/
def total (σ : spec α) : Prop := ∀ c, c ∈ σ.domain

/-- A specification is co-total if it specifies where every element in its codomain came from. -/
def co_total (σ : spec α) : Prop := ∀ c, c ∈ σ.range

@[simp] lemma total_inv : σ⁻¹.total ↔ σ.co_total := by simp only [total, co_total, domain_inv]
@[simp] lemma co_total_inv : σ⁻¹.co_total ↔ σ.total := by simp only [total, co_total, range_inv]

alias total_inv ↔ total.of_inv co_total.inv
alias co_total_inv ↔ co_total.of_inv total.inv

protected lemma total.lower (hσ : σ.total) : (σ.lower A).total :=
begin
  rintro c,
  obtain ⟨y, hyσ, hy⟩ := mem_domain.1 (hσ $ c.extend_path A),
  set z : binary_condition β := ⟨y.fst, c.snd⟩,
  refine mem_domain.2 ⟨z, _, prod.ext_iff.2 ⟨(prod.ext_iff.1 hy).1, rfl⟩⟩,
  suffices : y = z.extend_path A, -- probably can cut this
  { rwa this at hyσ },
  ext,
  { refl },
  unfold binary_condition.extend_path,
  dsimp only,
  exact congr_arg prod.snd hy,
end

protected lemma co_total.lower (hσ : σ.co_total) : (σ.lower A).co_total :=
begin
  rintro c,
  obtain ⟨y, hyσ, hy⟩ := mem_range.1 (hσ $ c.extend_path A),
  set z : binary_condition β := ⟨y.fst, c.snd⟩,
  refine mem_range.2 ⟨z, _, prod.ext_iff.2 ⟨(prod.ext_iff.1 hy).1, rfl⟩⟩,
  suffices : y = z.extend_path A, -- probably can cut this
  { rwa this at hyσ },
  ext,
  { refl },
  unfold binary_condition.extend_path,
  dsimp only,
  exact congr_arg prod.snd hy,
end

end spec
end

end con_nf
