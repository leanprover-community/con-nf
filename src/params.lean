import set_theory.cardinal.cofinality

/-!
# Parameters of the construction

This file is based on sections 3.1 and 3.2 of the paper.
-/

/-!
We do not assume that our definitions, instances, lemmas and theorems are 'computable';
that is, can be provably evaluated in finite time by a computer.
For our purposes, restricting to only computable functions is unnecessary.
-/
noncomputable theory

open cardinal
open_locale cardinal classical

universe u

namespace con_nf

/--
The parameters of the constructions. We collect them all in one class for simplicity.
Note that the ordinal `λ` in the paper is instead referred to here as `Λ`, since the symbol `λ` is
used for lambda abstractions.

Ordinals and cardinals are represented here as arbitrary types (not sets) with certain properties.
For instance, `Λ` is an arbitrary type that has an ordering `Λr`, which is assumed to be a
well-ordering (the `Λwf` term is a proof of this fact). If `Λr a b` holds, then we can say `a < b`.

The prefix `#` denotes the cardinality of a type.

Where possible, we use `<` and `≤` instead of `>` and `≥`. Human readers can easily convert between
the two, but it is not as immediately transparent for Lean. For simplicity, we keep with the
convention of using only `<` and `≤`.

When working with these parameters, it is useful to `open params` in order to address the parameters
simply by name, instead of having to type `params.Λ`, for instance.
-/
class params :=
(Λ : Type u) (Λr : Λ → Λ → Prop) [Λwf : is_well_order Λ Λr]
(hΛ : (ordinal.type Λr).is_limit)
(κ : Type u) (κ_regular : (#κ).is_regular)
(μ : Type u) (μr : μ → μ → Prop) [μwf : is_well_order μ μr]
(μ_ord : ordinal.type μr = (#μ).ord)
(μ_limit : (#μ).is_strong_limit)
(κ_lt_μ : #κ < #μ)
(κ_le_μ_cof : #κ ≤ (#μ).ord.cof)
(δ : Λ)
(hδ : (ordinal.typein Λr δ).is_limit)

/-- There exists a set of valid parameters for the model. -/
example : params := sorry

open params

variables [params.{u}]

/-- To allow Lean's type checker to see that the ordering `Λr` is a well-ordering without having to
explicitly write `Λwf` everywhere, we declare it as an instance. -/
instance : is_well_order Λ Λr := Λwf
/-- We can deduce from the well-ordering `Λwf` that `Λ` is linearly ordered. -/
instance : linear_order Λ := linear_order_of_STO' Λr
/-- We deduce that `Λ` has a well-founded relation. -/
instance : has_well_founded Λ := is_well_order.to_has_well_founded

/-- Since `μ` has cofinality `≥ κ`, the cardinality of `κ` must be at most that of `μ`. -/
lemma κ_le_μ : #κ ≤ #μ := κ_le_μ_cof.trans $ ordinal.cof_ord_le _

/-- The base type of the construction, `τ₋₁` in the document. Instead of declaring it as an
arbitrary type of cardinality `μ` and partitioning it in parts of cardinality `κ` afterwards, we
define it as `μ × κ`, which has the correct cardinality and comes with an obvious partition.

This type is occasionally referred to as a type of atoms. These are not 'atoms' in the ZFU, TTTU or
NFU sense; they are simply the elements of the model which are in type `τ₋₁`. -/
def base_type : Type* := μ × κ

/-- The cardinality of `τ₋₁` is the cardinality of `μ`.
We will prove that all types constructed in our model have cardinality equal to `μ`. -/
@[simp] lemma mk_base_type : #base_type = #μ :=
by simp_rw [base_type, mk_prod, lift_id,
  mul_eq_left (κ_regular.aleph_0_le.trans κ_lt_μ.le) κ_lt_μ.le κ_regular.pos.ne']

/-- Extended type index. -/
def xti : Type* := {s : finset Λ // s.nonempty}

def xti.min (s : xti) : Λ := s.1.min' s.2
def xti.max (s : xti) : Λ := s.1.max' s.2

def xti.drop (s : xti) : option xti := if h : _ then some ⟨s.1.erase s.min, h⟩ else none
def xti.drop_max (s : xti) : option xti := if h : _ then some ⟨s.1.erase s.max, h⟩ else none

instance : has_singleton Λ xti := ⟨λ x, ⟨{x}, finset.singleton_nonempty _⟩⟩
instance : has_insert Λ xti := ⟨λ x s, ⟨insert x s.1, finset.insert_nonempty _ _⟩⟩

noncomputable def xti.dropn (s : xti) : ℕ → option xti
| 0 := some s
| (n+1) := xti.dropn n >>= xti.drop

def sdom : xti → xti → Prop
| A := λ B, A.max < B.max ∨ A.max = B.max ∧
  ∃ A' ∈ A.drop_max, ∀ B' ∈ B.drop_max,
    have (A':xti).1.card < A.1.card, from sorry,
    sdom A' B'
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ A, A.1.card)⟩]}

instance : has_lt xti := ⟨sdom⟩
instance xti.is_well_order : is_well_order xti (<) := sorry
instance : has_well_founded xti := ⟨_, xti.is_well_order.wf⟩
instance : has_le xti := ⟨λ A B, A < B ∨ A = B⟩

end con_nf
