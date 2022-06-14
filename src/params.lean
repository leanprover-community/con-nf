import set_theory.cardinal.cofinality

/-!
# Parameters of the construction -/

noncomputable theory

open cardinal
open_locale cardinal classical

universe u

namespace con_nf

/-- The parameters of the constructions. We collect them all in one class for simplicity. -/
class params :=
(Λ : Type u) (Λr : Λ → Λ → Prop) [Λwf : is_well_order Λ Λr]
(hΛ : (ordinal.type Λr).is_limit)
(κ : Type u) (κ_regular : (#κ).is_regular)
(Λ_lt_κ : #Λ < #κ)
(μ : Type u) (μr : μ → μ → Prop) [μwf : is_well_order μ μr]
(μ_ord : ordinal.type μr = (#μ).ord)
(μ_limit : (#μ).is_strong_limit)
(κ_lt_μ : #κ < #μ)
(κ_le_μ_cof : #κ ≤ (#μ).ord.cof)
(δ : Λ)
(hδ : (ordinal.typein Λr δ).is_limit)

open params

variables [params.{u}]

instance : is_well_order Λ Λr := Λwf
instance : linear_order Λ := linear_order_of_STO' Λr

/-- The base type of the construction, `τ₋₁` in the document. Instead of declaring it as an
arbitrary type of cardinality `μ` and partitioning it into suitable sets of litters afterwards, we
define it as `(Λ × Λ) × μ × κ`, which has the correct cardinality and comes with a natural partition. -/
def base_type : Type* := (Λ × Λ) × μ × κ

@[simp] lemma mk_base_type : #base_type = #μ :=
begin
  simp_rw [base_type, mk_prod, lift_id,
    mul_eq_left (κ_regular.aleph_0_le.trans κ_lt_μ.le) κ_lt_μ.le κ_regular.pos.ne'],
  have ΛΛ_Λ : # Λ * # Λ = # Λ,
  { refine mul_eq_left _ _ _, sorry, sorry, sorry, },
  /- strang difficulties applying lemmas about ℵ₀ -/
  rw ΛΛ_Λ, clear ΛΛ_Λ,
  refine mul_eq_right (κ_regular.aleph_0_le.trans κ_lt_μ.le) _ _,
  transitivity, exact Λ_lt_κ.le, exact κ_lt_μ.le,
  rw cardinal.mk_ne_zero_iff,
  sorry,  /- lemma that a limit ordinal is non-zero and hence non-empty -/
end
/- may want:
  ordinal.omega_le_of_is_limit
  ordinal.card_le_card
-/

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
