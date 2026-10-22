module

public import ConNF.Position.Position

/-!
# Injective functions from denied sets

In this file, we construct a mechanism for creating injective functions satisfying particular
constraints.

## Main declarations

* `ConNF.funOfDeny`: An injective function satisfying particular requirements.
-/

@[expose] public noncomputable section

universe u

open Cardinal Ordinal

namespace ConNF

def initialEquiv {X : Type*} : X ≃ (#X).ord.ToType := by
  apply Nonempty.some
  rw [← Cardinal.eq]
  rw [mk_toType, card_ord]

/-- Endow a type `X` with a well-order of smallest possible order type. -/
@[implicit_reducible]
def initialLinearOrder (X : Type*) : LinearOrder X :=
  initialEquiv.linearOrder

theorem initialWellFoundedLT (X : Type*) :
    letI := initialLinearOrder X
    WellFoundedLT X :=
  initialEquiv.wellFoundedLT

theorem initialWellOrder_type {X : Type*} :
    letI := initialLinearOrder X
    letI := initialWellFoundedLT X
    type ((· < ·) : X → X → Prop) = (#X).ord := by
  have := Equiv.type_lt (initialEquiv (X := X))
  rwa [Ordinal.lift_id, Ordinal.lift_id, type_toType] at this

theorem initialWellOrder_card_Iio {X : Type*} :
    letI := initialLinearOrder X
    letI := initialWellFoundedLT X
    ∀ x : X, #{y | y < x} < #X := by
  letI := initialLinearOrder X
  letI := initialWellFoundedLT X
  intro x
  have := type_Iio_lt_type x
  rwa [initialWellOrder_type, lt_ord, card_type] at this

def chooseOfCardLt {X : Type*} {s : Set X} (h : #s < #X) : X :=
  (compl_nonempty_of_mk_lt h).choose

theorem chooseOfCardLt_not_mem {X : Type*} {s : Set X} (h : #s < #X) :
    chooseOfCardLt h ∉ s :=
  (compl_nonempty_of_mk_lt h).choose_spec

variable [Params.{u}]

theorem gtOfDeny_aux {X : Type u} (h₁ : #X ≤ #μ) (deny : X → Set μ)
    (h₂ : ∀ x, #(deny x) < (#μ).ord.cof)
    (x : X) (ih : letI := initialLinearOrder X; (y : X) → y < x → μ) :
    #(({ν | ∃ y h, ν = ih y h}) ∪ {ν | ∃ ξ ∈ deny x, ν ≤ ξ} : Set μ) < #μ := by
  letI := initialLinearOrder X
  letI := initialWellFoundedLT X
  apply (mk_union_le _ _).trans_lt
  refine add_lt_of_lt aleph0_lt_μ.le ?_ ?_
  · refine (mk_le_mk_of_subset (t := ⋃ (y : X) (h : y < x), {ih y h}) ?_).trans_lt ?_
    · rintro _ ⟨y, h, rfl⟩
      simp only [Set.mem_iUnion, Set.mem_singleton_iff]
      exact ⟨y, h, rfl⟩
    apply (mk_biUnion_le_of_le 1 (λ _ _ ↦ (mk_singleton _).le)).trans_lt ?_
    rw [mul_one]
    exact (initialWellOrder_card_Iio _).trans_le h₁
  · apply card_lt_of_μ_bounded
    obtain ⟨ν, hν⟩ := μ_bounded_lt_of_lt_μ_ord_cof (deny x) (h₂ x)
    use ν
    rintro ξ ⟨ζ, hζ, hξ⟩
    exact hξ.trans_lt (hν ζ hζ)

def gtOfDeny {X : Type u} (h₁ : #X ≤ #μ) (deny : X → Set μ) (h₂ : ∀ x, #(deny x) < (#μ).ord.cof)
    (x : X) (ih : letI := initialLinearOrder X; (y : X) → y < x → μ) : μ :=
  chooseOfCardLt (gtOfDeny_aux h₁ deny h₂ x ih)

theorem gtOfDeny_spec {X : Type u} (h₁ : #X ≤ #μ) (deny : X → Set μ)
    (h₂ : ∀ x, #(deny x) < (#μ).ord.cof)
    (x : X) (ih : letI := initialLinearOrder X; (y : X) → y < x → μ) :
    gtOfDeny h₁ deny h₂ x ih ∉ ({ν | ∃ y h, ν = ih y h}) ∪ {ν | ∃ ξ ∈ deny x, ν ≤ ξ} :=
  chooseOfCardLt_not_mem (gtOfDeny_aux h₁ deny h₂ x ih)

def funOfDeny {X : Type u} (h₁ : #X ≤ #μ) (deny : X → Set μ) (h₂ : ∀ x, #(deny x) < (#μ).ord.cof) :
    X → μ :=
  letI := initialLinearOrder X
  letI := initialWellFoundedLT X
  wellFounded_lt.fix (C := fun _ ↦ μ) (fun x ih ↦ gtOfDeny h₁ deny h₂ x ih)

theorem funOfDeny_eq {X : Type u} (h₁ : #X ≤ #μ) (deny : X → Set μ)
    (h₂ : ∀ x, #(deny x) < (#μ).ord.cof) (x : X) :
    funOfDeny h₁ deny h₂ x = gtOfDeny h₁ deny h₂ x (λ y _ ↦ funOfDeny h₁ deny h₂ y) :=
  letI := initialLinearOrder X
  letI := initialWellFoundedLT X
  wellFounded_lt.fix_eq (C := fun _ ↦ μ) (fun x ih ↦ gtOfDeny h₁ deny h₂ x ih) x

theorem funOfDeny_spec {X : Type u} (h₁ : #X ≤ #μ) (deny : X → Set μ)
    (h₂ : ∀ x, #(deny x) < (#μ).ord.cof) (x : X) :
    letI := initialLinearOrder X
    letI := initialWellFoundedLT X
    funOfDeny h₁ deny h₂ x ∉
      ({ν | ∃ y, ∃ _h : y < x, ν = funOfDeny h₁ deny h₂ y}) ∪ {ν | ∃ ξ ∈ deny x, ν ≤ ξ} := by
  rw [funOfDeny_eq]
  exact gtOfDeny_spec h₁ deny h₂ x (λ y _ ↦ funOfDeny h₁ deny h₂ y)

theorem funOfDeny_gt_deny {X : Type u} (h₁ : #X ≤ #μ) (deny : X → Set μ)
    (h₂ : ∀ x, #(deny x) < (#μ).ord.cof) (x : X) (ν : μ) (hν : ν ∈ deny x) :
    ν < funOfDeny h₁ deny h₂ x := by
  have := funOfDeny_spec h₁ deny h₂ x
  contrapose! this
  right
  exact ⟨ν, hν, this⟩

theorem funOfDeny_injective {X : Type u} (h₁ : #X ≤ #μ) (deny : X → Set μ)
    (h₂ : ∀ x, #(deny x) < (#μ).ord.cof) :
    Function.Injective (funOfDeny h₁ deny h₂) := by
  letI := initialLinearOrder X
  letI := initialWellFoundedLT X
  intro x y h
  wlog hxy : x ≤ y
  · exact (this h₁ deny h₂ h.symm (le_of_not_ge hxy)).symm
  have := funOfDeny_spec h₁ deny h₂ y
  contrapose! this
  left
  exact ⟨x, lt_of_le_of_ne hxy this, h.symm⟩

end ConNF
