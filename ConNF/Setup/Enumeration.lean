import ConNF.Aux.Rel
import ConNF.Setup.Path
import ConNF.Setup.Small

/-!
# Enumerations

In this file, we define enumerations of a type.

## Main declarations

* `ConNF.Enumeration`: The type family of enumerations.
-/

universe u

open Cardinal

namespace ConNF

variable [Params.{u}] {X Y : Type u}

@[ext]
structure Enumeration (X : Type u) where
  bound : κ
  rel : Rel κ X
  lt_bound : ∀ i ∈ rel.dom, i < bound
  rel_coinjective : rel.Coinjective

variable {E F G : Enumeration X}

namespace Enumeration

instance : CoeTC (Enumeration X) (Set X) where
  coe E := E.rel.codom

instance : Membership X (Enumeration X) where
  mem x E := x ∈ E.rel.codom

theorem mem_iff (x : X) (E : Enumeration X) :
    x ∈ E ↔ x ∈ E.rel.codom :=
  Iff.rfl

theorem dom_small (E : Enumeration X) :
    Small E.rel.dom :=
  (iio_small E.bound).mono E.lt_bound

theorem coe_small (E : Enumeration X) :
    Small (E : Set X) :=
  small_codom_of_small_dom E.rel_coinjective E.dom_small

theorem graph'_small (E : Enumeration X) :
    Small E.rel.graph' :=
  small_graph' E.dom_small E.coe_small

noncomputable def singleton (x : X) : Enumeration X where
  bound := 1
  rel i y := i = 0 ∧ y = x
  lt_bound i h := by
    have : i = 0 := by simpa only [Rel.dom, exists_eq_right, Set.setOf_eq_eq_singleton,
      Set.mem_singleton_iff] using h
    rw [this, κEquiv_lt, ← Subtype.coe_lt_coe, κEquiv_ofNat, κEquiv_ofNat, Nat.cast_zero,
      Nat.cast_one]
    exact zero_lt_one
  rel_coinjective := by
    constructor
    cc

@[simp]
theorem mem_singleton_iff (x y : X) :
    y ∈ singleton x ↔ y = x := by
  constructor
  · rintro ⟨_, _, h⟩
    exact h
  · intro h
    exact ⟨0, rfl, h⟩

theorem singleton_injective : Function.Injective (singleton : X → Enumeration X) := by
  intro x y h
  have := mem_singleton_iff y x
  rw [← h, mem_singleton_iff] at this
  exact this.mp rfl

/-!
## Cardinality bounds on enumerations
-/

end Enumeration

theorem card_enumeration_ge (X : Type u) : #X ≤ #(Enumeration X) :=
  mk_le_of_injective Enumeration.singleton_injective

def enumerationEmbedding (X : Type u) : Enumeration X ↪ κ × {s : Set (κ × X) | Small s} where
  toFun E := (E.bound, ⟨E.rel.graph', E.graph'_small⟩)
  inj' := by
    intro E F h
    rw [Prod.mk.injEq, Subtype.mk.injEq] at h
    exact Enumeration.ext h.1 (Rel.graph'_injective h.2)

theorem card_enumeration_le (h : #X ≤ #μ) : #(Enumeration X) ≤ #μ := by
  apply (mk_le_of_injective (enumerationEmbedding X).injective).trans
  rw [mk_prod, lift_id, lift_id]
  apply mul_le_of_le aleph0_lt_μ.le κ_le_μ
  apply card_small_le
  rw [mk_prod, lift_id, lift_id]
  exact mul_le_of_le aleph0_lt_μ.le κ_le_μ h

theorem card_enumeration_lt (h : #X < #μ) : #(Enumeration X) < #μ := by
  apply (mk_le_of_injective (enumerationEmbedding X).injective).trans_lt
  rw [mk_prod, lift_id, lift_id]
  apply mul_lt_of_lt aleph0_lt_μ.le κ_lt_μ
  apply (mk_subtype_le _).trans_lt
  rw [mk_set]
  apply μ_isStrongLimit.2
  rw [mk_prod, lift_id, lift_id]
  exact mul_lt_of_lt aleph0_lt_μ.le κ_lt_μ h

theorem card_enumeration_eq (h : #X = #μ) : #(Enumeration X) = #μ :=
  le_antisymm (card_enumeration_le h.le) (h.symm.le.trans (card_enumeration_ge X))

namespace Enumeration

/-!
## Operations on enumerations
-/

def image (E : Enumeration X) (f : X → Y) : Enumeration Y where
  bound := E.bound
  rel i y := ∃ x, E.rel i x ∧ f x = y
  lt_bound := by
    rintro i ⟨_, x, hi, rfl⟩
    exact E.lt_bound i ⟨x, hi⟩
  rel_coinjective := by
    constructor
    rintro i _ _ ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂, rfl⟩
    rw [E.rel_coinjective.coinjective hx₁ hx₂]

theorem image_rel {f : X → Y} (i : κ) (y : Y) :
    (E.image f).rel i y ↔ ∃ x, E.rel i x ∧ f x = y :=
  Iff.rfl

@[simp]
theorem mem_image {f : X → Y} (y : Y) :
    y ∈ E.image f ↔ y ∈ f '' E := by
  constructor
  · rintro ⟨i, x, hx, rfl⟩
    exact ⟨x, ⟨i, hx⟩, rfl⟩
  · rintro ⟨x, ⟨i, hx⟩, rfl⟩
    exact ⟨i, x, hx, rfl⟩

def invImage (E : Enumeration X) (f : Y → X) (hf : f.Injective) : Enumeration Y where
  bound := E.bound
  rel i y := E.rel i (f y)
  lt_bound := by
    rintro i ⟨y, hy⟩
    exact E.lt_bound i ⟨f y, hy⟩
  rel_coinjective := by
    constructor
    intro i y₁ y₂ h₁ h₂
    exact hf <| E.rel_coinjective.coinjective h₁ h₂

theorem invImage_rel {f : Y → X} {hf : f.Injective} (i : κ) (y : Y) :
    (E.invImage f hf).rel i y ↔ E.rel i (f y) :=
  Iff.rfl

@[simp]
theorem mem_invImage {f : Y → X} {hf : f.Injective} (y : Y) :
    y ∈ E.invImage f hf ↔ f y ∈ E :=
  Iff.rfl

/-!
## Enumerations over paths
-/

instance (X : Type u) (α β : TypeIndex) :
    Derivative (Enumeration (α ↝ ⊥ × X)) (Enumeration (β ↝ ⊥ × X)) α β where
  deriv E A := E.invImage (λ x ↦ (x.1 ⇗ A, x.2))
    (λ x y h ↦ Prod.ext (Path.deriv_right_injective
      ((Prod.mk.injEq _ _ _ _).mp h).1) ((Prod.mk.injEq _ _ _ _).mp h).2)

instance (X : Type u) (α β : TypeIndex) :
    Coderivative (Enumeration (β ↝ ⊥ × X)) (Enumeration (α ↝ ⊥ × X)) α β where
  coderiv E A := E.image (λ x ↦ (x.1 ⇗ A, x.2))

instance (X : Type u) (α : TypeIndex) :
    BotDerivative (Enumeration (α ↝ ⊥ × X)) (Enumeration X) α where
  botDeriv E A := E.invImage (λ x ↦ (A, x)) (Prod.mk.inj_left A)
  botSderiv E := E.invImage (λ x ↦ (Path.nil ↘., x)) (Prod.mk.inj_left (Path.nil ↘.))
  botDeriv_single E h := by
    cases α using WithBot.recBotCoe with
    | bot => cases lt_irrefl ⊥ h
    | coe => rfl

theorem ext_path {X : Type u} {α : TypeIndex} {E F : Enumeration (α ↝ ⊥ × X)}
    (h : ∀ A, E ⇘. A = F ⇘. A) :
    E = F := by
  ext i x
  · have := congr_arg bound (h (Path.nil ↘.))
    exact this
  · have := congr_arg rel (h x.1)
    exact iff_of_eq (congr_fun₂ this i x.2)

-- TODO: Some stuff about the partial order on enumerations and concatenation of enumerations.

end Enumeration

end ConNF
