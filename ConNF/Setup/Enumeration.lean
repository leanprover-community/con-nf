import ConNF.Aux.Rel
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

noncomputable def empty : Enumeration X where
  bound := 0
  rel _ _ := False
  lt_bound _ h := by cases h; contradiction
  rel_coinjective := by constructor; intros; contradiction

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

def comp (E : Enumeration X) (r : Rel X Y) (hr : r.Coinjective) : Enumeration Y where
  bound := E.bound
  rel := E.rel.comp r
  lt_bound := by
    rintro i ⟨y, x, hy⟩
    exact E.lt_bound i ⟨x, hy.1⟩
  rel_coinjective := E.rel_coinjective.comp hr

instance {G X : Type _} [Group G] [MulAction G X] :
    SMul G (Enumeration X) where
  smul π E := E.invImage (λ x ↦ π⁻¹ • x) (MulAction.injective π⁻¹)

@[simp]
theorem smul_rel {G X : Type _} [Group G] [MulAction G X]
    (π : G) (E : Enumeration X) (i : κ) (x : X) :
    (π • E).rel i x ↔ E.rel i (π⁻¹ • x) :=
  Iff.rfl

instance {G X : Type _} [Group G] [MulAction G X] :
    MulAction G (Enumeration X) where
  one_smul E := by
    ext i x
    · rfl
    · rw [smul_rel, inv_one, one_smul]
  mul_smul π₁ π₂ E := by
    ext i x
    · rfl
    · rw [smul_rel, smul_rel, smul_rel, mul_inv_rev, mul_smul]

theorem mem_smul_iff {G X : Type _} [Group G] [MulAction G X] (x : X) (g : G) (E : Enumeration X) :
    x ∈ g • E ↔ g⁻¹ • x ∈ E :=
  Iff.rfl

-- TODO: Some stuff about the partial order on enumerations and concatenation of enumerations.

end Enumeration

end ConNF
