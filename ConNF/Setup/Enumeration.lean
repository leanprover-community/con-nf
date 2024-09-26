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
  mem E x := x ∈ E.rel.codom

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
## Enumerations from sets
-/

theorem exists_equiv (s : Set X) (hs : Small s) :
    Nonempty ((i : κ) × (s ≃ Set.Iio i)) := by
  rw [Small] at hs
  refine ⟨κEquiv.symm ⟨(#s).ord, ?_⟩, Nonempty.some ?_⟩
  · rwa [Set.mem_Iio, ord_lt_ord]
  · rw [← Cardinal.eq, Set.Iio, κ_card_Iio_eq, Equiv.apply_symm_apply, card_ord]

noncomputable def ofSet (s : Set X) (hs : Small s) : Enumeration X where
  bound := (exists_equiv s hs).some.1
  rel i x := ∃ h, i = (exists_equiv s hs).some.2 ⟨x, h⟩
  lt_bound := by
    rintro _ ⟨x, h, rfl⟩
    exact ((exists_equiv s hs).some.2 ⟨x, h⟩).prop
  rel_coinjective := by
    constructor
    rintro x y i ⟨hx, hix⟩ ⟨hy, hiy⟩
    rw [hix] at hiy
    cases (exists_equiv s hs).some.2.injective (Subtype.coe_injective hiy)
    rfl

@[simp]
theorem mem_ofSet_iff (s : Set X) (hs : Small s) (x : X) :
    x ∈ ofSet s hs ↔ x ∈ s := by
  constructor
  · rintro ⟨i, hx, _⟩
    exact hx
  · intro h
    exact ⟨(exists_equiv s hs).some.2 ⟨x, h⟩, h, rfl⟩

@[simp]
theorem ofSet_coe (s : Set X) (hs : Small s) :
    (ofSet s hs : Set X) = s := by
  ext x
  rw [← mem_ofSet_iff s hs]
  rfl

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

@[simp]
theorem mem_smul {G X : Type _} [Group G] [MulAction G X]
    (π : G) (E : Enumeration X) (x : X) :
    x ∈ π • E ↔ π⁻¹ • x ∈ E :=
  Iff.rfl

open scoped Pointwise in
@[simp]
theorem smul_rel_codom {G X : Type _} [Group G] [MulAction G X]
    (π : G) (E : Enumeration X) :
    (π • E).rel.codom = π • E.rel.codom := by
  ext x
  constructor
  · rintro ⟨i, h⟩
    exact ⟨π⁻¹ • x, ⟨i, h⟩, smul_inv_smul π x⟩
  · rintro ⟨x, ⟨i, h⟩, rfl⟩
    use i
    rwa [smul_rel, inv_smul_smul]

open scoped Pointwise in
@[simp]
theorem smul_coe {G X : Type _} [Group G] [MulAction G X]
    (π : G) (E : Enumeration X) :
    ((π • E : Enumeration X) : Set X) = π • (E : Set X) :=
  smul_rel_codom π E

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

/-!
## Concatenation of enumerations
-/

noncomputable instance : Add (Enumeration X) where
  add E F := {
    bound := E.bound + F.bound
    rel := E.rel ⊔ Rel.comp (E.bound + ·).graph.inv F.rel
    lt_bound := by
      rintro i ⟨x, hi | ⟨j, rfl, hjx⟩⟩
      · exact (E.lt_bound i ⟨x, hi⟩).trans_le (κ_le_add E.bound F.bound)
      · rw [add_lt_add_iff_left]
        exact F.lt_bound j ⟨x, hjx⟩
    rel_coinjective := by
      constructor
      rintro x y i (hix | ⟨j, hj, hjx⟩) (hiy | ⟨k, hk, hky⟩)
      · exact E.rel_coinjective.coinjective hix hiy
      · cases hk
        have := E.lt_bound _ ⟨x, hix⟩
        rw [add_lt_iff_neg_left] at this
        cases (κ_zero_le k).not_lt this
      · cases hj
        have := E.lt_bound _ ⟨y, hiy⟩
        rw [add_lt_iff_neg_left] at this
        cases (κ_zero_le j).not_lt this
      · cases hj
        simp only [Rel.inv, flip, Function.graph_def, add_right_inj] at hk
        cases hk
        exact F.rel_coinjective.coinjective hjx hky
  }

@[simp]
theorem add_bound (E F : Enumeration X) :
    (E + F).bound = E.bound + F.bound :=
  rfl

theorem rel_add_iff {E F : Enumeration X} (i : κ) (x : X) :
    (E + F).rel i x ↔ E.rel i x ∨ ∃ j, E.bound + j = i ∧ F.rel j x :=
  Iff.rfl

@[simp]
theorem mem_add_iff {E F : Enumeration X} (x : X) :
    x ∈ E + F ↔ x ∈ E ∨ x ∈ F := by
  simp only [mem_iff, Rel.codom, Set.mem_setOf, rel_add_iff]
  constructor
  · rintro ⟨i, (hi | ⟨j, rfl, hj⟩)⟩
    · exact Or.inl ⟨i, hi⟩
    · exact Or.inr ⟨j, hj⟩
  · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · exact ⟨i, Or.inl hi⟩
    · exact ⟨_, Or.inr ⟨j, rfl, hj⟩⟩

@[simp]
theorem coe_add {E F : Enumeration X} :
    (E + F : Set X) = (E : Set X) ∪ F := by
  ext x
  exact mem_add_iff x

@[simp]
theorem add_empty (E : Enumeration X) :
    E + .empty = E := by
  ext i x
  · rw [add_bound, empty, add_zero]
  · simp only [empty, rel_add_iff, and_false, exists_const, or_false]

-- TODO: Some stuff about the partial order on enumerations and concatenation of enumerations.

end Enumeration

end ConNF
