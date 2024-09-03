import Mathlib.Data.Rel

open Set
open scoped symmDiff

namespace Rel

variable {α β : Type _}

-- Note the backward composition style of Rel.comp!
@[inherit_doc]
scoped infixr:80 " • " => Rel.comp

@[mk_iff]
structure Injective (r : Rel α β) : Prop where
  injective : ∀ ⦃x₁ x₂ y⦄, r x₁ y → r x₂ y → x₁ = x₂

@[mk_iff]
structure Coinjective (r : Rel α β) : Prop where
  coinjective : ∀ ⦃y₁ y₂ x⦄, r x y₁ → r x y₂ → y₁ = y₂

@[mk_iff]
structure Surjective (r : Rel α β) : Prop where
  surjective : ∀ y, ∃ x, r x y

@[mk_iff]
structure Cosurjective (r : Rel α β) : Prop where
  cosurjective : ∀ x, ∃ y, r x y

@[mk_iff]
structure Functional (r : Rel α β) extends r.Coinjective, r.Cosurjective : Prop

@[mk_iff]
structure Cofunctional (r : Rel α β) extends r.Injective, r.Surjective : Prop

@[mk_iff]
structure OneOne (r : Rel α β) extends r.Injective, r.Coinjective : Prop

@[mk_iff]
structure Bijective (r : Rel α β) extends r.Functional, r.Cofunctional : Prop

@[mk_iff]
structure CodomEqDom (r : Rel α α) : Prop where
  codom_eq_dom : r.codom = r.dom

@[mk_iff]
structure Permutative (r : Rel α α) extends r.OneOne, r.CodomEqDom : Prop

theorem CodomEqDom.mem_dom {r : Rel α α} (h : r.CodomEqDom) {x y : α} (hxy : r x y) :
    y ∈ r.dom := by
  rw [← h.codom_eq_dom]
  exact ⟨x, hxy⟩

theorem CodomEqDom.mem_codom {r : Rel α α} (h : r.CodomEqDom) {x y : α} (hxy : r x y) :
    x ∈ r.codom := by
  rw [h.codom_eq_dom]
  exact ⟨y, hxy⟩

/-- An elementary description of the property `CodomEqDom`. -/
theorem codomEqDom_iff' (r : Rel α α) :
    r.CodomEqDom ↔ (∀ x y, r x y → ∃ z, r y z) ∧ (∀ x y, r x y → ∃ z, r z x) := by
  constructor
  · rintro ⟨h⟩
    rw [Set.ext_iff] at h
    constructor
    · intro x y hxy
      exact (h y).mp ⟨x, hxy⟩
    · intro x y hxy
      exact (h x).mpr ⟨y, hxy⟩
  · rintro ⟨h₁, h₂⟩
    constructor
    ext x
    constructor
    · intro ⟨y, hxy⟩
      exact h₁ y x hxy
    · intro ⟨y, hxy⟩
      exact h₂ x y hxy

theorem OneOne.inv {r : Rel α β} (h : r.OneOne) : r.inv.OneOne :=
  ⟨⟨h.coinjective⟩, ⟨h.injective⟩⟩

@[simp]
theorem inv_injective_iff {r : Rel α β} :
    r.inv.Injective ↔ r.Coinjective :=
  ⟨λ h ↦ ⟨h.injective⟩, λ h ↦ ⟨h.coinjective⟩⟩

@[simp]
theorem inv_coinjective_iff {r : Rel α β} :
    r.inv.Coinjective ↔ r.Injective :=
  inv_injective_iff.symm

@[simp]
theorem inv_dom {r : Rel α β} :
    r.inv.dom = r.codom :=
  rfl

@[simp]
theorem inv_codom {r : Rel α β} :
    r.inv.codom = r.dom :=
  rfl

@[simp]
theorem inv_image {r : Rel α β} {s : Set β} :
    r.inv.image s = r.preimage s :=
  rfl

@[simp]
theorem inv_preimage {r : Rel α β} {s : Set α} :
    r.inv.preimage s = r.image s :=
  rfl

theorem Injective.image_injective {r : Rel α β} (h : r.Injective) {s t : Set α}
    (hs : s ⊆ r.dom) (ht : t ⊆ r.dom) (hst : r.image s = r.image t) : s = t := by
  rw [Set.ext_iff] at hst ⊢
  intro x
  constructor
  · intro hx
    obtain ⟨y, hxy⟩ := hs hx
    obtain ⟨z, hz, hzy⟩ := (hst y).mp ⟨x, hx, hxy⟩
    cases h.injective hxy hzy
    exact hz
  · intro hx
    obtain ⟨y, hxy⟩ := ht hx
    obtain ⟨z, hz, hzy⟩ := (hst y).mpr ⟨x, hx, hxy⟩
    cases h.injective hxy hzy
    exact hz

theorem subset_image_of_preimage_subset {r : Rel α β} {s : Set β} (hs : s ⊆ r.codom) (t : Set α) :
    r.preimage s ⊆ t → s ⊆ r.image t := by
  intro hst y hy
  obtain ⟨x, hx⟩ := hs hy
  exact ⟨x, hst ⟨y, hy, hx⟩, hx⟩

theorem Injective.preimage_subset_of_subset_image {r : Rel α β} (h : r.Injective)
    (s : Set β) (t : Set α) :
    s ⊆ r.image t → r.preimage s ⊆ t := by
  rintro hst x ⟨y, hy, hxy⟩
  obtain ⟨z, hz, hzy⟩ := hst hy
  cases h.injective hzy hxy
  exact hz

theorem Injective.preimage_subset_iff_subset_image {r : Rel α β} (h : r.Injective)
    (s : Set β) (hs : s ⊆ r.codom) (t : Set α) :
    r.preimage s ⊆ t ↔ s ⊆ r.image t :=
  ⟨subset_image_of_preimage_subset hs t, preimage_subset_of_subset_image h s t⟩

theorem OneOne.preimage_eq_iff_image_eq {r : Rel α β} (h : r.OneOne)
    {s : Set β} (hs : s ⊆ r.codom) {t : Set α} (ht : t ⊆ r.dom) :
    r.preimage s = t ↔ r.image t = s := by
  have h₁ := h.preimage_subset_iff_subset_image s hs t
  have h₂ := h.inv.preimage_subset_iff_subset_image t ht s
  rw [preimage_inv, inv_image] at h₂
  rw [subset_antisymm_iff, subset_antisymm_iff, h₁, h₂, and_comm]

theorem CodomEqDom.inv {r : Rel α α} (h : r.CodomEqDom) : r.inv.CodomEqDom := by
  rw [codomEqDom_iff] at h ⊢
  exact h.symm

theorem Permutative.inv {r : Rel α α} (h : r.Permutative) : r.inv.Permutative :=
  ⟨h.toOneOne.inv, h.toCodomEqDom.inv⟩

theorem Permutative.inv_dom {r : Rel α α} (h : r.Permutative) : r.inv.dom = r.dom :=
  h.codom_eq_dom

/-- An alternative spelling of `Rel.graph` that is useful for proving inequalities of cardinals. -/
def graph' (r : Rel α β) : Set (α × β) :=
  r.uncurry

theorem le_of_graph'_subset {r s : Rel α β} (h : r.graph' ⊆ s.graph') :
    r ≤ s :=
  λ x y h' ↦ mem_of_subset_of_mem (a := (x, y)) h h'

theorem graph'_subset_of_le {r s : Rel α β} (h : r ≤ s) :
    r.graph' ⊆ s.graph' :=
  λ z ↦ h z.1 z.2

theorem graph'_subset_iff {r s : Rel α β} :
    r.graph' ⊆ s.graph' ↔ r ≤ s :=
  ⟨le_of_graph'_subset, graph'_subset_of_le⟩

theorem graph'_injective :
    Function.Injective (Rel.graph' : Rel α β → Set (α × β)) :=
  λ _ _ h ↦ le_antisymm (le_of_graph'_subset h.le) (le_of_graph'_subset h.symm.le)

@[simp]
theorem image_dom {r : Rel α β} :
    r.image r.dom = r.codom :=
  preimage_eq_codom_of_domain_subset r subset_rfl

@[simp]
theorem preimage_codom {r : Rel α β} :
    r.preimage r.codom = r.dom :=
  image_dom

theorem preimage_subset_dom (r : Rel α β) (t : Set β) :
    r.preimage t ⊆ r.dom := by
  rintro x ⟨y, _, h⟩
  exact ⟨y, h⟩

theorem image_subset_codom (r : Rel α β) (s : Set α) :
    r.image s ⊆ r.codom :=
  r.inv.preimage_subset_dom s

theorem image_empty_of_disjoint_dom {r : Rel α β} {s : Set α} (h : Disjoint r.dom s) :
    r.image s = ∅ := by
  rw [eq_empty_iff_forall_not_mem]
  rw [disjoint_iff_forall_ne] at h
  rintro y ⟨x, hx₁, hx₂⟩
  exact h ⟨y, hx₂⟩ hx₁ rfl

theorem Injective.image_diff {r : Rel α β} (h : r.Injective) (s t : Set α) :
    r.image (s \ t) = r.image s \ r.image t := by
  ext y
  constructor
  · rintro ⟨x, hx₁, hx₂⟩
    refine ⟨⟨x, hx₁.1, hx₂⟩, ?_⟩
    rintro ⟨z, hz₁, hz₂⟩
    cases h.injective hx₂ hz₂
    exact hx₁.2 hz₁
  · rintro ⟨⟨x, hx₁, hx₂⟩, hy⟩
    refine ⟨x, ⟨hx₁, ?_⟩, hx₂⟩
    intro hx
    exact hy ⟨x, hx, hx₂⟩

theorem Injective.image_symmDiff {r : Rel α β} (h : r.Injective) (s t : Set α) :
    r.image (s ∆ t) = r.image s ∆ r.image t := by
  rw [Set.symmDiff_def, Set.symmDiff_def, image_union, h.image_diff, h.image_diff]

@[simp]
theorem sup_inv {r s : Rel α β} :
    (r ⊔ s).inv = r.inv ⊔ s.inv :=
  rfl

theorem sup_apply {r s : Rel α β} {x : α} {y : β} :
    (r ⊔ s) x y ↔ r x y ∨ s x y :=
  Iff.rfl

@[simp]
theorem sup_dom {r s : Rel α β} :
    (r ⊔ s).dom = r.dom ∪ s.dom := by
  ext x
  simp only [dom, mem_setOf_eq, mem_union, sup_apply]
  exact exists_or

@[simp]
theorem sup_codom {r s : Rel α β} :
    (r ⊔ s).codom = r.codom ∪ s.codom :=
  sup_dom

@[simp]
theorem sup_image {r s : Rel α β} (t : Set α) :
    (r ⊔ s).image t = r.image t ∪ s.image t := by
  ext y
  constructor
  · rintro ⟨x, hx₁, hx₂ | hx₂⟩
    · exact Or.inl ⟨x, hx₁, hx₂⟩
    · exact Or.inr ⟨x, hx₁, hx₂⟩
  · rintro (⟨x, hx₁, hx₂⟩ | ⟨x, hx₁, hx₂⟩)
    · exact ⟨x, hx₁, Or.inl hx₂⟩
    · exact ⟨x, hx₁, Or.inr hx₂⟩

theorem sup_injective {r s : Rel α β} (hr : r.Injective) (hs : s.Injective)
    (h : Disjoint r.codom s.codom) : (r ⊔ s).Injective := by
  constructor
  rintro x₁ x₂ y (h₁ | h₁) (h₂ | h₂)
  · exact hr.injective h₁ h₂
  · cases h.ne_of_mem ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ rfl
  · cases h.ne_of_mem ⟨x₂, h₂⟩ ⟨x₁, h₁⟩ rfl
  · exact hs.injective h₁ h₂

theorem sup_coinjective {r s : Rel α β} (hr : r.Coinjective) (hs : s.Coinjective)
    (h : Disjoint r.dom s.dom) : (r ⊔ s).Coinjective :=
  inv_coinjective_iff.mpr <| sup_injective (inv_injective_iff.mpr hr) (inv_injective_iff.mpr hs) h

theorem sup_codomEqDom {r s : Rel α α} (hr : r.CodomEqDom) (hs : s.CodomEqDom) :
    (r ⊔ s).CodomEqDom :=
  ⟨sup_codom.trans <| hr.codom_eq_dom ▸ hs.codom_eq_dom ▸ sup_dom.symm⟩

theorem sup_permutative {r s : Rel α α} (hr : r.Permutative) (hs : s.Permutative)
    (h : Disjoint r.dom s.dom) : (r ⊔ s).Permutative :=
  ⟨⟨sup_injective hr.toInjective hs.toInjective (hr.codom_eq_dom ▸ hs.codom_eq_dom ▸ h),
    sup_coinjective hr.toCoinjective hs.toCoinjective h⟩,
    sup_codomEqDom hr.toCodomEqDom hs.toCodomEqDom⟩

-- Compare Mathlib.Data.Rel and Mathlib.Logic.Relator.

end Rel
