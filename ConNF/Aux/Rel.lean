import Mathlib.Data.Rel
import Mathlib.Order.Chain

open Set
open scoped symmDiff

namespace Rel

variable {α β γ : Type _}

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

theorem CodomEqDom.dom_union_codom {r : Rel α α} (h : r.CodomEqDom) :
    r.dom ∪ r.codom = r.dom := by
  rw [h.codom_eq_dom, union_self]

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

theorem inv_injective : Function.Injective (inv : Rel α β → Rel β α) := by
  intro r s h
  ext a b : 2
  exact congr_fun₂ h b a

@[simp]
theorem inv_inj {r s : Rel α β} : r.inv = s.inv ↔ r = s :=
  ⟨λ h ↦ inv_injective h, λ h ↦ h ▸ rfl⟩

@[simp]
theorem inv_injective_iff {r : Rel α β} :
    r.inv.Injective ↔ r.Coinjective :=
  ⟨λ h ↦ ⟨h.injective⟩, λ h ↦ ⟨h.coinjective⟩⟩

@[simp]
theorem inv_coinjective_iff {r : Rel α β} :
    r.inv.Coinjective ↔ r.Injective :=
  inv_injective_iff.symm

@[simp]
theorem inv_surjective_iff {r : Rel α β} :
    r.inv.Surjective ↔ r.Cosurjective :=
  ⟨λ h ↦ ⟨h.surjective⟩, λ h ↦ ⟨h.cosurjective⟩⟩

@[simp]
theorem inv_cosurjective_iff {r : Rel α β} :
    r.inv.Cosurjective ↔ r.Surjective :=
  inv_surjective_iff.symm

@[simp]
theorem inv_functional_iff {r : Rel α β} :
    r.inv.Functional ↔ r.Cofunctional :=
  ⟨λ h ↦ ⟨inv_coinjective_iff.mp h.toCoinjective, inv_cosurjective_iff.mp h.toCosurjective⟩,
    λ h ↦ ⟨inv_injective_iff.mp h.toInjective, inv_surjective_iff.mp h.toSurjective⟩⟩

@[simp]
theorem inv_cofunctional_iff {r : Rel α β} :
    r.inv.Cofunctional ↔ r.Functional :=
  inv_functional_iff.symm

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

theorem comp_inv {r : Rel α β} {s : Rel β γ} :
    (r.comp s).inv = s.inv.comp r.inv := by
  ext c a
  simp only [inv, flip, comp]
  tauto

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

theorem Injective.comp {r : Rel α β} {s : Rel β γ} (hr : r.Injective) (hs : s.Injective) :
    (r.comp s).Injective := by
  constructor
  rintro a₁ a₂ c ⟨b₁, hr₁, hs₁⟩ ⟨b₂, hr₂, hs₂⟩
  cases hs.injective hs₁ hs₂
  exact hr.injective hr₁ hr₂

theorem Coinjective.comp {r : Rel α β} {s : Rel β γ} (hr : r.Coinjective) (hs : s.Coinjective) :
    (r.comp s).Coinjective := by
  rw [← inv_injective_iff, comp_inv]
  exact Injective.comp (inv_injective_iff.mpr hs) (inv_injective_iff.mpr hr)

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

theorem image_eq_of_le_of_le {r s : Rel α β} (h : r ≤ s) {t : Set α} (ht : ∀ x ∈ t, s x ≤ r x) :
    r.image t = s.image t := by
  ext y
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨x, hx, h x y hy⟩
  · rintro ⟨x, hx, hy⟩
    exact ⟨x, hx, ht x hx y hy⟩

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

theorem sup_oneOne {r s : Rel α β} (hr : r.OneOne) (hs : s.OneOne)
    (h₁ : Disjoint r.dom s.dom) (h₂ : Disjoint r.codom s.codom) : (r ⊔ s).OneOne :=
  ⟨sup_injective hr.toInjective hs.toInjective h₂,
    sup_coinjective hr.toCoinjective hs.toCoinjective h₁⟩

theorem sup_codomEqDom {r s : Rel α α} (hr : r.CodomEqDom) (hs : s.CodomEqDom) :
    (r ⊔ s).CodomEqDom :=
  ⟨sup_codom.trans <| hr.codom_eq_dom ▸ hs.codom_eq_dom ▸ sup_dom.symm⟩

theorem sup_permutative {r s : Rel α α} (hr : r.Permutative) (hs : s.Permutative)
    (h : Disjoint r.dom s.dom) : (r ⊔ s).Permutative :=
  ⟨sup_oneOne hr.toOneOne hs.toOneOne h (hr.codom_eq_dom ▸ hs.codom_eq_dom ▸ h),
    sup_codomEqDom hr.toCodomEqDom hs.toCodomEqDom⟩

@[simp]
theorem inv_le_inv_iff {r s : Rel α β} :
    r.inv ≤ s.inv ↔ r ≤ s := by
  constructor
  · intro h x y
    exact h y x
  · intro h y x
    exact h x y

@[simp]
theorem iSup_apply_iff {T : Type _} {r : T → Rel α β} (x : α) (y : β) :
    (⨆ t, r t) x y ↔ ∃ t, r t x y := by
  constructor
  · rintro ⟨_, ⟨⟨_, ⟨_, t, rfl⟩, rfl⟩, rfl⟩, ht⟩
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨_, ⟨⟨_, ⟨_, t, rfl⟩, rfl⟩, rfl⟩, ht⟩

@[simp]
theorem biSup_apply_iff {T : Type _} {r : T → Rel α β} {s : Set T} (x : α) (y : β) :
    (⨆ t ∈ s, r t) x y ↔ ∃ t ∈ s, r t x y := by
  have := iSup_apply_iff (r := λ t : s ↦ r t) x y
  simp only [iSup_subtype'', Subtype.exists, exists_prop] at this
  exact this

theorem iSup_dom {T : Type _} (r : T → Rel α β) :
    (⨆ t, r t).dom = ⋃ t, (r t).dom := by
  simp only [dom, iSup_apply_iff, Set.ext_iff, mem_setOf_eq, mem_iUnion]
  exact λ x ↦ exists_comm

theorem biSup_dom {T : Type _} (r : T → Rel α β) (s : Set T) :
    (⨆ t ∈ s, r t).dom = ⋃ t ∈ s, (r t).dom := by
  have := iSup_dom (λ t : s ↦ r t)
  rwa [iSup_subtype'', iUnion_coe_set] at this

theorem isChain_inv {T : Type _} {r : T → Rel α β} (h : IsChain (· ≤ ·) (Set.range r)) :
    IsChain (· ≤ ·) (Set.range (λ t ↦ (r t).inv)) := by
  rintro _ ⟨t₁, rfl⟩ _ ⟨t₂, rfl⟩ _
  dsimp only
  rw [inv_le_inv_iff, inv_le_inv_iff]
  apply h.total ⟨t₁, rfl⟩ ⟨t₂, rfl⟩

theorem iSup_inv {T : Type _} {r : T → Rel α β} :
    (⨆ t, (r t).inv) = (⨆ t, r t).inv := by
  apply le_antisymm <;>
  · rintro x y h
    simp only [inv, iSup_apply_iff, flip] at h ⊢
    exact h

theorem iSup_injective_of_isChain {T : Type _} {r : T → Rel α β}
    (h₁ : ∀ t, (r t).Injective) (h₂ : IsChain (· ≤ ·) (Set.range r)) :
    (⨆ t, r t).Injective := by
  constructor
  intro x₁ x₂ y hx₁ hx₂
  rw [iSup_apply_iff] at hx₁ hx₂
  obtain ⟨t₁, hx₁⟩ := hx₁
  obtain ⟨t₂, hx₂⟩ := hx₂
  obtain (h | h) := h₂.total ⟨t₁, rfl⟩ ⟨t₂, rfl⟩
  · exact (h₁ t₂).injective (h x₁ y hx₁) hx₂
  · exact (h₁ t₁).injective hx₁ (h x₂ y hx₂)

theorem iSup_coinjective_of_isChain {T : Type _} {r : T → Rel α β}
    (h₁ : ∀ t, (r t).Coinjective) (h₂ : IsChain (· ≤ ·) (Set.range r)) :
    (⨆ t, r t).Coinjective := by
  have := iSup_injective_of_isChain (r := λ t ↦ (r t).inv) ?_ (isChain_inv h₂)
  · rwa [iSup_inv, inv_injective_iff] at this
  · intro t
    rw [inv_injective_iff]
    exact h₁ t

theorem iSup_codomEqDom_of_isChain {T : Type _} {r : T → Rel α α} (h : ∀ t, (r t).CodomEqDom) :
    (⨆ t, r t).CodomEqDom := by
  simp only [codomEqDom_iff'] at h ⊢
  simp only [iSup_apply_iff]
  constructor
  · rintro x y ⟨t, ht⟩
    obtain ⟨u, hu⟩ := (h t).1 x y ht
    exact ⟨u, t, hu⟩
  · rintro x y ⟨t, ht⟩
    obtain ⟨u, hu⟩ := (h t).2 x y ht
    exact ⟨u, t, hu⟩

theorem iSup_oneOne_of_isChain {T : Type _} {r : T → Rel α β}
    (h₁ : ∀ t, (r t).OneOne) (h₂ : IsChain (· ≤ ·) (Set.range r)) :
    (⨆ t, r t).OneOne :=
  ⟨iSup_injective_of_isChain (λ t ↦ (h₁ t).toInjective) h₂,
    iSup_coinjective_of_isChain (λ t ↦ (h₁ t).toCoinjective) h₂⟩

theorem iSup_permutative_of_isChain {T : Type _} {r : T → Rel α α}
    (h₁ : ∀ t, (r t).Permutative) (h₂ : IsChain (· ≤ ·) (Set.range r)) :
    (⨆ t, r t).Permutative :=
  ⟨iSup_oneOne_of_isChain (λ t ↦ (h₁ t).toOneOne) h₂,
    iSup_codomEqDom_of_isChain (λ t ↦ (h₁ t).toCodomEqDom)⟩

theorem biSup_permutative_of_isChain {T : Type _} {r : T → Rel α α} {s : Set T}
    (h₁ : ∀ t ∈ s, (r t).Permutative) (h₂ : IsChain (· ≤ ·) (r '' s)) :
    (⨆ t ∈ s, r t).Permutative := by
  have := iSup_permutative_of_isChain (T := s) (λ t ↦ h₁ t t.prop) ?_
  · rwa [iSup_subtype] at this
  · rwa [image_eq_range] at h₂

noncomputable def toFunction (r : Rel α β) (hr : r.Functional) : α → β :=
  λ a ↦ (hr.cosurjective a).choose

theorem toFunction_rel (r : Rel α β) (hr : r.Functional) (a : α) :
    r a (r.toFunction hr a) :=
  (hr.cosurjective a).choose_spec

theorem toFunction_eq_iff (r : Rel α β) (hr : r.Functional) (a : α) (b : β) :
    r.toFunction hr a = b ↔ r a b := by
  constructor
  · rintro rfl
    exact toFunction_rel r hr a
  · intro h
    exact hr.coinjective (toFunction_rel r hr a) h

noncomputable def toEquiv (r : Rel α β) (hr : r.Bijective) : α ≃ β where
  toFun := r.toFunction hr.toFunctional
  invFun := r.inv.toFunction (inv_functional_iff.mpr hr.toCofunctional)
  left_inv a := by
    rw [toFunction_eq_iff]
    exact toFunction_rel r _ a
  right_inv b := by
    rw [toFunction_eq_iff]
    exact toFunction_rel r.inv _ b

theorem toEquiv_rel (r : Rel α β) (hr : r.Bijective) (a : α) :
    r a (r.toEquiv hr a) :=
  toFunction_rel r hr.toFunctional a

theorem toEquiv_eq_iff (r : Rel α β) (hr : r.Bijective) (a : α) (b : β) :
    r.toEquiv hr a = b ↔ r a b :=
  toFunction_eq_iff r hr.toFunctional a b

theorem toFunction_image (r : Rel α β) (hr : r.Functional) (s : Set α) :
    r.toFunction hr '' s = r.image s := by
  ext y
  constructor
  · rintro ⟨x, hx, hy⟩
    rw [toFunction_eq_iff] at hy
    exact ⟨x, hx, hy⟩
  · rintro ⟨x, hx, hy⟩
    refine ⟨x, hx, ?_⟩
    rwa [toFunction_eq_iff]

theorem toEquiv_image (r : Rel α β) (hr : r.Bijective) (s : Set α) :
    r.toEquiv hr '' s = r.image s :=
  r.toFunction_image hr.toFunctional s

-- Compare Mathlib.Data.Rel and Mathlib.Logic.Relator.

end Rel
