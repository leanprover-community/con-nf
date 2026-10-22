module

public import Mathlib.Data.Rel
public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.Preorder.Chain

@[expose] public section

open Set
open scoped symmDiff SetRel

namespace SetRel

variable {α β γ : Type*}

def field (r : SetRel α α) : Set α :=
  r.dom ∪ r.cod

@[mk_iff]
structure Injective (r : SetRel α β) : Prop where
  injective : ∀ ⦃x₁ x₂ y⦄, x₁ ~[r] y → x₂ ~[r] y → x₁ = x₂

@[mk_iff]
structure Coinjective (r : SetRel α β) : Prop where
  coinjective : ∀ ⦃y₁ y₂ x⦄, x ~[r] y₁ → x ~[r] y₂ → y₁ = y₂

@[mk_iff]
structure Surjective (r : SetRel α β) : Prop where
  surjective : ∀ y, ∃ x, x ~[r] y

@[mk_iff]
structure Cosurjective (r : SetRel α β) : Prop where
  cosurjective : ∀ x, ∃ y, x ~[r] y

@[mk_iff]
structure Functional (r : SetRel α β) : Prop extends Coinjective r, Cosurjective r

@[mk_iff]
structure Cofunctional (r : SetRel α β) : Prop extends Injective r, Surjective r

@[mk_iff]
structure OneOne (r : SetRel α β) : Prop extends Injective r, Coinjective r

@[mk_iff]
structure Bijective (r : SetRel α β) : Prop extends Functional r, Cofunctional r

@[mk_iff]
structure CodEqDom (r : SetRel α α) : Prop where
  cod_eq_dom : r.cod = r.dom

@[mk_iff]
structure Permutative (r : SetRel α α) : Prop extends OneOne r, CodEqDom r

lemma CodEqDom.dom_union_cod {r : SetRel α α} (h : r.CodEqDom) :
    r.dom ∪ r.cod = r.dom := by
  rw [h.cod_eq_dom, union_self]

lemma CodEqDom.mem_dom {r : SetRel α α} (h : r.CodEqDom) {x y : α} (hxy : x ~[r] y) :
    y ∈ r.dom := by
  rw [← h.cod_eq_dom]
  exact ⟨x, hxy⟩

lemma CodEqDom.mem_cod {r : SetRel α α} (h : r.CodEqDom) {x y : α} (hxy : x ~[r] y) :
    x ∈ r.cod := by
  rw [h.cod_eq_dom]
  exact ⟨y, hxy⟩

/-- An elementary description of the property `CodEqDom`. -/
lemma codEqDom_iff' (r : SetRel α α) :
    r.CodEqDom ↔ (∀ x y, x ~[r] y → ∃ z, y ~[r] z) ∧ (∀ x y, x ~[r] y → ∃ z, z ~[r] x) := by
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

lemma OneOne.inv {r : SetRel α β} (h : r.OneOne) : r.inv.OneOne :=
  ⟨⟨h.coinjective⟩, ⟨h.injective⟩⟩

lemma inv_injective : Function.Injective (inv : SetRel α β → SetRel β α) := by
  intro r s h
  simpa only [inv_inv] using congr_arg inv h

@[simp]
lemma inv_inj {r s : SetRel α β} : r.inv = s.inv ↔ r = s :=
  inv_injective.eq_iff

@[simp]
lemma inv_injective_iff {r : SetRel α β} :
    r.inv.Injective ↔ r.Coinjective :=
  ⟨λ h ↦ ⟨h.injective⟩, λ h ↦ ⟨h.coinjective⟩⟩

@[simp]
lemma inv_coinjective_iff {r : SetRel α β} :
    r.inv.Coinjective ↔ r.Injective :=
  inv_injective_iff.symm

@[simp]
lemma inv_surjective_iff {r : SetRel α β} :
    r.inv.Surjective ↔ r.Cosurjective :=
  ⟨λ h ↦ ⟨h.surjective⟩, λ h ↦ ⟨h.cosurjective⟩⟩

@[simp]
lemma inv_cosurjective_iff {r : SetRel α β} :
    r.inv.Cosurjective ↔ r.Surjective :=
  inv_surjective_iff.symm

@[simp]
lemma inv_functional_iff {r : SetRel α β} :
    r.inv.Functional ↔ r.Cofunctional :=
  ⟨λ h ↦ ⟨inv_coinjective_iff.mp h.toCoinjective, inv_cosurjective_iff.mp h.toCosurjective⟩,
    λ h ↦ ⟨inv_injective_iff.mp h.toInjective, inv_surjective_iff.mp h.toSurjective⟩⟩

@[simp]
lemma inv_cofunctional_iff {r : SetRel α β} :
    r.inv.Cofunctional ↔ r.Functional :=
  inv_functional_iff.symm

lemma Injective.image_injective {r : SetRel α β} (h : r.Injective) {s t : Set α}
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

lemma subset_image_of_preimage_subset {r : SetRel α β} {s : Set β} (hs : s ⊆ r.cod)
    (t : Set α) : r.preimage s ⊆ t → s ⊆ r.image t := by
  intro hst y hy
  obtain ⟨x, hx⟩ := hs hy
  exact ⟨x, hst ⟨y, hy, hx⟩, hx⟩

lemma Injective.preimage_subset_of_subset_image {r : SetRel α β} (h : r.Injective)
    (s : Set β) (t : Set α) :
    s ⊆ r.image t → r.preimage s ⊆ t := by
  rintro hst x ⟨y, hy, hxy⟩
  obtain ⟨z, hz, hzy⟩ := hst hy
  cases h.injective hzy hxy
  exact hz

lemma Injective.preimage_subset_iff_subset_image {r : SetRel α β} (h : r.Injective)
    (s : Set β) (hs : s ⊆ r.cod) (t : Set α) :
    r.preimage s ⊆ t ↔ s ⊆ r.image t :=
  ⟨subset_image_of_preimage_subset hs t, preimage_subset_of_subset_image h s t⟩

lemma OneOne.preimage_eq_iff_image_eq {r : SetRel α β} (h : r.OneOne)
    {s : Set β} (hs : s ⊆ r.cod) {t : Set α} (ht : t ⊆ r.dom) :
    r.preimage s = t ↔ r.image t = s := by
  have h₁ := h.preimage_subset_iff_subset_image s hs t
  have h₂ := h.inv.preimage_subset_iff_subset_image t ht s
  rw [preimage_inv, image_inv] at h₂
  rw [subset_antisymm_iff, subset_antisymm_iff, h₁, h₂, and_comm]

lemma CodEqDom.inv {r : SetRel α α} (h : r.CodEqDom) : r.inv.CodEqDom := by
  rw [codEqDom_iff] at h ⊢
  exact h.symm

lemma Permutative.inv {r : SetRel α α} (h : r.Permutative) : r.inv.Permutative :=
  ⟨h.toOneOne.inv, h.toCodEqDom.inv⟩

lemma Permutative.inv_dom {r : SetRel α α} (h : r.Permutative) : r.inv.dom = r.dom :=
  h.cod_eq_dom

lemma Injective.comp {r : SetRel α β} {s : SetRel β γ} (hr : r.Injective) (hs : s.Injective) :
    (r ○ s).Injective := by
  constructor
  rintro a₁ a₂ c ⟨b₁, hr₁, hs₁⟩ ⟨b₂, hr₂, hs₂⟩
  cases hs.injective hs₁ hs₂
  exact hr.injective hr₁ hr₂

lemma Coinjective.comp {r : SetRel α β} {s : SetRel β γ} (hr : r.Coinjective)
    (hs : s.Coinjective) : (r ○ s).Coinjective := by
  rw [← inv_injective_iff, inv_comp]
  exact Injective.comp (inv_injective_iff.mpr hs) (inv_injective_iff.mpr hr)

lemma Injective.mono {r s : SetRel α β} (hs : s.Injective) (h : r ≤ s) :
    r.Injective := by
  constructor
  intro a₁ a₂ b h₁ h₂
  exact hs.injective (h h₁) (h h₂)

lemma Coinjective.mono {r s : SetRel α β} (hs : s.Coinjective) (h : r ≤ s) :
    r.Coinjective := by
  constructor
  intro b₁ b₂ a h₁ h₂
  exact hs.coinjective (h h₁) (h h₂)

lemma OneOne.mono {r s : SetRel α β} (hs : s.OneOne) (h : r ≤ s) :
    r.OneOne :=
  ⟨hs.toInjective.mono h, hs.toCoinjective.mono h⟩

@[simp]
lemma image_dom {r : SetRel α β} :
    r.image r.dom = r.cod := by
  ext y
  constructor
  · rintro ⟨x, -, hxy⟩
    exact ⟨x, hxy⟩
  · rintro ⟨x, hxy⟩
    exact ⟨x, ⟨y, hxy⟩, hxy⟩

@[simp]
lemma preimage_cod {r : SetRel α β} :
    r.preimage r.cod = r.dom :=
  image_dom (r := r.inv)

lemma preimage_subset_dom (r : SetRel α β) (t : Set β) :
    r.preimage t ⊆ r.dom := by
  rintro x ⟨y, _, h⟩
  exact ⟨y, h⟩

lemma image_subset_cod (r : SetRel α β) (s : Set α) :
    r.image s ⊆ r.cod :=
  r.inv.preimage_subset_dom s

lemma image_empty_of_disjoint_dom {r : SetRel α β} {s : Set α} (h : Disjoint r.dom s) :
    r.image s = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  rw [disjoint_iff_forall_ne] at h
  rintro y ⟨x, hx₁, hx₂⟩
  exact h ⟨y, hx₂⟩ hx₁ rfl

lemma image_eq_of_inter_eq {r : SetRel α β} {s t : Set α} (h : s ∩ r.dom = t ∩ r.dom) :
    r.image s = r.image t := by
  rw [← image_inter_dom, h, image_inter_dom]

lemma Injective.image_diff {r : SetRel α β} (h : r.Injective) (s t : Set α) :
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

lemma Injective.image_symmDiff {r : SetRel α β} (h : r.Injective) (s t : Set α) :
    r.image (s ∆ t) = r.image s ∆ r.image t := by
  rw [Set.symmDiff_def, Set.symmDiff_def, image_union, h.image_diff, h.image_diff]

lemma image_eq_of_le_of_le {r s : SetRel α β} (h : r ≤ s) {t : Set α}
    (ht : ∀ x ∈ t, ∀ y, x ~[s] y → x ~[r] y) :
    r.image t = s.image t := by
  ext y
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨x, hx, h hy⟩
  · rintro ⟨x, hx, hy⟩
    exact ⟨x, hx, ht x hx y hy⟩

@[simp]
lemma sup_inv {r s : SetRel α β} :
    (r ⊔ s).inv = r.inv ⊔ s.inv :=
  rfl

lemma mem_sup {r s : SetRel α β} {x : α} {y : β} :
    x ~[r ⊔ s] y ↔ x ~[r] y ∨ x ~[s] y :=
  Iff.rfl

@[simp]
lemma sup_dom {r s : SetRel α β} :
    (r ⊔ s).dom = r.dom ∪ s.dom := by
  ext x
  simp only [mem_dom, mem_union, mem_sup, exists_or]

@[simp]
lemma sup_cod {r s : SetRel α β} :
    (r ⊔ s).cod = r.cod ∪ s.cod :=
  sup_dom (r := r.inv) (s := s.inv)

@[simp]
lemma sup_image {r s : SetRel α β} (t : Set α) :
    (r ⊔ s).image t = r.image t ∪ s.image t := by
  ext y
  constructor
  · rintro ⟨x, hx₁, hx₂ | hx₂⟩
    · exact Or.inl ⟨x, hx₁, hx₂⟩
    · exact Or.inr ⟨x, hx₁, hx₂⟩
  · rintro (⟨x, hx₁, hx₂⟩ | ⟨x, hx₁, hx₂⟩)
    · exact ⟨x, hx₁, Or.inl hx₂⟩
    · exact ⟨x, hx₁, Or.inr hx₂⟩

protected lemma Injective.sup {r s : SetRel α β} (hr : r.Injective) (hs : s.Injective)
    (h : Disjoint r.cod s.cod) : (r ⊔ s).Injective := by
  constructor
  rintro x₁ x₂ y (h₁ | h₁) (h₂ | h₂)
  · exact hr.injective h₁ h₂
  · cases h.ne_of_mem ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ rfl
  · cases h.ne_of_mem ⟨x₂, h₂⟩ ⟨x₁, h₁⟩ rfl
  · exact hs.injective h₁ h₂

protected lemma Coinjective.sup {r s : SetRel α β} (hr : r.Coinjective) (hs : s.Coinjective)
    (h : Disjoint r.dom s.dom) : (r ⊔ s).Coinjective :=
  inv_coinjective_iff.mpr <| (inv_injective_iff.mpr hr).sup (inv_injective_iff.mpr hs) h

protected lemma OneOne.sup {r s : SetRel α β} (hr : r.OneOne) (hs : s.OneOne)
    (h₁ : Disjoint r.dom s.dom) (h₂ : Disjoint r.cod s.cod) : (r ⊔ s).OneOne :=
  ⟨hr.toInjective.sup hs.toInjective h₂,
    hr.toCoinjective.sup hs.toCoinjective h₁⟩

protected lemma CodEqDom.sup {r s : SetRel α α} (hr : r.CodEqDom) (hs : s.CodEqDom) :
    (r ⊔ s).CodEqDom :=
  ⟨sup_cod.trans <| hr.cod_eq_dom ▸ hs.cod_eq_dom ▸ sup_dom.symm⟩

protected lemma Permutative.sup {r s : SetRel α α} (hr : r.Permutative) (hs : s.Permutative)
    (h : Disjoint r.dom s.dom) : (r ⊔ s).Permutative :=
  ⟨hr.toOneOne.sup hs.toOneOne h (hr.cod_eq_dom ▸ hs.cod_eq_dom ▸ h),
    hr.toCodEqDom.sup hs.toCodEqDom⟩

@[simp]
lemma inf_inv {r s : SetRel α β} :
    (r ⊓ s).inv = r.inv ⊓ s.inv :=
  rfl

lemma mem_inf {r s : SetRel α β} {x : α} {y : β} :
    x ~[r ⊓ s] y ↔ x ~[r] y ∧ x ~[s] y :=
  Iff.rfl

lemma inf_dom {r s : SetRel α β} :
    (r ⊓ s).dom ⊆ r.dom ∩ s.dom := by
  rintro x ⟨y, hy⟩
  exact ⟨⟨y, hy.1⟩, ⟨y, hy.2⟩⟩

lemma inf_cod {r s : SetRel α β} :
    (r ⊓ s).cod ⊆ r.cod ∩ s.cod :=
  inf_dom (r := r.inv) (s := s.inv)

@[simp]
lemma inv_le_inv_iff {r s : SetRel α β} :
    r.inv ≤ s.inv ↔ r ≤ s :=
  ⟨λ h ↦ by simpa only [inv_inv] using inv_mono h, inv_mono⟩

@[simp]
lemma mem_iSup_iff {T : Type*} {r : T → SetRel α β} (x : α) (y : β) :
    x ~[⨆ t, r t] y ↔ ∃ t, x ~[r t] y :=
  Set.mem_iUnion

@[simp]
lemma mem_biSup_iff {T : Type*} {r : T → SetRel α β} {s : Set T} (x : α) (y : β) :
    x ~[⨆ t ∈ s, r t] y ↔ ∃ t ∈ s, x ~[r t] y :=
  Set.mem_iUnion₂.trans (by simp only [exists_prop])

lemma iSup_dom {T : Type*} (r : T → SetRel α β) :
    (⨆ t, r t).dom = ⋃ t, (r t).dom := by
  ext x
  simp only [mem_dom, mem_iSup_iff, mem_iUnion]
  exact exists_comm

lemma biSup_dom {T : Type*} (r : T → SetRel α β) (s : Set T) :
    (⨆ t ∈ s, r t).dom = ⋃ t ∈ s, (r t).dom := by
  have := iSup_dom (λ t : s ↦ r t)
  rwa [iSup_subtype'', iUnion_coe_set] at this

lemma isChain_inv {T : Type*} {r : T → SetRel α β} (h : IsChain (· ≤ ·) (Set.range r)) :
    IsChain (· ≤ ·) (Set.range (λ t ↦ (r t).inv)) := by
  rintro _ ⟨t₁, rfl⟩ _ ⟨t₂, rfl⟩ _
  dsimp only
  rw [inv_le_inv_iff, inv_le_inv_iff]
  apply h.total ⟨t₁, rfl⟩ ⟨t₂, rfl⟩

lemma iSup_inv {T : Type*} {r : T → SetRel α β} :
    (⨆ t, (r t).inv) = (⨆ t, r t).inv := by
  ext ⟨x, y⟩
  exact (mem_iSup_iff x y).trans (mem_iSup_iff (r := r) y x).symm

lemma iSup_injective_of_isChain {T : Type*} {r : T → SetRel α β}
    (h₁ : ∀ t, (r t).Injective) (h₂ : IsChain (· ≤ ·) (Set.range r)) :
    (⨆ t, r t).Injective := by
  constructor
  intro x₁ x₂ y hx₁ hx₂
  rw [mem_iSup_iff] at hx₁ hx₂
  obtain ⟨t₁, hx₁⟩ := hx₁
  obtain ⟨t₂, hx₂⟩ := hx₂
  obtain (h | h) := h₂.total ⟨t₁, rfl⟩ ⟨t₂, rfl⟩
  · exact (h₁ t₂).injective (h hx₁) hx₂
  · exact (h₁ t₁).injective hx₁ (h hx₂)

lemma iSup_coinjective_of_isChain {T : Type*} {r : T → SetRel α β}
    (h₁ : ∀ t, (r t).Coinjective) (h₂ : IsChain (· ≤ ·) (Set.range r)) :
    (⨆ t, r t).Coinjective := by
  have := iSup_injective_of_isChain (r := λ t ↦ (r t).inv) ?_ (isChain_inv h₂)
  · rwa [iSup_inv, inv_injective_iff] at this
  · intro t
    rw [inv_injective_iff]
    exact h₁ t

lemma iSup_codEqDom_of_isChain {T : Type*} {r : T → SetRel α α}
    (h : ∀ t, (r t).CodEqDom) : CodEqDom (⨆ t, r t : SetRel α α) := by
  simp only [codEqDom_iff'] at h ⊢
  constructor
  · intro x y hxy
    obtain ⟨t, ht⟩ := (mem_iSup_iff x y).mp hxy
    obtain ⟨u, hu⟩ := (h t).1 x y ht
    exact ⟨u, (mem_iSup_iff y u).mpr ⟨t, hu⟩⟩
  · intro x y hxy
    obtain ⟨t, ht⟩ := (mem_iSup_iff x y).mp hxy
    obtain ⟨u, hu⟩ := (h t).2 x y ht
    exact ⟨u, (mem_iSup_iff u x).mpr ⟨t, hu⟩⟩

lemma iSup_oneOne_of_isChain {T : Type*} {r : T → SetRel α β}
    (h₁ : ∀ t, (r t).OneOne) (h₂ : IsChain (· ≤ ·) (Set.range r)) :
    (⨆ t, r t).OneOne :=
  ⟨iSup_injective_of_isChain (λ t ↦ (h₁ t).toInjective) h₂,
    iSup_coinjective_of_isChain (λ t ↦ (h₁ t).toCoinjective) h₂⟩

lemma iSup_permutative_of_isChain {T : Type*} {r : T → SetRel α α}
    (h₁ : ∀ t, (r t).Permutative) (h₂ : IsChain (· ≤ ·) (Set.range r)) :
    (⨆ t, r t).Permutative :=
  ⟨iSup_oneOne_of_isChain (λ t ↦ (h₁ t).toOneOne) h₂,
    iSup_codEqDom_of_isChain (λ t ↦ (h₁ t).toCodEqDom)⟩

lemma biSup_permutative_of_isChain {T : Type*} {r : T → SetRel α α} {s : Set T}
    (h₁ : ∀ t ∈ s, (r t).Permutative) (h₂ : IsChain (· ≤ ·) (r '' s)) :
    (⨆ t ∈ s, r t).Permutative := by
  have := iSup_permutative_of_isChain (T := s) (λ t ↦ h₁ t t.prop) ?_
  · rwa [iSup_subtype] at this
  · rwa [image_eq_range] at h₂

noncomputable def toFunction (r : SetRel α β) (hr : r.Functional) : α → β :=
  λ a ↦ (hr.cosurjective a).choose

lemma toFunction_rel (r : SetRel α β) (hr : r.Functional) (a : α) :
    a ~[r] r.toFunction hr a :=
  (hr.cosurjective a).choose_spec

lemma toFunction_eq_iff (r : SetRel α β) (hr : r.Functional) (a : α) (b : β) :
    r.toFunction hr a = b ↔ a ~[r] b := by
  constructor
  · rintro rfl
    exact toFunction_rel r hr a
  · intro h
    exact hr.coinjective (toFunction_rel r hr a) h

noncomputable def toEquiv (r : SetRel α β) (hr : r.Bijective) : α ≃ β where
  toFun := r.toFunction hr.toFunctional
  invFun := r.inv.toFunction (inv_functional_iff.mpr hr.toCofunctional)
  left_inv a := by
    rw [toFunction_eq_iff]
    exact toFunction_rel r hr.toFunctional a
  right_inv b := by
    rw [toFunction_eq_iff]
    exact toFunction_rel r.inv (inv_functional_iff.mpr hr.toCofunctional) b

lemma toEquiv_rel (r : SetRel α β) (hr : r.Bijective) (a : α) :
    a ~[r] r.toEquiv hr a :=
  toFunction_rel r hr.toFunctional a

lemma toEquiv_eq_iff (r : SetRel α β) (hr : r.Bijective) (a : α) (b : β) :
    r.toEquiv hr a = b ↔ a ~[r] b :=
  toFunction_eq_iff r hr.toFunctional a b

lemma toFunction_image (r : SetRel α β) (hr : r.Functional) (s : Set α) :
    r.toFunction hr '' s = r.image s := by
  ext y
  constructor
  · rintro ⟨x, hx, hy⟩
    rw [toFunction_eq_iff] at hy
    exact ⟨x, hx, hy⟩
  · rintro ⟨x, hx, hy⟩
    refine ⟨x, hx, ?_⟩
    rwa [toFunction_eq_iff]

lemma toEquiv_image (r : SetRel α β) (hr : r.Bijective) (s : Set α) :
    r.toEquiv hr '' s = r.image s :=
  r.toFunction_image hr.toFunctional s

end SetRel
