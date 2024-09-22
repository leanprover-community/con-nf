import ConNF.Aux.Cardinal
import ConNF.Aux.Rel

noncomputable section
open Cardinal

namespace Rel

variable {α β : Type _}

/-- TODO: Fix the paper version of this. -/
structure OrbitRestriction (s : Set α) (β : Type _) where
  sandbox : Set α
  sandbox_disjoint : Disjoint s sandbox
  categorise : α → β
  catPerm : Equiv.Perm β
  le_card_categorise (b : β) : max ℵ₀ #s ≤ #(sandbox ∩ categorise ⁻¹' {b} : Set α)

theorem le_card_categorise {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) (b : β) :
    #((r.dom ∪ r.codom : Set α) × ℕ) ≤ #(R.sandbox ∩ R.categorise ⁻¹' {b} : Set α) := by
  rw [Cardinal.mk_prod, Cardinal.lift_id', Cardinal.mk_eq_aleph0 ℕ, Cardinal.lift_aleph0]
  refine le_trans ?_ (R.le_card_categorise b)
  apply mul_le_of_le
  · exact le_max_left ℵ₀ _
  · exact le_max_right ℵ₀ _
  · exact le_max_left ℵ₀ _

def catInj {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) (b : β) :
    (r.dom ∪ r.codom : Set α) × ℕ ↪ (R.sandbox ∩ R.categorise ⁻¹' {b} : Set α) :=
  Nonempty.some (le_card_categorise R b)

theorem catInj_mem_sandbox {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) (b : β)
    (x : (r.dom ∪ r.codom : Set α) × ℕ) :
    (catInj R b x : α) ∈ R.sandbox :=
  (catInj R b x).prop.1

@[simp]
theorem categorise_catInj {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) (b : β)
    (x : (r.dom ∪ r.codom : Set α) × ℕ) :
    R.categorise (catInj R b x) = b :=
  (catInj R b x).prop.2

theorem catInj_ne_of_mem {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) (b : β)
    (x : (r.dom ∪ r.codom : Set α) × ℕ) (a : α) (ha : a ∈ r.dom ∪ r.codom) :
    (catInj R b x : α) ≠ a := by
  have := R.sandbox_disjoint
  rw [Set.disjoint_iff_forall_ne] at this
  exact (this ha (catInj_mem_sandbox R b x)).symm

theorem catInj_injective {r : Rel α α} {R : OrbitRestriction (r.dom ∪ r.codom) β}
    {b₁ b₂ : β} {x₁ x₂ : (r.dom ∪ r.codom : Set α) × ℕ}
    (h : (catInj R b₁ x₁ : α) = catInj R b₂ x₂) :
    b₁ = b₂ ∧ x₁ = x₂ := by
  have h₁ := categorise_catInj R b₁ x₁
  have h₂ := categorise_catInj R b₂ x₂
  rw [h, h₂] at h₁
  cases h₁
  rw [Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq] at h
  exact ⟨rfl, h⟩

@[simp]
theorem catInj_inj {r : Rel α α} {R : OrbitRestriction (r.dom ∪ r.codom) β}
    {b₁ b₂ : β} {a₁ a₂ : α} {h₁ : a₁ ∈ r.dom ∪ r.codom} {h₂ : a₂ ∈ r.dom ∪ r.codom} {n₁ n₂ : ℕ} :
    (catInj R b₁ (⟨a₁, h₁⟩, n₁) : α) = catInj R b₂ (⟨a₂, h₂⟩, n₂) ↔
      b₁ = b₂ ∧ a₁ = a₂ ∧ n₁ = n₂ := by
  constructor
  · intro h
    obtain ⟨rfl, h'⟩ := catInj_injective h
    cases h'
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

inductive newOrbits {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) : Rel α α
  | left (a : α) (had : a ∈ r.dom) (hac : a ∉ r.codom) :
      newOrbits R (catInj R (R.catPerm.symm (R.categorise a)) (⟨a, Or.inl had⟩, 0)) a
  | leftStep (n : ℕ) (a : α) (had : a ∈ r.dom) (hac : a ∉ r.codom) :
      newOrbits R
        (catInj R (R.catPerm.symm^[n + 2] (R.categorise a)) (⟨a, Or.inl had⟩, n + 1))
        (catInj R (R.catPerm.symm^[n + 1] (R.categorise a)) (⟨a, Or.inl had⟩, n))
  | right (a : α) (had : a ∉ r.dom) (hac : a ∈ r.codom) :
      newOrbits R a (catInj R (R.catPerm (R.categorise a)) (⟨a, Or.inr hac⟩, 0))
  | rightStep (n : ℕ) (a : α) (had : a ∉ r.dom) (hac : a ∈ r.codom) :
      newOrbits R
        (catInj R (R.catPerm^[n + 1] (R.categorise a)) (⟨a, Or.inr hac⟩, n))
        (catInj R (R.catPerm^[n + 2] (R.categorise a)) (⟨a, Or.inr hac⟩, n + 1))

def permutativeExtension (r : Rel α α) (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    Rel α α :=
  r ⊔ newOrbits R

theorem le_permutativeExtension (r : Rel α α) (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    r ≤ r.permutativeExtension R :=
  le_sup_left

theorem dom_permutativeExtension_subset (r : Rel α α) (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    (r.permutativeExtension R).dom ⊆ r.dom ∪ r.codom ∪ R.sandbox := by
  rintro a₁ ⟨a₂, h | h⟩
  · exact Or.inl (Or.inl ⟨a₂, h⟩)
  cases h with
  | right _ had hac => exact Or.inl (Or.inr hac)
  | _ => right; apply catInj_mem_sandbox

theorem dom_permutativeExtension_subset' (r : Rel α α) (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    (r.permutativeExtension R).dom ⊆ (r.dom ∪ r.codom) ∪
      ((⋃ a ∈ r.dom, ⋃ n, Subtype.val '' Set.range
        (catInj R (R.catPerm.symm^[n + 1] (R.categorise a)))) ∪
      (⋃ a ∈ r.codom, ⋃ n, Subtype.val '' Set.range
        (catInj R (R.catPerm^[n + 1] (R.categorise a))))) := by
  rintro a₁ ⟨a₂, h | h⟩
  · exact Or.inl (Or.inl ⟨a₂, h⟩)
  cases h with
  | left _ had hac =>
    right; left
    simp only [Set.mem_iUnion]
    exact ⟨a₂, had, 0, _, ⟨_, rfl⟩, rfl⟩
  | leftStep n a had hac =>
    right; left
    simp only [Set.mem_iUnion]
    exact ⟨a, had, n + 1, _, ⟨_, rfl⟩, rfl⟩
  | right _ had hac => exact Or.inl (Or.inr hac)
  | rightStep n a had hac =>
    right; right
    simp only [Set.mem_iUnion]
    exact ⟨a, hac, n , _, ⟨_, rfl⟩, rfl⟩

theorem card_permutativeExtension (r : Rel α α) (R : OrbitRestriction (r.dom ∪ r.codom) β)
    (hr : r.Coinjective) :
    #(r.permutativeExtension R).dom ≤ max ℵ₀ #r.dom := by
  apply (mk_le_mk_of_subset (dom_permutativeExtension_subset' r R)).trans
  apply (mk_union_le _ _).trans
  apply (add_le_add (mk_union_le _ _) (mk_union_le _ _)).trans
  apply add_le_of_le (le_max_left _ _) <;> apply add_le_of_le (le_max_left _ _)
  · exact le_max_right _ _
  · exact le_max_of_le_right (card_codom_le_of_coinjective hr)
  · refine (mk_biUnion_le_of_le (max ℵ₀ #r.dom) ?_).trans ?_
    · intro a _
      have := mk_iUnion_le_of_le_lift
          (f := λ n ↦ Subtype.val '' Set.range (catInj R (R.catPerm.symm^[n + 1] (R.categorise a))))
          (max ℵ₀ #r.dom) ?_
      · rw [lift_id', lift_id', mk_eq_aleph0 ℕ, lift_aleph0] at this
        apply this.trans
        exact mul_le_of_le (le_max_left _ _) (le_max_left _ _) le_rfl
      · intro n
        apply mk_image_le.trans
        apply mk_range_le.trans
        rw [mk_prod, lift_id', mk_eq_aleph0 ℕ, lift_aleph0]
        refine mul_le_of_le (le_max_left _ _) ?_ (le_max_left _ _)
        apply (mk_union_le _ _).trans
        apply add_le_of_le (le_max_left _ _) (le_max_right _ _)
        exact le_max_of_le_right (card_codom_le_of_coinjective hr)
    · exact mul_le_of_le (le_max_left _ _) (le_max_right _ _) le_rfl
  · refine (mk_biUnion_le_of_le (max ℵ₀ #r.dom) ?_).trans ?_
    · intro a _
      have := mk_iUnion_le_of_le_lift
          (f := λ n ↦ Subtype.val '' Set.range (catInj R (R.catPerm^[n + 1] (R.categorise a))))
          (max ℵ₀ #r.dom) ?_
      · rw [lift_id', lift_id', mk_eq_aleph0 ℕ, lift_aleph0] at this
        apply this.trans
        exact mul_le_of_le (le_max_left _ _) (le_max_left _ _) le_rfl
      · intro n
        apply mk_image_le.trans
        apply mk_range_le.trans
        rw [mk_prod, lift_id', mk_eq_aleph0 ℕ, lift_aleph0]
        refine mul_le_of_le (le_max_left _ _) ?_ (le_max_left _ _)
        apply (mk_union_le _ _).trans
        apply add_le_of_le (le_max_left _ _) (le_max_right _ _)
        exact le_max_of_le_right (card_codom_le_of_coinjective hr)
    · refine mul_le_of_le (le_max_left _ _) ?_ le_rfl
      exact le_max_of_le_right (card_codom_le_of_coinjective hr)

theorem categorise_newOrbits {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β)
    {a₁ a₂ : α} (h : newOrbits R a₁ a₂) :
    R.categorise a₂ = R.catPerm (R.categorise a₁) := by
  cases h with
  | left => simp only [categorise_catInj, Equiv.apply_symm_apply]
  | leftStep => simp only [Function.iterate_succ_apply', Function.comp_apply,
      categorise_catInj, Equiv.apply_symm_apply]
  | right => simp only [categorise_catInj]
  | rightStep => simp only [Function.iterate_succ_apply', Function.comp_apply,
      categorise_catInj, Equiv.apply_symm_apply]

theorem categorise_permutativeExtension {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β)
    {a₁ a₂ : α} (h : r.permutativeExtension R a₁ a₂) :
    r a₁ a₂ ∨ R.categorise a₂ = R.catPerm (R.categorise a₁) :=
  h.elim Or.inl (Or.inr ∘ categorise_newOrbits R)

theorem newOrbits_injective {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    (newOrbits R).Injective := by
  constructor
  intro a₁ a₂ a₃ h₁ h₂
  set a₄ := a₃ with h
  clear_value a₄
  rw [h] at h₁
  cases h₁ with
  | left _ hac had =>
    cases h₂ with
    | left => cases h; rfl
    | _ => cases catInj_ne_of_mem R _ _ a₃ (Or.inl hac) h
  | leftStep =>
    cases h₂ with
    | left _ hac had => cases catInj_ne_of_mem R _ _ a₄ (Or.inl hac) h.symm
    | leftStep =>
      simp only [Function.comp_apply, catInj_inj, add_left_inj, Function.iterate_succ_apply',
        EmbeddingLike.apply_eq_iff_eq] at h ⊢
      exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
    | _ =>
      rw [catInj_inj] at h
      cases h.2.1
      contradiction
  | right _ ha₁c ha₁d =>
    cases h₂ with
    | left _ ha₄c ha₄d => cases catInj_ne_of_mem R _ _ a₄ (Or.inl ha₄c) h.symm
    | leftStep n a had hac =>
      rw [catInj_inj] at h
      cases h.2.1
      contradiction
    | right =>
      rw [catInj_inj] at h
      exact h.2.1.symm
    | rightStep => simp only [catInj_inj, AddLeftCancelMonoid.add_eq_zero,
        one_ne_zero, and_false] at h
  | rightStep =>
    cases h₂ with
    | left _ hac had => cases catInj_ne_of_mem R _ _ a₄ (Or.inl hac) h.symm
    | leftStep =>
      rw [catInj_inj] at h
      cases h.2.1
      contradiction
    | rightStep =>
      simp only [Function.comp_apply, catInj_inj, add_left_inj, Function.iterate_succ_apply',
        EmbeddingLike.apply_eq_iff_eq] at h ⊢
      exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
    | right =>
      simp only [catInj_inj, self_eq_add_left, AddLeftCancelMonoid.add_eq_zero,
        one_ne_zero, and_false] at h

theorem newOrbits_coinjective {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    (newOrbits R).Coinjective := by
  constructor
  intro a₁ a₂ a₃ h₁ h₂
  set a₄ := a₃ with h
  clear_value a₄
  rw [h] at h₁
  cases h₁ with
  | right _ hac had =>
    cases h₂ with
    | right => cases h; rfl
    | _ => cases catInj_ne_of_mem R _ _ a₃ (Or.inr had) h
  | rightStep =>
    cases h₂ with
    | right _ hac had => cases catInj_ne_of_mem R _ _ a₄ (Or.inr had) h.symm
    | rightStep =>
      simp only [Function.comp_apply, catInj_inj, add_left_inj, Function.iterate_succ_apply',
        EmbeddingLike.apply_eq_iff_eq] at h ⊢
      exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
    | _ =>
      rw [catInj_inj] at h
      cases h.2.1
      contradiction
  | left _ ha₁c ha₁d =>
    cases h₂ with
    | right _ ha₄c ha₄d => cases catInj_ne_of_mem R _ _ a₄ (Or.inr ha₄d) h.symm
    | rightStep n a had hac =>
      rw [catInj_inj] at h
      cases h.2.1
      contradiction
    | left =>
      rw [catInj_inj] at h
      exact h.2.1.symm
    | leftStep => simp only [catInj_inj, AddLeftCancelMonoid.add_eq_zero,
        one_ne_zero, and_false] at h
  | leftStep =>
    cases h₂ with
    | right _ hac had => cases catInj_ne_of_mem R _ _ a₄ (Or.inr had) h.symm
    | rightStep =>
      rw [catInj_inj] at h
      cases h.2.1
      contradiction
    | leftStep =>
      simp only [Function.comp_apply, catInj_inj, add_left_inj, Function.iterate_succ_apply',
        EmbeddingLike.apply_eq_iff_eq] at h ⊢
      exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
    | left =>
      simp only [catInj_inj, self_eq_add_left, AddLeftCancelMonoid.add_eq_zero,
        one_ne_zero, and_false] at h

theorem newOrbits_oneOne {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    (newOrbits R).OneOne :=
  ⟨newOrbits_injective R, newOrbits_coinjective R⟩

theorem permutativeExtension_codomEqDom {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    (permutativeExtension r R).CodomEqDom := by
  rw [codomEqDom_iff']
  constructor
  · rintro a₁ a₂ (h | h)
    · by_cases had : a₂ ∈ r.dom
      · obtain ⟨a₃, h'⟩ := had
        exact ⟨a₃, Or.inl h'⟩
      · exact ⟨_, Or.inr (newOrbits.right a₂ had ⟨a₁, h⟩)⟩
    · cases h with
      | left _ had hac =>
        obtain ⟨a₃, h⟩ := had
        exact ⟨a₃, Or.inl h⟩
      | leftStep n a had hac =>
        cases n with
        | zero => exact ⟨_, Or.inr (newOrbits.left a had hac)⟩
        | succ n => exact ⟨_, Or.inr (newOrbits.leftStep n a had hac)⟩
      | right _ had hac => exact ⟨_, Or.inr (newOrbits.rightStep 0 a₁ had hac)⟩
      | rightStep n a had hac => exact ⟨_, Or.inr (newOrbits.rightStep (n + 1) a had hac)⟩
  · rintro a₁ a₂ (h | h)
    · by_cases hac : a₁ ∈ r.codom
      · obtain ⟨a₃, h'⟩ := hac
        exact ⟨a₃, Or.inl h'⟩
      · exact ⟨_, Or.inr (newOrbits.left a₁ ⟨a₂, h⟩ hac)⟩
    · cases h with
      | left _ had hac => exact ⟨_, Or.inr (newOrbits.leftStep 0 a₂ had hac)⟩
      | leftStep n a had hac => exact ⟨_, Or.inr (newOrbits.leftStep (n + 1) a had hac)⟩
      | right _ had hac =>
        obtain ⟨a₃, h⟩ := hac
        exact ⟨a₃, Or.inl h⟩
      | rightStep n a had hac =>
        cases n with
        | zero => exact ⟨_, Or.inr (newOrbits.right a had hac)⟩
        | succ n => exact ⟨_, Or.inr (newOrbits.rightStep n a had hac)⟩

theorem disjoint_newOrbits_dom {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    Disjoint r.dom (newOrbits R).dom := by
  rw [Set.disjoint_iff_forall_ne]
  rintro a₁ ha₁ a₂ ⟨a₃, h⟩
  cases h with
  | right => rintro rfl; contradiction
  | _ => exact (catInj_ne_of_mem R _ _ _ (Or.inl ha₁)).symm

theorem disjoint_newOrbits_codom {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β) :
    Disjoint r.codom (newOrbits R).codom := by
  rw [Set.disjoint_iff_forall_ne]
  rintro a₁ ha₁ a₂ ⟨a₃, h⟩
  cases h with
  | left => rintro rfl; contradiction
  | _ => exact (catInj_ne_of_mem R _ _ _ (Or.inr ha₁)).symm

theorem permutativeExtension_permutative {r : Rel α α} (R : OrbitRestriction (r.dom ∪ r.codom) β)
    (hr : r.OneOne) :
    (permutativeExtension r R).Permutative :=
  ⟨sup_oneOne hr (newOrbits_oneOne R) (disjoint_newOrbits_dom R) (disjoint_newOrbits_codom R),
    permutativeExtension_codomEqDom R⟩

def permutativeExtension' (r : Rel α α) (hr : r.OneOne) (s : Set α)
    (hs₁ : s.Infinite) (hs₂ : #r.dom ≤ #s) (hs₃ : Disjoint (r.dom ∪ r.codom) s) :
    Rel α α :=
  r.permutativeExtension {
    sandbox := s
    sandbox_disjoint := hs₃
    categorise := λ _ ↦ Unit.unit
    catPerm := 1
    le_card_categorise := by
      intro
      simp only [Set.mem_singleton_iff, Set.preimage_const_of_mem, Set.inter_univ, max_le_iff,
        le_refl, and_true]
      rw [← Set.infinite_coe_iff, Cardinal.infinite_iff] at hs₁
      refine ⟨hs₁, ?_⟩
      apply (mk_union_le _ _).trans
      apply add_le_of_le hs₁ hs₂
      exact (card_codom_le_of_coinjective hr.toCoinjective).trans hs₂
  }

theorem le_permutativeExtension' {r : Rel α α} {hr : r.OneOne} {s : Set α}
    {hs₁ : s.Infinite} {hs₂ : #r.dom ≤ #s} {hs₃ : Disjoint (r.dom ∪ r.codom) s} :
    r ≤ r.permutativeExtension' hr s hs₁ hs₂ hs₃ :=
  r.le_permutativeExtension _

theorem permutativeExtension'_permutative {r : Rel α α} {hr : r.OneOne} {s : Set α}
    {hs₁ : s.Infinite} {hs₂ : #r.dom ≤ #s} {hs₃ : Disjoint (r.dom ∪ r.codom) s} :
    (r.permutativeExtension' hr s hs₁ hs₂ hs₃).Permutative :=
  permutativeExtension_permutative _ hr

theorem dom_permutativeExtension'_subset {r : Rel α α} {hr : r.OneOne} {s : Set α}
    {hs₁ : s.Infinite} {hs₂ : #r.dom ≤ #s} {hs₃ : Disjoint (r.dom ∪ r.codom) s} :
    (r.permutativeExtension' hr s hs₁ hs₂ hs₃).dom ⊆ r.dom ∪ r.codom ∪ s :=
  r.dom_permutativeExtension_subset _

end Rel
