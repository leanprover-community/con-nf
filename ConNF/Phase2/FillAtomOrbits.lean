import ConNF.Phase2.NearLitterAction

#align_import phase2.fill_atom_orbits

open Cardinal Quiver Set Sum WithBot

open scoped Cardinal Classical Pointwise

universe u

namespace ConNf

variable [Params.{u}]

/-!
# Filling in orbits of atoms
-/


namespace NearLitterAction

variable (φ : NearLitterAction) (hφ : φ.Lawful)

def needForwardImages : Set Atom :=
  φ.atomMap.ran \ φ.atomMap.Dom

def needBackwardImages : Set Atom :=
  φ.atomMap.Dom \ φ.atomMap.ran

theorem atomMap_ran_small : Small φ.atomMap.ran :=
  by
  have : Small (φ.atom_map_or_else '' φ.atom_map.dom) := small.image φ.atom_map_dom_small
  refine' small.mono _ this
  rintro _ ⟨a, ha, rfl⟩
  refine' ⟨a, ha, _⟩
  rw [atom_map_or_else_of_dom]

theorem needForwardImages_small : Small φ.needForwardImages :=
  Small.mono (diff_subset _ _) φ.atomMap_ran_small

theorem needBackwardImages_small : Small φ.needBackwardImages :=
  Small.mono (diff_subset _ _) φ.atomMap_dom_small

theorem mk_diff_dom_ran (L : Litter) :
    (#(litterSet L \ (φ.atomMap.Dom ∪ φ.atomMap.ran) : Set Atom)) = (#κ) :=
  by
  refine' le_antisymm _ _
  · refine' ⟨⟨fun a => a.1.2, _⟩⟩
    intro a b h
    refine' Subtype.coe_injective (Prod.ext (a.prop.1.trans b.prop.1.symm) _)
    simp only [Subtype.val_eq_coe] at h
    exact h
  · by_contra' h
    have :=
      add_lt_of_lt κ_regular.aleph_0_le h (small.union φ.atom_map_dom_small φ.atom_map_ran_small)
    have := (le_mk_diff_add_mk (litter_set L) _).trans_lt this
    simp only [mk_litter_set, lt_self_iff_false] at this
    exact this

theorem need_images_small (L : Litter) :
    (#Sum (ℕ × φ.needBackwardImages) (ℕ × φ.needForwardImages)) < (#κ) :=
  by
  simp only [mk_prod, mk_denumerable, lift_aleph_0, lift_uzero, mk_diff_dom_ran, mk_sum, lift_id]
  rw [← mul_add]
  refine' lt_of_le_of_lt (mul_le_max _ _) (max_lt (max_lt _ _) _)
  exact Λ_limit.aleph_0_le.trans_lt Λ_lt_κ
  exact add_lt_of_lt κ_regular.aleph_0_le φ.need_backward_images_small φ.need_forward_images_small
  exact Λ_limit.aleph_0_le.trans_lt Λ_lt_κ

theorem le_mk_diff_dom_ran (L : Litter) :
    (#Sum (ℕ × φ.needBackwardImages) (ℕ × φ.needForwardImages)) ≤
      (#(litterSet L \ (φ.atomMap.Dom ∪ φ.atomMap.ran) : Set Atom)) :=
  by
  rw [mk_diff_dom_ran]
  exact (φ.need_images_small L).le

def orbitSet (L : Litter) : Set Atom :=
  (le_mk_iff_exists_subset.mp (φ.le_mk_diff_dom_ran L)).some

theorem orbitSet_subset (L : Litter) :
    φ.orbitSet L ⊆ litterSet L \ (φ.atomMap.Dom ∪ φ.atomMap.ran) :=
  (le_mk_iff_exists_subset.mp (φ.le_mk_diff_dom_ran L)).choose_spec.1

theorem not_mem_needForwardImages_of_mem_orbitSet {a : Atom} {L : Litter} (h : a ∈ φ.orbitSet L) :
    a ∉ φ.needForwardImages := fun ha => (φ.orbitSet_subset L h).2 (Or.inr ha.1)

theorem not_mem_needBackwardImages_of_mem_orbitSet {a : Atom} {L : Litter} (h : a ∈ φ.orbitSet L) :
    a ∉ φ.needBackwardImages := fun ha => (φ.orbitSet_subset L h).2 (Or.inl ha.1)

theorem mk_orbitSet (L : Litter) :
    (#φ.orbitSet L) = (#Sum (ℕ × φ.needBackwardImages) (ℕ × φ.needForwardImages)) :=
  (le_mk_iff_exists_subset.mp (φ.le_mk_diff_dom_ran L)).choose_spec.2

noncomputable irreducible_def orbitSetEquiv (L : Litter) :
    φ.orbitSet L ≃ Sum (ℕ × φ.needBackwardImages) (ℕ × φ.needForwardImages) :=
  (Cardinal.eq.mp (φ.mk_orbitSet L)).some

theorem orbitSetEquiv_injective {a₁ a₂ : Sum (ℕ × φ.needBackwardImages) (ℕ × φ.needForwardImages)}
    {L₁ L₂ : Litter} (h : ((φ.orbitSetEquiv L₁).symm a₁ : Atom) = (φ.orbitSetEquiv L₂).symm a₂) :
    L₁ = L₂ ∧ a₁ = a₂ :=
  by
  have h₁ := φ.orbit_set_subset L₁ ((φ.orbit_set_equiv L₁).symm a₁).Prop
  have h₂ := φ.orbit_set_subset L₂ ((φ.orbit_set_equiv L₂).symm a₂).Prop
  rw [h] at h₁
  cases eq_of_mem_litter_set_of_mem_litter_set h₁.1 h₂.1
  simp only [Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq] at h
  exact ⟨rfl, h⟩

theorem orbitSetEquiv_congr {L L' : Litter} {a : Atom} (ha : a ∈ φ.orbitSet L) (h : L = L') :
    φ.orbitSetEquiv L ⟨a, ha⟩ = φ.orbitSetEquiv L' ⟨a, h ▸ ha⟩ := by cases h <;> rfl

theorem orbitSetEquiv_symm_congr {L L' : Litter}
    {a : Sum (ℕ × ↥φ.needBackwardImages) (ℕ × ↥φ.needForwardImages)} (h : L = L') :
    ((φ.orbitSetEquiv L).symm a : Atom) = (φ.orbitSetEquiv L').symm a := by cases h <;> rfl

theorem orbitSet_small (L : Litter) : Small (φ.orbitSet L) :=
  by
  rw [Small, mk_orbit_set]
  exact φ.need_images_small L

noncomputable def nextForwardImage (L : Litter) (a : ℕ × φ.needForwardImages) : Atom :=
  (φ.orbitSetEquiv (φ.litterPerm hφ L)).symm (inr (a.1 + 1, a.2))

noncomputable def nextBackwardImage (L : Litter) : ℕ × φ.needBackwardImages → Atom
  | (0, a) => a
  | (n + 1, a) => (φ.orbitSetEquiv (φ.litterPerm hφ L)).symm (inl (n, a))

def nextForwardImageDomain (L : Litter) : Set (ℕ × φ.needForwardImages) :=
  {a | (a.2 : Atom).1 ∈ (φ.litterPerm hφ).domain ∧ (φ.litterPerm hφ^[a.1 + 1]) (a.2 : Atom).1 = L}

def nextBackwardImageDomain (L : Litter) : Set (ℕ × φ.needBackwardImages) :=
  {a |
    (a.2 : Atom).1 ∈ (φ.litterPerm hφ).domain ∧
      ((φ.litterPerm hφ).symm^[a.1 + 1]) (a.2 : Atom).1 = L}

theorem mk_mem_nextForwardImageDomain (L : Litter) (n : ℕ) (a : φ.needForwardImages) :
    (n, a) ∈ φ.nextForwardImageDomain hφ L ↔
      (a : Atom).1 ∈ (φ.litterPerm hφ).domain ∧ (φ.litterPerm hφ^[n + 1]) (a : Atom).1 = L :=
  Iff.rfl

theorem mk_mem_nextBackwardImageDomain (L : Litter) (n : ℕ) (a : φ.needBackwardImages) :
    (n, a) ∈ φ.nextBackwardImageDomain hφ L ↔
      (a : Atom).1 ∈ (φ.litterPerm hφ).domain ∧ ((φ.litterPerm hφ).symm^[n + 1]) (a : Atom).1 = L :=
  Iff.rfl

theorem nextForwardImage_eq {L₁ L₂ : Litter} {a b : ℕ × φ.needForwardImages}
    (hL₁ : L₁ ∈ (φ.litterPerm hφ).domain) (hL₂ : L₂ ∈ (φ.litterPerm hφ).domain)
    (h : φ.nextForwardImage hφ L₁ a = φ.nextForwardImage hφ L₂ b) : L₁ = L₂ :=
  by
  rw [next_forward_image, next_forward_image] at h
  have ha :=
    φ.orbit_set_subset _ ((φ.orbit_set_equiv (φ.litter_perm hφ L₁)).symm (inr (a.1 + 1, a.2))).Prop
  have hb :=
    φ.orbit_set_subset _ ((φ.orbit_set_equiv (φ.litter_perm hφ L₂)).symm (inr (b.1 + 1, b.2))).Prop
  rw [h] at ha
  refine' (φ.litter_perm hφ).InjOn hL₁ hL₂ _
  exact eq_of_mem_litter_set_of_mem_litter_set ha.1 hb.1

theorem nextBackwardImage_eq {L₁ L₂ : Litter} {a b : ℕ × φ.needBackwardImages}
    (ha : a ∈ φ.nextBackwardImageDomain hφ L₁) (hb : b ∈ φ.nextBackwardImageDomain hφ L₂)
    (hL₁ : L₁ ∈ (φ.litterPerm hφ).domain) (hL₂ : L₂ ∈ (φ.litterPerm hφ).domain)
    (h : φ.nextBackwardImage hφ L₁ a = φ.nextBackwardImage hφ L₂ b) : L₁ = L₂ :=
  by
  obtain ⟨m, a⟩ := a
  obtain ⟨n, b⟩ := b
  cases m <;> cases n <;> rw [next_backward_image, next_backward_image] at h
  · simp only [next_backward_image_domain, Function.iterate_succ, Function.comp_apply,
      mem_set_of_eq, Function.iterate_zero, id.def] at ha hb
    rw [← h, ha.2] at hb
    exact hb.2
  · rw [Subtype.coe_eq_iff] at h
    obtain ⟨h₁, h₂⟩ := h
    cases φ.not_mem_need_backward_images_of_mem_orbit_set ((φ.orbit_set_equiv _).symm _).Prop h₁
  · symm at h
    rw [Subtype.coe_eq_iff] at h
    obtain ⟨h₁, h₂⟩ := h
    cases φ.not_mem_need_backward_images_of_mem_orbit_set ((φ.orbit_set_equiv _).symm _).Prop h₁
  · have ha :=
      φ.orbit_set_subset _ ((φ.orbit_set_equiv (φ.litter_perm hφ L₁)).symm (inl (m, a))).Prop
    have hb :=
      φ.orbit_set_subset _ ((φ.orbit_set_equiv (φ.litter_perm hφ L₂)).symm (inl (n, b))).Prop
    rw [h] at ha
    refine' (φ.litter_perm hφ).InjOn hL₁ hL₂ _
    exact eq_of_mem_litter_set_of_mem_litter_set ha.1 hb.1

theorem nextForwardImage_injective {L : Litter} {a b : ℕ × φ.needForwardImages}
    (h : φ.nextForwardImage hφ L a = φ.nextForwardImage hφ L b) : a = b :=
  by
  simp only [next_forward_image, Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq, Prod.mk.inj_iff,
    add_left_inj] at h
  exact Prod.ext h.1 h.2

theorem nextBackwardImage_injective {L : Litter} {a b : ℕ × φ.needBackwardImages}
    (ha : a ∈ φ.nextBackwardImageDomain hφ L) (hb : b ∈ φ.nextBackwardImageDomain hφ L)
    (h : φ.nextBackwardImage hφ L a = φ.nextBackwardImage hφ L b) : a = b :=
  by
  obtain ⟨m, a⟩ := a
  obtain ⟨n, b⟩ := b
  cases m <;> cases n <;>
    simp only [Prod.mk.inj_iff, Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq, Prod.mk.inj_iff,
      false_and_iff, Nat.zero_eq, Prod.mk.inj_iff, next_backward_image, Prod.mk.inj_iff,
      eq_self_iff_true, true_and_iff, Subtype.coe_inj] at h ⊢
  · exact h
  · rw [Subtype.coe_eq_iff] at h
    obtain ⟨h₁, h₂⟩ := h
    cases φ.not_mem_need_backward_images_of_mem_orbit_set ((φ.orbit_set_equiv _).symm _).Prop h₁
  · symm at h
    rw [Subtype.coe_eq_iff] at h
    obtain ⟨h₁, h₂⟩ := h
    cases φ.not_mem_need_backward_images_of_mem_orbit_set ((φ.orbit_set_equiv _).symm _).Prop h₁
  · exact h

theorem nextForwardImage_injective' {L₁ L₂ : Litter} {a b : ℕ × φ.needForwardImages}
    (hL₁ : L₁ ∈ (φ.litterPerm hφ).domain) (hL₂ : L₂ ∈ (φ.litterPerm hφ).domain)
    (h : φ.nextForwardImage hφ L₁ a = φ.nextForwardImage hφ L₂ b) : a = b :=
  by
  cases φ.next_forward_image_eq hφ hL₁ hL₂ h
  exact φ.next_forward_image_injective hφ h

theorem nextBackwardImage_injective' {L₁ L₂ : Litter} {a b : ℕ × φ.needBackwardImages}
    (ha : a ∈ φ.nextBackwardImageDomain hφ L₁) (hb : b ∈ φ.nextBackwardImageDomain hφ L₂)
    (hL₁ : L₁ ∈ (φ.litterPerm hφ).domain) (hL₂ : L₂ ∈ (φ.litterPerm hφ).domain)
    (h : φ.nextBackwardImage hφ L₁ a = φ.nextBackwardImage hφ L₂ b) : a = b :=
  by
  cases φ.next_backward_image_eq hφ ha hb hL₁ hL₂ h
  exact φ.next_backward_image_injective hφ ha hb h

theorem nextForwardImage_ne_nextBackwardImage {L₁ L₂ : Litter} {a : ℕ × φ.needForwardImages}
    {b : ℕ × φ.needBackwardImages} : φ.nextForwardImage hφ L₁ a ≠ φ.nextBackwardImage hφ L₂ b :=
  by
  obtain ⟨n, b⟩ := b
  cases n
  · rw [next_forward_image, next_backward_image]
    refine'
      (ne_of_mem_of_not_mem _ (φ.orbit_set_subset _ ((φ.orbit_set_equiv _).symm _).Prop).2).symm
    exact Or.inl b.prop.1
  · rw [next_forward_image, next_backward_image]
    intro h
    cases (φ.orbit_set_equiv_injective h).2

noncomputable def nextImageCore (a : Atom) (L : Litter) (ha : a ∈ φ.orbitSet L) : Atom :=
  (φ.orbitSetEquiv L ⟨a, ha⟩).elim (φ.nextBackwardImage hφ L) (φ.nextForwardImage hφ L)

def nextImageCoreDomain : Set Atom :=
  ⋃ L ∈ (φ.litterPerm hφ).domain,
    coe ''
      {a : φ.orbitSet L |
        (φ.orbitSetEquiv L a).elim (fun b => b ∈ φ.nextBackwardImageDomain hφ L) fun b =>
          b ∈ φ.nextForwardImageDomain hφ L}

theorem nextImageCoreDomain_small : Small (φ.nextImageCoreDomain hφ) :=
  Small.bUnion (φ.litterPerm_domain_small hφ) fun L hL =>
    Small.image (lt_of_le_of_lt (Cardinal.mk_subtype_le _) (φ.orbitSet_small L))

theorem litter_map_dom_of_mem_nextImageCoreDomain {a : Atom} (h : a ∈ φ.nextImageCoreDomain hφ) :
    a.1 ∈ (φ.litterPerm hφ).domain :=
  by
  rw [next_image_core_domain] at h
  simp only [PFun.mem_dom, Union_exists, mem_Union, mem_image, mem_set_of_eq, SetCoe.exists,
    Subtype.coe_mk, exists_and_right, exists_eq_right, exists_prop] at h
  obtain ⟨L, hL, ha, h⟩ := h
  have := (φ.orbit_set_subset L ha).1
  rw [mem_litter_set] at this
  rw [this]
  exact hL

theorem mem_orbitSet_of_mem_nextImageCoreDomain {a : Atom} (h : a ∈ φ.nextImageCoreDomain hφ) :
    a ∈ φ.orbitSet a.1 := by
  rw [next_image_core_domain] at h
  simp only [PFun.mem_dom, Union_exists, mem_Union, mem_image, mem_set_of_eq, SetCoe.exists,
    Subtype.coe_mk, exists_and_right, exists_eq_right, exists_prop] at h
  obtain ⟨L, hL, ha, h⟩ := h
  have := (φ.orbit_set_subset L ha).1
  rw [mem_litter_set] at this
  rw [this]
  exact ha

theorem orbitSetEquivElimOfMemNextImageCoreDomain {a : Atom} (h : a ∈ φ.nextImageCoreDomain hφ) :
    (φ.orbitSetEquiv a.1 ⟨a, φ.mem_orbitSet_of_mem_nextImageCoreDomain hφ h⟩).elim
      (fun c => c ∈ φ.nextBackwardImageDomain hφ a.1) fun c =>
      c ∈ φ.nextForwardImageDomain hφ a.1 :=
  by
  rw [next_image_core_domain] at h
  simp only [PFun.mem_dom, Union_exists, mem_Union, mem_image, mem_set_of_eq, SetCoe.exists,
    Subtype.coe_mk, exists_and_right, exists_eq_right, exists_prop] at h
  obtain ⟨L, hL, ha, h⟩ := h
  have := (φ.orbit_set_subset L ha).1
  rw [mem_litter_set] at this
  cases this
  exact h

theorem nextImageCore_injective (a b : Atom) (ha : a ∈ φ.nextImageCoreDomain hφ)
    (hb : b ∈ φ.nextImageCoreDomain hφ)
    (h :
      φ.nextImageCore hφ a a.1 (φ.mem_orbitSet_of_mem_nextImageCoreDomain hφ ha) =
        φ.nextImageCore hφ b b.1 (φ.mem_orbitSet_of_mem_nextImageCoreDomain hφ hb)) :
    a = b := by
  rw [next_image_core, next_image_core] at h
  obtain ⟨a', ha'⟩ :=
    (φ.orbit_set_equiv a.fst).symm.Surjective
      ⟨a, φ.mem_orbit_set_of_mem_next_image_core_domain hφ ha⟩
  obtain ⟨b', hb'⟩ :=
    (φ.orbit_set_equiv b.fst).symm.Surjective
      ⟨b, φ.mem_orbit_set_of_mem_next_image_core_domain hφ hb⟩
  have hae := φ.orbit_set_equiv_elim_of_mem_next_image_core_domain hφ ha
  have hbe := φ.orbit_set_equiv_elim_of_mem_next_image_core_domain hφ hb
  simp only [← ha', ← hb', Equiv.apply_symm_apply] at h hae hbe
  obtain ⟨m, a'⟩ | ⟨m, a'⟩ := a' <;> obtain ⟨n, b'⟩ | ⟨n, b'⟩ := b' <;>
    simp only [elim_inl, elim_inr, mk_mem_next_backward_image_domain,
      mk_mem_next_forward_image_domain] at h hae hbe
  · cases φ.next_backward_image_injective' hφ _ _ _ _ h
    · rw [hae.2] at hbe
      rw [Subtype.ext_iff, Subtype.coe_mk] at ha' hb'
      rw [← ha', ← hb', hbe.2]
    · exact hae
    · exact hbe
    · exact φ.litter_map_dom_of_mem_next_image_core_domain hφ ha
    · exact φ.litter_map_dom_of_mem_next_image_core_domain hφ hb
  · cases φ.next_forward_image_ne_next_backward_image hφ h.symm
  · cases φ.next_forward_image_ne_next_backward_image hφ h
  · cases φ.next_forward_image_injective' hφ _ _ h
    · rw [hae.2] at hbe
      rw [Subtype.ext_iff, Subtype.coe_mk] at ha' hb'
      rw [← ha', ← hb']
      exact φ.orbit_set_equiv_symm_congr hbe.2
    · exact φ.litter_map_dom_of_mem_next_image_core_domain hφ ha
    · exact φ.litter_map_dom_of_mem_next_image_core_domain hφ hb

def nextImageDomain : Set Atom :=
  φ.needForwardImages ∩ {a | a.1 ∈ (φ.litterPerm hφ).domain} ∪ φ.nextImageCoreDomain hφ

noncomputable def nextImage (a : Atom) (ha : a ∈ φ.nextImageDomain hφ) : Atom :=
  ha.elim' (fun ha' => (φ.orbitSetEquiv (φ.litterPerm hφ a.1)).symm (inr (0, ⟨a, ha'.1⟩)))
    (φ.nextImageCore hφ a a.1 ∘ φ.mem_orbitSet_of_mem_nextImageCoreDomain hφ)

theorem nextImageDomain_small : Small (φ.nextImageDomain hφ) :=
  Small.union (Small.mono (inter_subset_left _ _) φ.needForwardImages_small)
    (φ.nextImageCoreDomain_small hφ)

theorem disjoint_needForwardImages_nextImageCoreDomain :
    Disjoint φ.needForwardImages (φ.nextImageCoreDomain hφ) :=
  by
  rw [Set.disjoint_iff]
  rintro a ⟨ha₁, ha₂⟩
  exact
    (φ.orbit_set_subset _ (φ.mem_orbit_set_of_mem_next_image_core_domain hφ ha₂)).2 (Or.inr ha₁.1)

theorem nextImage_eq_of_needForwardImages (a : Atom)
    (ha : a ∈ φ.needForwardImages ∧ a.1 ∈ (φ.litterPerm hφ).domain) :
    φ.nextImage hφ a (Or.inl ha) =
      (φ.orbitSetEquiv (φ.litterPerm hφ a.1)).symm (inr (0, ⟨a, ha.1⟩)) :=
  Or.elim'_left _ _ _ ha

theorem nextImage_eq_of_mem_nextImageCoreDomain (a : Atom) (ha : a ∈ φ.nextImageCoreDomain hφ) :
    φ.nextImage hφ a (Or.inr ha) =
      φ.nextImageCore hφ a a.1 (φ.mem_orbitSet_of_mem_nextImageCoreDomain hφ ha) :=
  by
  refine' Or.elim'_right _ _ _ _
  exact fun h =>
    set.disjoint_right.mp (φ.disjoint_need_forward_images_next_image_core_domain hφ) ha h.1

theorem orbitSetEquiv_ne_nextImageCore (a b : Atom)
    (ha : a ∈ φ.needForwardImages ∧ a.fst ∈ (φ.litterPerm hφ).domain)
    (hb : b ∈ φ.nextImageCoreDomain hφ) :
    ((φ.orbitSetEquiv (φ.litterPerm hφ a.fst)).symm (inr (0, ⟨a, ha.1⟩)) : Atom) ≠
      φ.nextImageCore hφ b b.fst (φ.mem_orbitSet_of_mem_nextImageCoreDomain hφ hb) :=
  by
  obtain ⟨b', hb'⟩ :=
    (φ.orbit_set_equiv b.fst).symm.Surjective
      ⟨b, φ.mem_orbit_set_of_mem_next_image_core_domain hφ hb⟩
  rw [Equiv.symm_apply_eq] at hb'
  intro h
  rw [next_image_core] at h
  rw [← hb'] at h
  obtain ⟨_ | n, b'⟩ | b' := b' <;>
    simp only [elim_inl, elim_inr, next_backward_image, next_forward_image] at h
  · have := φ.orbit_set_subset _ ((φ.orbit_set_equiv _).symm _).Prop
    rw [h] at this
    exact this.2 (Or.inl b'.prop.1)
  · cases (φ.orbit_set_equiv_injective h).2
  · cases (φ.orbit_set_equiv_injective h).2

theorem nextImage_injective (a b : Atom) (ha : a ∈ φ.nextImageDomain hφ)
    (hb : b ∈ φ.nextImageDomain hφ) (h : φ.nextImage hφ a ha = φ.nextImage hφ b hb) : a = b :=
  by
  cases ha <;> cases hb <;>
    simp only [next_image_eq_of_need_forward_images, next_image_eq_of_mem_next_image_core_domain] at
      h
  · have := φ.orbit_set_equiv_injective h
    simp only [Prod.mk.inj_iff, eq_self_iff_true, Subtype.mk_eq_mk, true_and_iff] at this
    exact this.2
  · cases φ.orbit_set_equiv_ne_next_image_core hφ _ _ _ _ h
  · cases φ.orbit_set_equiv_ne_next_image_core hφ _ _ _ _ h.symm
  · refine' φ.next_image_core_injective hφ a b ha hb h

noncomputable def orbitAtomMap : Atom →. Atom := fun a =>
  { Dom := (φ.atomMap a).Dom ∨ a ∈ φ.nextImageDomain hφ
    get := fun h => Or.elim' h (φ.atomMap a).get (φ.nextImage hφ a) }

@[simp]
theorem orbitAtomMap_dom_iff (a : Atom) :
    (φ.orbitAtomMap hφ a).Dom ↔ (φ.atomMap a).Dom ∨ a ∈ φ.nextImageDomain hφ :=
  Iff.rfl

@[simp]
theorem orbitAtomMap_dom : (φ.orbitAtomMap hφ).Dom = φ.atomMap.Dom ∪ φ.nextImageDomain hφ :=
  rfl

theorem disjoint_atomMap_dom_nextImageDomain : Disjoint φ.atomMap.Dom (φ.nextImageDomain hφ) :=
  by
  rw [Set.disjoint_iff]
  rintro a ⟨h₁, h₂ | h₂⟩
  · exact h₂.1.2 h₁
  · exact (φ.orbit_set_subset _ (φ.mem_orbit_set_of_mem_next_image_core_domain hφ h₂)).2 (Or.inl h₁)

theorem orbitAtomMap_eq_of_mem_dom (a : Atom) (ha : (φ.atomMap a).Dom) :
    (φ.orbitAtomMap hφ a).get (Or.inl ha) = (φ.atomMap a).get ha :=
  Or.elim'_left _ _ _ _

theorem orbitAtomMap_eq_of_mem_nextImageDomain (a : Atom) (ha : a ∈ φ.nextImageDomain hφ) :
    (φ.orbitAtomMap hφ a).get (Or.inr ha) = φ.nextImage hφ a ha :=
  Or.elim'_right _ _ _ (id Set.disjoint_right.mp (φ.disjoint_atomMap_dom_nextImageDomain hφ) ha)

theorem orbitAtomMap_eq_of_needForwardImages (a : Atom)
    (ha : a ∈ φ.needForwardImages ∧ a.fst ∈ (φ.litterPerm hφ).domain) :
    (φ.orbitAtomMap hφ a).get (Or.inr (Or.inl ha)) =
      (φ.orbitSetEquiv (φ.litterPerm hφ a.1)).symm (inr (0, ⟨a, ha.1⟩)) :=
  by
  unfold orbit_atom_map
  simp only
  rw [Or.elim'_right]
  exact φ.next_image_eq_of_need_forward_images hφ a ha
  exact id set.disjoint_right.mp (φ.disjoint_atom_map_dom_next_image_domain hφ) (Or.inl ha)

theorem orbitAtomMap_eq_of_mem_nextImageCoreDomain (a : Atom) (ha : a ∈ φ.nextImageCoreDomain hφ) :
    (φ.orbitAtomMap hφ a).get (Or.inr (Or.inr ha)) =
      φ.nextImageCore hφ a a.1 (φ.mem_orbitSet_of_mem_nextImageCoreDomain hφ ha) :=
  by
  unfold orbit_atom_map
  simp only
  rw [Or.elim'_right]
  exact φ.next_image_eq_of_mem_next_image_core_domain hφ a ha
  exact id set.disjoint_right.mp (φ.disjoint_atom_map_dom_next_image_domain hφ) (Or.inr ha)

theorem orbitAtomMap_dom_small : Small (φ.orbitAtomMap hφ).Dom :=
  Small.union φ.atomMap_dom_small (φ.nextImageDomain_small hφ)

theorem orbitAtomMap_apply_ne_of_needForwardImages ⦃a b : Atom⦄ (ha : (φ.atomMap a).Dom)
    (hb : b ∈ φ.needForwardImages ∧ b.fst ∈ (φ.litterPerm hφ).domain) :
    (φ.orbitAtomMap hφ a).get (Or.inl ha) ≠ (φ.orbitAtomMap hφ b).get (Or.inr (Or.inl hb)) :=
  by
  rw [orbit_atom_map_eq_of_mem_dom, orbit_atom_map_eq_of_need_forward_images]
  intro h
  have := φ.orbit_set_subset _ ((φ.orbit_set_equiv _).symm _).Prop
  rw [← h] at this
  exact this.2 (Or.inr ⟨a, ha, rfl⟩)

theorem orbitAtomMap_apply_ne_of_mem_nextImageCoreDomain ⦃a b : Atom⦄ (ha : (φ.atomMap a).Dom)
    (hb : b ∈ φ.nextImageCoreDomain hφ) :
    (φ.orbitAtomMap hφ a).get (Or.inl ha) ≠ (φ.orbitAtomMap hφ b).get (Or.inr (Or.inr hb)) :=
  by
  obtain ⟨b', hb'⟩ :=
    (φ.orbit_set_equiv b.fst).symm.Surjective
      ⟨b, φ.mem_orbit_set_of_mem_next_image_core_domain hφ hb⟩
  rw [orbit_atom_map_eq_of_mem_dom, orbit_atom_map_eq_of_mem_next_image_core_domain,
    next_image_core, ← hb', Equiv.apply_symm_apply]
  obtain ⟨_ | n, b'⟩ | ⟨n, b'⟩ := b' <;>
    simp only [elim_inr, elim_inl, Nat.zero_eq, next_backward_image, next_forward_image]
  · intro h
    have := b'.prop.2
    rw [← h] at this
    exact this ⟨a, ha, rfl⟩
  · intro h
    have := (φ.orbit_set_subset _ ((φ.orbit_set_equiv _).symm _).Prop).2
    rw [← h] at this
    exact this (Or.inr ⟨a, ha, rfl⟩)
  · intro h
    have := (φ.orbit_set_subset _ ((φ.orbit_set_equiv _).symm _).Prop).2
    rw [← h] at this
    exact this (Or.inr ⟨a, ha, rfl⟩)

theorem orbitAtomMap_apply_ne ⦃a b : Atom⦄ (ha : (φ.atomMap a).Dom)
    (hb : b ∈ φ.nextImageDomain hφ) :
    (φ.orbitAtomMap hφ a).get (Or.inl ha) ≠ (φ.orbitAtomMap hφ b).get (Or.inr hb) :=
  by
  cases hb
  exact φ.orbit_atom_map_apply_ne_of_need_forward_images hφ ha hb
  exact φ.orbit_atom_map_apply_ne_of_mem_next_image_core_domain hφ ha hb

theorem orbitAtomMap_injective ⦃a b : Atom⦄ (ha : (φ.orbitAtomMap hφ a).Dom)
    (hb : (φ.orbitAtomMap hφ b).Dom)
    (h : (φ.orbitAtomMap hφ a).get ha = (φ.orbitAtomMap hφ b).get hb) : a = b :=
  by
  cases ha <;> cases hb
  · rw [orbit_atom_map_eq_of_mem_dom, orbit_atom_map_eq_of_mem_dom] at h
    exact hφ.atom_map_injective ha hb h
  · cases φ.orbit_atom_map_apply_ne hφ ha hb h
  · cases φ.orbit_atom_map_apply_ne hφ hb ha h.symm
  · rw [orbit_atom_map_eq_of_mem_next_image_domain, orbit_atom_map_eq_of_mem_next_image_domain] at h
    exact φ.next_image_injective hφ a b ha hb h

theorem nextImageCore_atom_mem_litter_map (a : Atom) (ha : a ∈ φ.nextImageCoreDomain hφ) :
    φ.nextImageCore hφ a a.fst (φ.mem_orbitSet_of_mem_nextImageCoreDomain hφ ha) ∈
      litterSet (φ.litterPerm hφ a.fst) :=
  by
  have hL := φ.litter_map_dom_of_mem_next_image_core_domain hφ ha
  have := φ.mem_orbit_set_of_mem_next_image_core_domain hφ ha
  obtain ⟨a', ha'⟩ :=
    (φ.orbit_set_equiv a.fst).symm.Surjective
      ⟨a, φ.mem_orbit_set_of_mem_next_image_core_domain hφ ha⟩
  have := φ.orbit_set_equiv_elim_of_mem_next_image_core_domain hφ ha
  rw [next_image_core]
  rw [← ha', Equiv.apply_symm_apply] at this ⊢
  obtain ⟨_ | n, a'⟩ | ⟨n, a'⟩ := a' <;>
    simp only [elim_inr, elim_inl, Nat.zero_eq, next_backward_image, next_forward_image,
      mk_mem_next_backward_image_domain, mk_mem_next_forward_image_domain, Function.iterate_one] at
      this ⊢
  · have ha'' := this.2.symm
    rw [LocalPerm.eq_symm_apply] at ha''
    · exact ha''.symm
    · exact hL
    · exact this.1
  exact (φ.orbit_set_subset _ ((φ.orbit_set_equiv _).symm _).Prop).1
  exact (φ.orbit_set_subset _ ((φ.orbit_set_equiv _).symm _).Prop).1

theorem nextImageCore_not_mem_ran (a : Atom) (ha : a ∈ φ.nextImageCoreDomain hφ) :
    φ.nextImageCore hφ a a.fst (φ.mem_orbitSet_of_mem_nextImageCoreDomain hφ ha) ∉ φ.atomMap.ran :=
  by
  rintro ⟨b, hb₁, hb₂⟩
  rw [next_image_core] at hb₂
  obtain ⟨a', ha'⟩ :=
    (φ.orbit_set_equiv a.fst).symm.Surjective
      ⟨a, φ.mem_orbit_set_of_mem_next_image_core_domain hφ ha⟩
  rw [← ha', Equiv.apply_symm_apply] at hb₂
  obtain ⟨_ | n, a'⟩ | ⟨n, a'⟩ := a' <;>
    simp only [elim_inr, elim_inl, Nat.zero_eq, next_backward_image, next_forward_image,
      mk_mem_next_backward_image_domain, mk_mem_next_forward_image_domain, Function.iterate_one] at
      hb₂
  · exact a'.prop.2 ⟨b, hb₁, hb₂⟩
  all_goals
    have := φ.orbit_set_subset _ ((φ.orbit_set_equiv _).symm _).Prop
    rw [← hb₂] at this
    exact this.2 (Or.inr ⟨b, hb₁, rfl⟩)

theorem nextImageCore_atom_mem
    (hdiff :
      ∀ L hL,
        ((φ.litterMap L).get hL : Set Atom) ∆ litterSet ((φ.litterMap L).get hL).1 ⊆ φ.atomMap.ran)
    (a : Atom) (ha : a ∈ φ.nextImageCoreDomain hφ) (L : Litter) (hL : (φ.litterMap L).Dom) :
    a.fst = L ↔
      φ.nextImageCore hφ a a.fst (φ.mem_orbitSet_of_mem_nextImageCoreDomain hφ ha) ∈
        (φ.litterMap L).get hL :=
  by
  have hamem := φ.mem_orbit_set_of_mem_next_image_core_domain hφ ha
  have ha' := φ.next_image_core_atom_mem_litter_map hφ a ha
  rw [mem_litter_set] at ha'
  constructor
  · rintro rfl
    have := not_mem_subset (hdiff _ hL) (φ.next_image_core_not_mem_ran hφ a ha)
    simp only [mem_symm_diff, SetLike.mem_coe, mem_litter_set, not_or, not_and_or,
      Classical.not_not] at this
    refine' this.2.resolve_left (not_not.mpr _)
    rw [ha']
    rw [litter_perm_apply_eq _ hL]
    rw [φ.rough_litter_map_or_else_of_dom]
  · intro h
    have hL' := litter_perm_apply_eq L hL
    rw [φ.rough_litter_map_or_else_of_dom hL] at hL'
    have := not_mem_subset (hdiff _ hL) (φ.next_image_core_not_mem_ran hφ a ha)
    simp only [mem_symm_diff, SetLike.mem_coe, mem_litter_set, Classical.not_not, h, true_and_iff,
      not_true, and_false_iff, or_false_iff] at this
    rw [ha', ← hL', ← LocalPerm.eq_symm_apply, LocalPerm.left_inv] at this
    exact this
    exact Or.inl (Or.inl (Or.inl hL))
    exact φ.litter_map_dom_of_mem_next_image_core_domain hφ ha
    exact LocalPerm.map_domain _ (Or.inl (Or.inl (Or.inl hL)))

theorem orbitSetEquiv_atom_mem
    (hdiff :
      ∀ L hL,
        ((φ.litterMap L).get hL : Set Atom) ∆ litterSet ((φ.litterMap L).get hL).1 ⊆ φ.atomMap.ran)
    (a : Atom) (ha : a ∈ φ.needForwardImages ∧ a.fst ∈ (φ.litterPerm hφ).domain) (L : Litter)
    (hL : (φ.litterMap L).Dom) :
    a.fst = L ↔
      ((φ.orbitSetEquiv (φ.litterPerm hφ a.fst)).symm (inr (0, ⟨a, ha.1⟩)) : Atom) ∈
        (φ.litterMap L).get hL :=
  by
  have ha' : _ ∧ _ :=
    φ.orbit_set_subset _
      ((φ.orbit_set_equiv (φ.litter_perm hφ a.fst)).symm (inr (0, ⟨a, ha.1⟩))).Prop
  rw [mem_litter_set] at ha'
  constructor
  · rintro rfl
    have := not_mem_subset (hdiff _ hL) _
    simp only [mem_symm_diff, SetLike.mem_coe, mem_litter_set, not_or, not_and_or,
      Classical.not_not] at this
    refine' this.2.resolve_left (not_not.mpr _)
    · rw [ha'.1]
      rw [litter_perm_apply_eq _ hL]
      rw [φ.rough_litter_map_or_else_of_dom]
    · exact ha'.2 ∘ Or.inr
  · intro h
    have :=
      @not_mem_subset _
        ((φ.orbit_set_equiv (φ.litter_perm hφ a.fst)).symm (inr (0, ⟨a, ha.1⟩)) : atom) _ _
        (hdiff L hL) (ha'.2 ∘ Or.inr)
    simp only [mem_symm_diff, h, SetLike.mem_coe, mem_litter_set, true_and_iff, not_true,
      and_false_iff, or_false_iff, Classical.not_not] at this
    rw [ha'.1, ← rough_litter_map_or_else_of_dom, ← @litter_perm_apply_eq _ _ hφ, ←
      LocalPerm.eq_symm_apply, LocalPerm.left_inv] at this
    exact this
    · exact Or.inl (Or.inl (Or.inl hL))
    · exact ha.2
    · exact (φ.litter_perm hφ).map_domain (Or.inl (Or.inl (Or.inl hL)))
    · exact hL

theorem orbit_atom_mem
    (hdiff :
      ∀ L hL,
        ((φ.litterMap L).get hL : Set Atom) ∆ litterSet ((φ.litterMap L).get hL).1 ⊆ φ.atomMap.ran)
    (a : Atom) (ha : (φ.orbitAtomMap hφ a).Dom) (L : Litter) (hL : (φ.litterMap L).Dom) :
    a.fst = L ↔ (φ.orbitAtomMap hφ a).get ha ∈ (φ.litterMap L).get hL :=
  by
  obtain ha | ha | ha := ha
  · rw [orbit_atom_map_eq_of_mem_dom]
    exact hφ.atom_mem a ha L hL
  · rw [orbit_atom_map_eq_of_need_forward_images]
    exact φ.orbit_set_equiv_atom_mem hφ hdiff a ha L hL
  · rw [orbit_atom_map_eq_of_mem_next_image_core_domain]
    rw [φ.next_image_core_atom_mem hφ hdiff a ha L hL]

noncomputable def fillAtomOrbits : NearLitterAction
    where
  atomMap := φ.orbitAtomMap hφ
  litterMap := φ.litterMap
  atomMap_dom_small := φ.orbitAtomMap_dom_small hφ
  litterMap_dom_small := φ.litterMap_dom_small

theorem fillAtomOrbitsLawful
    (hdiff :
      ∀ L hL,
        ((φ.litterMap L).get hL : Set Atom) ∆ litterSet ((φ.litterMap L).get hL).1 ⊆
          φ.atomMap.ran) :
    (φ.fillAtomOrbits hφ).Lawful :=
  { atomMap_injective := φ.orbitAtomMap_injective hφ
    litterMap_injective := hφ.litterMap_injective
    atom_mem := φ.orbit_atom_mem hφ hdiff }

variable {φ}
  {hdiff :
    ∀ L hL,
      ((φ.litterMap L).get hL : Set Atom) ∆ litterSet ((φ.litterMap L).get hL).1 ⊆ φ.atomMap.ran}

@[simp]
theorem fillAtomOrbits_atomMap : (φ.fillAtomOrbits hφ).atomMap = φ.orbitAtomMap hφ :=
  rfl

@[simp]
theorem fillAtomOrbits_litterMap : (φ.fillAtomOrbits hφ).litterMap = φ.litterMap :=
  rfl

theorem subset_orbitAtomMap_dom : φ.atomMap.Dom ⊆ (φ.orbitAtomMap hφ).Dom :=
  subset_union_left _ _

theorem subset_orbitAtomMap_ran : φ.atomMap.ran ⊆ (φ.orbitAtomMap hφ).ran :=
  by
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a, subset_orbit_atom_map_dom hφ ha, φ.orbit_atom_map_eq_of_mem_dom hφ _ _⟩

theorem fst_mem_litterPerm_domain_of_mem_map ⦃L : Litter⦄ (hL : (φ.litterMap L).Dom) ⦃a : Atom⦄
    (ha : a ∈ (φ.litterMap L).get hL) : a.1 ∈ (φ.litterPerm hφ).domain :=
  by
  by_cases a.1 = ((φ.litter_map L).get hL).1
  · rw [h]
    refine' Or.inl (Or.inl (Or.inr ⟨L, hL, _⟩))
    rw [rough_litter_map_or_else_of_dom]
  · by_cases h' : a.fst ∈ (φ.litter_perm' hφ).domain
    exact Or.inl h'
    exact Or.inr ⟨banned_litter.diff L hL a ⟨ha, h⟩, h'⟩

theorem fst_mem_litterPerm_domain_of_dom ⦃a : Atom⦄ (ha : a ∈ φ.atomMap.Dom) :
    a.fst ∈ (φ.litterPerm hφ).domain :=
  by
  by_cases h' : a.fst ∈ (φ.litter_perm' hφ).domain
  exact Or.inl h'
  exact Or.inr ⟨banned_litter.atom_dom a ha, h'⟩

theorem fst_mem_litterPerm_domain_of_ran ⦃a : Atom⦄ (ha : a ∈ φ.atomMap.ran) :
    a.fst ∈ (φ.litterPerm hφ).domain :=
  by
  by_cases h' : a.fst ∈ (φ.litter_perm' hφ).domain
  exact Or.inl h'
  obtain ⟨b, hb, rfl⟩ := ha
  exact Or.inr ⟨banned_litter.atom_map b hb, h'⟩

theorem fillAtomOrbits_precise
    (hdiff :
      ∀ L hL,
        ((φ.litterMap L).get hL : Set Atom) ∆ litterSet ((φ.litterMap L).get hL).1 ⊆
          φ.atomMap.ran) :
    Precise (φ.fillAtomOrbits hφ) := by
  intro L hL
  constructor
  · exact subset_trans (hdiff L hL) (subset_orbit_atom_map_ran hφ)
  · intro a ha ha'
    simp only [fill_atom_orbits_atom_map, fill_atom_orbits_litter_map, mem_litter_set,
      orbit_atom_map_dom_iff] at *
    obtain ha | ha | ha := ha
    · have := φ.orbit_atom_map_eq_of_mem_dom hφ a ha
      generalize_proofs at this ha' ⊢
      rw [this, or_iff_not_imp_left]
      intro hmap
      have hfwd : (φ.atom_map a).get ha ∈ φ.need_forward_images := ⟨⟨a, _, rfl⟩, hmap⟩
      refine' Or.inl ⟨hfwd, Or.inl (Or.inl _)⟩
      refine' mem_of_eq_of_mem _ (Or.inl hL)
      rw [← ha', this]
    · refine' Or.inr (Or.inr ⟨_, ⟨L, rfl⟩, _⟩)
      simp only [PFun.mem_dom, Union_exists, mem_Union, mem_image, mem_set_of_eq, SetCoe.exists,
        Subtype.coe_mk, exists_and_right, exists_eq_right, exists_prop]
      have haL : L = φ.litter_perm hφ a.fst :=
        by
        have :=
          (congr_arg Prod.fst (φ.orbit_atom_map_eq_of_need_forward_images hφ a ha)).symm.trans ha'
        rw [← this]
        exact (φ.orbit_set_subset _ ((φ.orbit_set_equiv _).symm _).Prop).1
      refine' ⟨Or.inl (Or.inl (Or.inl hL)), _, _⟩
      · refine' mem_of_eq_of_mem (φ.orbit_atom_map_eq_of_need_forward_images hφ a ha) _
        rw [haL]
        exact ((φ.orbit_set_equiv _).symm _).Prop
      · have := φ.orbit_atom_map_eq_of_need_forward_images hφ a ha
        obtain ⟨hm₁, hm₂⟩ := subtype.coe_eq_iff.mp this.symm
        rw [Equiv.symm_apply_eq, φ.orbit_set_equiv_congr hm₁ haL.symm] at hm₂
        refine' mem_of_eq_of_mem hm₂.symm _
        change
          Sum.elim (fun b => b ∈ φ.next_backward_image_domain hφ L)
            (fun b => b ∈ φ.next_forward_image_domain hφ L) (inr (0, ⟨a, ha.1⟩))
        refine' ⟨ha.2, _⟩
        simp only [Subtype.coe_mk, Function.iterate_one]
        exact haL.symm
    · have := φ.orbit_atom_map_eq_of_mem_next_image_core_domain hφ a ha
      generalize_proofs at this ha' ⊢
      rw [this, next_image_core]
      obtain ⟨_, ⟨L', rfl⟩, _, ⟨hL', rfl⟩, a, hbL, rfl⟩ := ha
      set b := φ.orbit_set_equiv L' a with hb
      clear_value b
      simp only [mem_set_of_eq] at hbL
      rw [← hb] at hbL
      have haL' := (φ.orbit_set_subset _ a.prop).1
      rw [mem_litter_set] at haL'
      have :=
        φ.orbit_set_equiv_congr (φ.mem_orbit_set_of_mem_next_image_core_domain hφ _)
          (φ.orbit_set_subset _ a.prop).1
      rw [Subtype.coe_eta] at this
      rw [this, ← hb]
      obtain ⟨_ | n, b⟩ | ⟨n, b⟩ := b <;>
        simp only [need_backward_images, need_forward_images, elim_inl, elim_inr,
          next_backward_image, next_forward_image] at hbL ⊢
      · exact Or.inl b.prop.1
      · refine' Or.inr (Or.inr _)
        have hbL' := hbL.2
        symm at hbL'
        rw [Function.iterate_succ_apply',
          LocalPerm.eq_symm_apply _ hL' ((φ.litter_perm hφ).symm.iterate_domain hbL.1)] at hbL'
        refine'
          ⟨_, ⟨((φ.litter_perm hφ).symm^[n + 1]) (b : atom).1, rfl⟩, _, ⟨_, rfl⟩,
            ⟨(φ.orbit_set_equiv (φ.litter_perm hφ (a : atom).1)).symm (inl (n, b)), _⟩, _⟩
        · exact (φ.litter_perm hφ).symm.iterate_domain hbL.1
        · rw [← hbL']
          have := ((φ.orbit_set_equiv (φ.litter_perm hφ (a : atom).1)).symm (inl (n, b))).Prop
          rw [haL'] at this ⊢
          exact this
        · simp only [Function.comp_apply, mem_set_of_eq, Subtype.coe_mk, eq_self_iff_true,
            and_true_iff]
          rw [φ.orbit_set_equiv_congr _ hbL'.symm,
            φ.orbit_set_equiv_congr _ (congr_arg (φ.litter_perm hφ) haL'.symm)]
          simp only [Subtype.coe_eta, Equiv.apply_symm_apply, elim_inl]
          exact ⟨hbL.1, rfl⟩
      · refine' Or.inr (Or.inr _)
        refine'
          ⟨_, ⟨(φ.litter_perm hφ^[n + 2]) (b : atom).1, rfl⟩, _, ⟨_, rfl⟩,
            ⟨(φ.orbit_set_equiv (φ.litter_perm hφ (a : atom).1)).symm (inr (n + 1, b)), _⟩, _⟩
        · exact (φ.litter_perm hφ).iterate_domain hbL.1
        · rw [Function.iterate_succ_apply', hbL.2, haL']
          exact ((φ.orbit_set_equiv _).symm _).Prop
        · simp only [Function.comp_apply, mem_set_of_eq, Subtype.coe_mk, eq_self_iff_true,
            and_true_iff]
          have := congr_arg (φ.litter_perm hφ) hbL.2
          rw [← Function.iterate_succ_apply' (φ.litter_perm hφ) (n + 1)] at this
          rw [φ.orbit_set_equiv_congr _ this,
            φ.orbit_set_equiv_congr _ (congr_arg (φ.litter_perm hφ) haL'.symm)]
          simp only [Function.iterate_succ, Function.comp_apply, Subtype.coe_eta,
            Equiv.apply_symm_apply, elim_inr]
          exact ⟨hbL.1, rfl⟩
      · refine' ⟨_, ⟨L', rfl⟩, _, ⟨hL', rfl⟩, a, _, rfl⟩
        rw [mem_set_of_eq, ← hb]
        exact hbL
  · rw [fill_atom_orbits_litter_map] at hL
    rintro a ⟨ha₁ | ⟨ha₁, ha₁'⟩ | ha₁, ha₂⟩ <;>
      simp only [fill_atom_orbits_atom_map, fill_atom_orbits_litter_map, orbit_atom_map_dom,
        mem_inter_iff, mem_union, SetLike.mem_coe] at *
    · by_cases ha₃ : a ∈ φ.atom_map.ran
      · obtain ⟨b, hb₁, hb₂⟩ := ha₃
        refine' ⟨b, Or.inl hb₁, _⟩
        rw [orbit_atom_map_eq_of_mem_dom]
        exact hb₂
      · refine'
          ⟨(φ.orbit_set_equiv ((φ.litter_perm hφ).symm a.1)).symm (inl (0, ⟨a, ha₁, ha₃⟩)), _, _⟩
        · refine' Or.inr (Or.inr ⟨_, ⟨(φ.litter_perm hφ).symm a.1, rfl⟩, _, ⟨_, rfl⟩, _⟩)
          ·
            exact
              (φ.litter_perm hφ).symm.map_domain (fst_mem_litter_perm_domain_of_mem_map hφ hL ha₂)
          refine' ⟨_, _, rfl⟩
          simp only [mem_set_of_eq, Equiv.apply_symm_apply, elim_inl]
          exact ⟨fst_mem_litter_perm_domain_of_mem_map hφ hL ha₂, rfl⟩
        · rw [orbit_atom_map_eq_of_mem_next_image_core_domain, next_image_core]
          have :
            ((φ.orbit_set_equiv ((φ.litter_perm hφ).symm a.fst)).symm (inl (0, ⟨a, _⟩)) :
                  atom).fst =
              (φ.litter_perm hφ).symm a.fst :=
            by
            exact (φ.orbit_set_subset _ ((φ.orbit_set_equiv _).symm _).Prop).1
            exact ⟨ha₁, ha₃⟩
          rw [φ.orbit_set_equiv_congr _ this]
          simp only [Equiv.apply_symm_apply, elim_inl, Subtype.coe_eta, next_backward_image,
            Subtype.coe_mk]
    · obtain ⟨⟨b, hb₁, hb₂⟩, ha₁⟩ := ha₁
      rw [← hb₂]
      refine' ⟨b, Or.inl hb₁, _⟩
      rw [orbit_atom_map_eq_of_mem_dom]
    · obtain ⟨a', ha'⟩ :=
        (φ.orbit_set_equiv a.fst).symm.Surjective
          ⟨a, φ.mem_orbit_set_of_mem_next_image_core_domain hφ ha₁⟩
      obtain ⟨n, a'⟩ | ⟨_ | n, a'⟩ := a'
      · have :
          ((φ.orbit_set_equiv (((φ.litter_perm hφ).symm^[n + 2]) (a' : atom).fst)).symm
                (inl (n + 1, a')) :
              atom) ∈
            φ.next_image_core_domain hφ :=
          by
          refine' ⟨_, ⟨((φ.litter_perm hφ).symm^[n + 2]) (a' : atom).fst, rfl⟩, _, ⟨_, rfl⟩, _⟩
          exact
            (φ.litter_perm hφ).symm.iterate_domain (fst_mem_litter_perm_domain_of_dom hφ a'.prop.1)
          refine' ⟨_, _, rfl⟩
          simp only [mem_set_of_eq, Equiv.apply_symm_apply, elim_inl]
          exact ⟨fst_mem_litter_perm_domain_of_dom hφ a'.prop.1, rfl⟩
        refine' ⟨_, Or.inr (Or.inr this), _⟩
        rw [orbit_atom_map_eq_of_mem_next_image_core_domain]
        rw [next_image_core]
        have :
          ((φ.orbit_set_equiv (((φ.litter_perm hφ).symm^[n + 2]) (a' : atom).fst)).symm
                  (inl (n + 1, a')) :
                atom).fst =
            ((φ.litter_perm hφ).symm^[n + 2]) (a' : atom).fst :=
          (φ.orbit_set_subset _ ((φ.orbit_set_equiv _).symm _).Prop).1
        rw [φ.orbit_set_equiv_congr _ this]
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply, elim_inl, next_backward_image]
        have := congr_arg Subtype.val ha'
        simp only [Subtype.val_eq_coe] at this
        rw [← this]
        refine' φ.orbit_set_equiv_symm_congr _
        have := (φ.orbit_set_subset _ ((φ.orbit_set_equiv _).symm _).Prop).1
        rw [mem_litter_set] at this
        rw [this]
        have := φ.orbit_set_equiv_elim_of_mem_next_image_core_domain hφ ha₁
        rw [← ha'] at this
        simp only [Equiv.apply_symm_apply, elim_inl, next_backward_image_domain,
          Function.comp_apply, mem_set_of_eq] at this
        rw [← this.2, Function.iterate_succ_apply', LocalPerm.right_inv]
        exact (φ.litter_perm hφ).symm.iterate_domain this.1
      · have := φ.orbit_set_equiv_elim_of_mem_next_image_core_domain hφ ha₁
        rw [← ha'] at this
        simp only [Equiv.apply_symm_apply, elim_inr, next_forward_image_domain, Function.comp_apply,
          mem_set_of_eq, Function.iterate_one] at this
        refine' ⟨a', Or.inr (Or.inl ⟨a'.prop, this.1⟩), _⟩
        rw [orbit_atom_map_eq_of_need_forward_images, φ.orbit_set_equiv_symm_congr this.2,
          Subtype.coe_eta, ha']
        rfl
      · have :
          ((φ.orbit_set_equiv ((φ.litter_perm hφ^[n + 1]) (a' : atom).fst)).symm (inr (n, a')) :
              atom) ∈
            φ.next_image_core_domain hφ :=
          by
          refine' ⟨_, ⟨(φ.litter_perm hφ^[n + 1]) (a' : atom).fst, rfl⟩, _, ⟨_, rfl⟩, _⟩
          exact (φ.litter_perm hφ).iterate_domain (fst_mem_litter_perm_domain_of_ran hφ a'.prop.1)
          refine' ⟨_, _, rfl⟩
          simp only [mem_set_of_eq, Equiv.apply_symm_apply, elim_inl]
          exact ⟨fst_mem_litter_perm_domain_of_ran hφ a'.prop.1, rfl⟩
        refine' ⟨_, Or.inr (Or.inr this), _⟩
        rw [orbit_atom_map_eq_of_mem_next_image_core_domain]
        rw [next_image_core]
        have :
          ((φ.orbit_set_equiv ((φ.litter_perm hφ^[n + 1]) (a' : atom).fst)).symm (inr (n, a')) :
                atom).fst =
            (φ.litter_perm hφ^[n + 1]) (a' : atom).fst :=
          (φ.orbit_set_subset _ ((φ.orbit_set_equiv _).symm _).Prop).1
        rw [φ.orbit_set_equiv_congr _ this]
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply, elim_inl, next_backward_image]
        have := congr_arg Subtype.val ha'
        simp only [Subtype.val_eq_coe] at this
        rw [← this]
        refine' φ.orbit_set_equiv_symm_congr _
        have := (φ.orbit_set_subset _ ((φ.orbit_set_equiv _).symm _).Prop).1
        rw [mem_litter_set] at this
        rw [this]
        have := φ.orbit_set_equiv_elim_of_mem_next_image_core_domain hφ ha₁
        rw [← ha'] at this
        simp only [Equiv.apply_symm_apply, elim_inr, next_forward_image_domain, Function.comp_apply,
          mem_set_of_eq] at this
        rw [← this.2, Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply']

end NearLitterAction

end ConNf
