import phase2.weak_approx

open cardinal quiver set sum with_bot
open_locale cardinal classical pointwise

universe u

namespace con_nf
variables [params.{u}]

/-!
# Filling in orbits of atoms
-/

namespace weak_near_litter_approx

variables (w : weak_near_litter_approx)

def need_forward_images : set atom := w.atom_map.ran \ w.atom_map.dom
def need_backward_images : set atom := w.atom_map.dom \ w.atom_map.ran

lemma atom_map_ran_small : small w.atom_map.ran :=
begin
  have : small (w.atom_map_or_else '' w.atom_map.dom) := small.image w.atom_map_dom_small,
  refine small.mono _ this,
  rintros _ ⟨a, ha, rfl⟩,
  refine ⟨a, ha, _⟩,
  rw atom_map_or_else_of_dom,
end

lemma need_forward_images_small : small w.need_forward_images :=
small.mono (diff_subset _ _) w.atom_map_ran_small

lemma need_backward_images_small : small w.need_backward_images :=
small.mono (diff_subset _ _) w.atom_map_dom_small

lemma mk_diff_dom_ran (L : litter) :
  #(litter_set L \ (w.atom_map.dom ∪ w.atom_map.ran) : set atom) = #κ :=
begin
  refine le_antisymm _ _,
  { refine ⟨⟨λ a, a.1.2, _⟩⟩,
    intros a b h,
    refine subtype.coe_injective (prod.ext (a.prop.1.trans b.prop.1.symm) _),
    simp only [subtype.val_eq_coe] at h,
    exact h, },
  { by_contra' h,
    have := add_lt_of_lt κ_regular.aleph_0_le h
      (small.union w.atom_map_dom_small w.atom_map_ran_small),
    have := (le_mk_diff_add_mk (litter_set L) _).trans_lt this,
    simp only [mk_litter_set, lt_self_iff_false] at this,
    exact this, },
end

lemma need_images_small (L : litter) :
  #(ℕ × w.need_backward_images ⊕ ℕ × w.need_forward_images) < #κ :=
begin
  simp only [mk_prod, mk_denumerable, lift_aleph_0, lift_uzero, mk_diff_dom_ran, mk_sum, lift_id],
  rw ← mul_add,
  refine lt_of_le_of_lt (mul_le_max _ _) (max_lt (max_lt _ _) _),
  exact Λ_limit.aleph_0_le.trans_lt Λ_lt_κ,
  exact add_lt_of_lt κ_regular.aleph_0_le w.need_backward_images_small w.need_forward_images_small,
  exact Λ_limit.aleph_0_le.trans_lt Λ_lt_κ,
end

lemma le_mk_diff_dom_ran (L : litter) :
  #(ℕ × w.need_backward_images ⊕ ℕ × w.need_forward_images) ≤
    #(litter_set L \ (w.atom_map.dom ∪ w.atom_map.ran) : set atom) :=
begin
  rw [mk_diff_dom_ran],
  exact (w.need_images_small L).le,
end

def orbit_set (L : litter) : set atom :=
(le_mk_iff_exists_subset.mp (w.le_mk_diff_dom_ran L)).some

lemma orbit_set_subset (L : litter) :
  w.orbit_set L ⊆ litter_set L \ (w.atom_map.dom ∪ w.atom_map.ran) :=
(le_mk_iff_exists_subset.mp (w.le_mk_diff_dom_ran L)).some_spec.1

lemma not_mem_need_forward_images_of_mem_orbit_set {a : atom} {L : litter}
  (h : a ∈ w.orbit_set L) : a ∉ w.need_forward_images :=
λ ha, (w.orbit_set_subset L h).2 (or.inr ha.1)

lemma not_mem_need_backward_images_of_mem_orbit_set {a : atom} {L : litter}
  (h : a ∈ w.orbit_set L) : a ∉ w.need_backward_images :=
λ ha, (w.orbit_set_subset L h).2 (or.inl ha.1)

lemma mk_orbit_set (L : litter) :
  #(w.orbit_set L) = #(ℕ × w.need_backward_images ⊕ ℕ × w.need_forward_images) :=
(le_mk_iff_exists_subset.mp (w.le_mk_diff_dom_ran L)).some_spec.2

@[irreducible] noncomputable def orbit_set_equiv (L : litter) :
  w.orbit_set L ≃ ℕ × w.need_backward_images ⊕ ℕ × w.need_forward_images :=
(cardinal.eq.mp (w.mk_orbit_set L)).some

lemma orbit_set_equiv_injective {a₁ a₂ : ℕ × w.need_backward_images ⊕ ℕ × w.need_forward_images}
  {L₁ L₂ : litter} (h : ((w.orbit_set_equiv L₁).symm a₁ : atom) = (w.orbit_set_equiv L₂).symm a₂) :
  L₁ = L₂ ∧ a₁ = a₂ :=
begin
  have h₁ := w.orbit_set_subset L₁ ((w.orbit_set_equiv L₁).symm a₁).prop,
  have h₂ := w.orbit_set_subset L₂ ((w.orbit_set_equiv L₂).symm a₂).prop,
  rw h at h₁,
  cases eq_of_mem_litter_set_of_mem_litter_set h₁.1 h₂.1,
  simp only [subtype.coe_inj, embedding_like.apply_eq_iff_eq] at h,
  exact ⟨rfl, h⟩,
end

lemma orbit_set_equiv_congr {L L' : litter} {a : atom} (ha : a ∈ w.orbit_set L) (h : L = L') :
  w.orbit_set_equiv L ⟨a, ha⟩ = w.orbit_set_equiv L' ⟨a, h ▸ ha⟩ :=
by cases h; refl

lemma orbit_set_equiv_symm_congr {L L' : litter}
  {a : ℕ × ↥(w.need_backward_images) ⊕ ℕ × ↥(w.need_forward_images)} (h : L = L') :
  ((w.orbit_set_equiv L).symm a : atom) = (w.orbit_set_equiv L').symm a :=
by cases h; refl

lemma orbit_set_small (L : litter) : small (w.orbit_set L) :=
begin
  rw [small, mk_orbit_set],
  exact w.need_images_small L,
end

noncomputable def next_forward_image (L : litter) (a : ℕ × w.need_forward_images) : atom :=
(w.orbit_set_equiv (w.litter_perm L)).symm (inr (a.1 + 1, a.2))

noncomputable def next_backward_image (L : litter) : ℕ × w.need_backward_images → atom
| (0, a) := a
| (n + 1, a) := (w.orbit_set_equiv (w.litter_perm L)).symm (inl (n, a))

def next_forward_image_domain (L : litter) : set (ℕ × w.need_forward_images) :=
{a | (a.2 : atom).1 ∈ w.litter_perm.domain ∧ (w.litter_perm^[a.1 + 1] (a.2 : atom).1 = L)}

def next_backward_image_domain (L : litter) : set (ℕ × w.need_backward_images) :=
{a | (a.2 : atom).1 ∈ w.litter_perm.domain ∧ (w.litter_perm.symm^[a.1 + 1] (a.2 : atom).1 = L)}

lemma mk_mem_next_forward_image_domain (L : litter) (n : ℕ) (a : w.need_forward_images) :
  (n, a) ∈ w.next_forward_image_domain L ↔
    (a : atom).1 ∈ w.litter_perm.domain ∧ (w.litter_perm^[n + 1] (a : atom).1 = L) := iff.rfl

lemma mk_mem_next_backward_image_domain (L : litter) (n : ℕ) (a : w.need_backward_images) :
  (n, a) ∈ w.next_backward_image_domain L ↔
    (a : atom).1 ∈ w.litter_perm.domain ∧ (w.litter_perm.symm^[n + 1] (a : atom).1 = L) := iff.rfl

lemma next_forward_image_eq {L₁ L₂ : litter} {a b : ℕ × w.need_forward_images}
  (hL₁ : L₁ ∈ w.litter_perm.domain) (hL₂ : L₂ ∈ w.litter_perm.domain)
  (h : w.next_forward_image L₁ a = w.next_forward_image L₂ b) : L₁ = L₂ :=
begin
  rw [next_forward_image, next_forward_image] at h,
  have ha := w.orbit_set_subset _
    ((w.orbit_set_equiv (w.litter_perm L₁)).symm (inr (a.1 + 1, a.2))).prop,
  have hb := w.orbit_set_subset _
    ((w.orbit_set_equiv (w.litter_perm L₂)).symm (inr (b.1 + 1, b.2))).prop,
  rw h at ha,
  refine w.litter_perm.inj_on hL₁ hL₂ _,
  exact eq_of_mem_litter_set_of_mem_litter_set ha.1 hb.1,
end

lemma next_backward_image_eq {L₁ L₂ : litter} {a b : ℕ × w.need_backward_images}
  (ha : a ∈ w.next_backward_image_domain L₁) (hb : b ∈ w.next_backward_image_domain L₂)
  (hL₁ : L₁ ∈ w.litter_perm.domain) (hL₂ : L₂ ∈ w.litter_perm.domain)
  (h : w.next_backward_image L₁ a = w.next_backward_image L₂ b) : L₁ = L₂ :=
begin
  obtain ⟨m, a⟩ := a,
  obtain ⟨n, b⟩ := b,
  cases m;
  cases n;
  rw [next_backward_image, next_backward_image] at h,
  { simp only [next_backward_image_domain, function.iterate_succ, function.comp_app, mem_set_of_eq,
      function.iterate_zero, id.def] at ha hb,
    rw [← h, ha.2] at hb,
    exact hb.2, },
  { rw subtype.coe_eq_iff at h,
    obtain ⟨h₁, h₂⟩ := h,
    cases w.not_mem_need_backward_images_of_mem_orbit_set ((w.orbit_set_equiv _).symm _).prop h₁, },
  { symmetry' at h,
    rw subtype.coe_eq_iff at h,
    obtain ⟨h₁, h₂⟩ := h,
    cases w.not_mem_need_backward_images_of_mem_orbit_set ((w.orbit_set_equiv _).symm _).prop h₁, },
  { have ha := w.orbit_set_subset _
      ((w.orbit_set_equiv (w.litter_perm L₁)).symm (inl (m, a))).prop,
    have hb := w.orbit_set_subset _
      ((w.orbit_set_equiv (w.litter_perm L₂)).symm (inl (n, b))).prop,
    rw h at ha,
    refine w.litter_perm.inj_on hL₁ hL₂ _,
    exact eq_of_mem_litter_set_of_mem_litter_set ha.1 hb.1, },
end

lemma next_forward_image_injective {L : litter} {a b : ℕ × w.need_forward_images}
  (h : w.next_forward_image L a = w.next_forward_image L b) : a = b :=
begin
  simp only [next_forward_image, subtype.coe_inj, embedding_like.apply_eq_iff_eq, prod.mk.inj_iff,
    add_left_inj] at h,
  exact prod.ext h.1 h.2,
end

lemma next_backward_image_injective {L : litter} {a b : ℕ × w.need_backward_images}
  (ha : a ∈ w.next_backward_image_domain L) (hb : b ∈ w.next_backward_image_domain L)
  (h : w.next_backward_image L a = w.next_backward_image L b) : a = b :=
begin
  obtain ⟨m, a⟩ := a,
  obtain ⟨n, b⟩ := b,
  cases m;
  cases n;
  simp only [prod.mk.inj_iff, subtype.coe_inj, embedding_like.apply_eq_iff_eq, prod.mk.inj_iff,
    false_and, nat.nat_zero_eq_zero, prod.mk.inj_iff, next_backward_image, prod.mk.inj_iff,
    eq_self_iff_true, true_and, subtype.coe_inj] at h ⊢,
  { exact h, },
  { rw subtype.coe_eq_iff at h,
    obtain ⟨h₁, h₂⟩ := h,
    cases w.not_mem_need_backward_images_of_mem_orbit_set ((w.orbit_set_equiv _).symm _).prop h₁, },
  { symmetry' at h,
    rw subtype.coe_eq_iff at h,
    obtain ⟨h₁, h₂⟩ := h,
    cases w.not_mem_need_backward_images_of_mem_orbit_set ((w.orbit_set_equiv _).symm _).prop h₁, },
  { exact h, },
end

lemma next_forward_image_injective' {L₁ L₂ : litter} {a b : ℕ × w.need_forward_images}
  (hL₁ : L₁ ∈ w.litter_perm.domain) (hL₂ : L₂ ∈ w.litter_perm.domain)
  (h : w.next_forward_image L₁ a = w.next_forward_image L₂ b) : a = b :=
begin
  cases w.next_forward_image_eq hL₁ hL₂ h,
  exact w.next_forward_image_injective h,
end

lemma next_backward_image_injective' {L₁ L₂ : litter} {a b : ℕ × w.need_backward_images}
  (ha : a ∈ w.next_backward_image_domain L₁) (hb : b ∈ w.next_backward_image_domain L₂)
  (hL₁ : L₁ ∈ w.litter_perm.domain) (hL₂ : L₂ ∈ w.litter_perm.domain)
  (h : w.next_backward_image L₁ a = w.next_backward_image L₂ b) : a = b :=
begin
  cases w.next_backward_image_eq ha hb hL₁ hL₂ h,
  exact w.next_backward_image_injective ha hb h,
end

lemma next_forward_image_ne_next_backward_image {L₁ L₂ : litter}
  {a : ℕ × w.need_forward_images} {b : ℕ × w.need_backward_images} :
  w.next_forward_image L₁ a ≠ w.next_backward_image L₂ b :=
begin
  obtain ⟨n, b⟩ := b,
  cases n,
  { rw [next_forward_image, next_backward_image],
    refine (ne_of_mem_of_not_mem _
      (w.orbit_set_subset _ ((w.orbit_set_equiv _).symm _).prop).2).symm,
    exact or.inl b.prop.1, },
  { rw [next_forward_image, next_backward_image],
    intro h,
    cases (w.orbit_set_equiv_injective h).2, },
end

noncomputable def next_image_core (a : atom) (L : litter) (ha : a ∈ w.orbit_set L) : atom :=
(w.orbit_set_equiv L ⟨a, ha⟩).elim (w.next_backward_image L) (w.next_forward_image L)

def next_image_core_domain : set atom :=
⋃ L ∈ w.litter_perm.domain, coe '' {a : w.orbit_set L | (w.orbit_set_equiv L a).elim
  (λ b, b ∈ w.next_backward_image_domain L) (λ b, b ∈ w.next_forward_image_domain L)}

lemma next_image_core_domain_small : small w.next_image_core_domain :=
small.bUnion w.litter_perm_domain_small
  (λ L hL, small.image (lt_of_le_of_lt (cardinal.mk_subtype_le _) (w.orbit_set_small L)))

lemma litter_map_dom_of_mem_next_image_core_domain {a : atom} (h : a ∈ w.next_image_core_domain) :
  a.1 ∈ w.litter_perm.domain :=
begin
  rw next_image_core_domain at h,
  simp only [pfun.mem_dom, Union_exists, mem_Union, mem_image, mem_set_of_eq, set_coe.exists,
    subtype.coe_mk, exists_and_distrib_right, exists_eq_right, exists_prop] at h,
  obtain ⟨L, hL, ha, h⟩ := h,
  have := (w.orbit_set_subset L ha).1,
  rw mem_litter_set at this,
  rw this,
  exact hL,
end

lemma mem_orbit_set_of_mem_next_image_core_domain {a : atom} (h : a ∈ w.next_image_core_domain) :
  a ∈ w.orbit_set a.1 :=
begin
  rw next_image_core_domain at h,
  simp only [pfun.mem_dom, Union_exists, mem_Union, mem_image, mem_set_of_eq, set_coe.exists,
    subtype.coe_mk, exists_and_distrib_right, exists_eq_right, exists_prop] at h,
  obtain ⟨L, hL, ha, h⟩ := h,
  have := (w.orbit_set_subset L ha).1,
  rw mem_litter_set at this,
  rw this,
  exact ha,
end

lemma orbit_set_equiv_elim_of_mem_next_image_core_domain {a : atom}
  (h : a ∈ w.next_image_core_domain) :
  (w.orbit_set_equiv a.1 ⟨a, w.mem_orbit_set_of_mem_next_image_core_domain h⟩).elim
    (λ c, c ∈ w.next_backward_image_domain a.1) (λ c, c ∈ w.next_forward_image_domain a.1) :=
begin
  rw next_image_core_domain at h,
  simp only [pfun.mem_dom, Union_exists, mem_Union, mem_image, mem_set_of_eq, set_coe.exists,
    subtype.coe_mk, exists_and_distrib_right, exists_eq_right, exists_prop] at h,
  obtain ⟨L, hL, ha, h⟩ := h,
  have := (w.orbit_set_subset L ha).1,
  rw mem_litter_set at this,
  cases this,
  exact h,
end

lemma next_image_core_injective (a b : atom)
  (ha : a ∈ w.next_image_core_domain) (hb : b ∈ w.next_image_core_domain)
  (h : w.next_image_core a a.1 (w.mem_orbit_set_of_mem_next_image_core_domain ha) =
    w.next_image_core b b.1 (w.mem_orbit_set_of_mem_next_image_core_domain hb)) : a = b :=
begin
  rw [next_image_core, next_image_core] at h,
  obtain ⟨a', ha'⟩ := (w.orbit_set_equiv a.fst).symm.surjective
    ⟨a, w.mem_orbit_set_of_mem_next_image_core_domain ha⟩,
  obtain ⟨b', hb'⟩ := (w.orbit_set_equiv b.fst).symm.surjective
    ⟨b, w.mem_orbit_set_of_mem_next_image_core_domain hb⟩,
  have hae := w.orbit_set_equiv_elim_of_mem_next_image_core_domain ha,
  have hbe := w.orbit_set_equiv_elim_of_mem_next_image_core_domain hb,
  simp only [← ha', ← hb', equiv.apply_symm_apply] at h hae hbe,
  obtain (⟨m, a'⟩ | ⟨m, a'⟩) := a';
  obtain (⟨n, b'⟩ | ⟨n, b'⟩) := b';
  simp only [elim_inl, elim_inr,
    mk_mem_next_backward_image_domain, mk_mem_next_forward_image_domain] at h hae hbe,
  { cases w.next_backward_image_injective' _ _ _ _ h,
    { rw hae.2 at hbe,
      rw [subtype.ext_iff, subtype.coe_mk] at ha' hb',
      rw [← ha', ← hb', hbe.2], },
    { exact hae, },
    { exact hbe, },
    { exact w.litter_map_dom_of_mem_next_image_core_domain ha, },
    { exact w.litter_map_dom_of_mem_next_image_core_domain hb, }, },
  { cases w.next_forward_image_ne_next_backward_image h.symm, },
  { cases w.next_forward_image_ne_next_backward_image h, },
  { cases w.next_forward_image_injective' _ _ h,
    { rw hae.2 at hbe,
      rw [subtype.ext_iff, subtype.coe_mk] at ha' hb',
      rw [← ha', ← hb'],
      exact w.orbit_set_equiv_symm_congr hbe.2, },
    { exact w.litter_map_dom_of_mem_next_image_core_domain ha, },
    { exact w.litter_map_dom_of_mem_next_image_core_domain hb, }, },
end

def next_image_domain : set atom :=
(w.need_forward_images ∩ {a | a.1 ∈ w.litter_perm.domain}) ∪ w.next_image_core_domain

noncomputable def next_image (a : atom) (ha : a ∈ w.next_image_domain) : atom :=
ha.elim'
  (λ ha', (w.orbit_set_equiv (w.litter_perm a.1)).symm (inr (0, ⟨a, ha'.1⟩)))
  (w.next_image_core a a.1 ∘ w.mem_orbit_set_of_mem_next_image_core_domain)

lemma next_image_domain_small : small w.next_image_domain :=
small.union
  (small.mono (inter_subset_left _ _) w.need_forward_images_small)
  w.next_image_core_domain_small

lemma disjoint_need_forward_images_next_image_core_domain :
  disjoint w.need_forward_images w.next_image_core_domain :=
begin
  rw set.disjoint_iff,
  rintro a ⟨ha₁, ha₂⟩,
  exact (w.orbit_set_subset _ (w.mem_orbit_set_of_mem_next_image_core_domain ha₂)).2 (or.inr ha₁.1),
end

lemma next_image_eq_of_need_forward_images (a : atom)
  (ha : a ∈ w.need_forward_images ∧ a.1 ∈ w.litter_perm.domain) :
  w.next_image a (or.inl ha) =
  (w.orbit_set_equiv (w.litter_perm a.1)).symm (inr (0, ⟨a, ha.1⟩)) :=
or.elim'_left _ _ _ ha

lemma next_image_eq_of_mem_next_image_core_domain (a : atom) (ha : a ∈ w.next_image_core_domain) :
  w.next_image a (or.inr ha) =
  w.next_image_core a a.1 (w.mem_orbit_set_of_mem_next_image_core_domain ha) :=
begin
  refine or.elim'_right _ _ _ _,
  exact λ h, set.disjoint_right.mp w.disjoint_need_forward_images_next_image_core_domain ha h.1,
end

lemma orbit_set_equiv_ne_next_image_core (a b : atom)
  (ha : a ∈ w.need_forward_images ∧ a.fst ∈ w.litter_perm.domain)
  (hb : b ∈ w.next_image_core_domain) :
  (((w.orbit_set_equiv (w.litter_perm a.fst)).symm) (inr (0, ⟨a, ha.1⟩)) : atom) ≠
    w.next_image_core b b.fst (w.mem_orbit_set_of_mem_next_image_core_domain hb) :=
begin
  obtain ⟨b', hb'⟩ := (w.orbit_set_equiv b.fst).symm.surjective
    ⟨b, w.mem_orbit_set_of_mem_next_image_core_domain hb⟩,
  rw equiv.symm_apply_eq at hb',
  intro h,
  rw next_image_core at h,
  rw ← hb' at h,
  obtain (⟨_ | n, b'⟩ | b') := b';
  simp only [elim_inl, elim_inr, next_backward_image, next_forward_image] at h,
  { have := w.orbit_set_subset _ ((w.orbit_set_equiv _).symm _).prop,
    rw h at this,
    exact this.2 (or.inl b'.prop.1), },
  { cases (w.orbit_set_equiv_injective h).2, },
  { cases (w.orbit_set_equiv_injective h).2, },
end

lemma next_image_injective (a b : atom)
  (ha : a ∈ w.next_image_domain) (hb : b ∈ w.next_image_domain)
  (h : w.next_image a ha = w.next_image b hb) : a = b :=
begin
  cases ha;
  cases hb;
  simp only [next_image_eq_of_need_forward_images,
    next_image_eq_of_mem_next_image_core_domain] at h,
  { have := w.orbit_set_equiv_injective h,
    simp only [prod.mk.inj_iff, eq_self_iff_true, subtype.mk_eq_mk, true_and] at this,
    exact this.2, },
  { cases w.orbit_set_equiv_ne_next_image_core _ _ _ _ h, },
  { cases w.orbit_set_equiv_ne_next_image_core _ _ _ _ h.symm, },
  { refine w.next_image_core_injective a b ha hb h, },
end

noncomputable def orbit_atom_map : atom →. atom :=
λ a, {
  dom := (w.atom_map a).dom ∨ a ∈ w.next_image_domain,
  get := λ h, or.elim' h (w.atom_map a).get (w.next_image a)
}

@[simp] lemma orbit_atom_map_dom_iff (a : atom) :
  (w.orbit_atom_map a).dom ↔ (w.atom_map a).dom ∨ a ∈ w.next_image_domain := iff.rfl

@[simp] lemma orbit_atom_map_dom :
  w.orbit_atom_map.dom = w.atom_map.dom ∪ w.next_image_domain := rfl

lemma disjoint_atom_map_dom_next_image_domain : disjoint w.atom_map.dom w.next_image_domain :=
begin
  rw set.disjoint_iff,
  rintros a ⟨h₁, h₂ | h₂⟩,
  { exact h₂.1.2 h₁, },
  { exact (w.orbit_set_subset _
      (w.mem_orbit_set_of_mem_next_image_core_domain h₂)).2 (or.inl h₁), },
end

lemma orbit_atom_map_eq_of_mem_dom (a : atom) (ha : (w.atom_map a).dom) :
  (w.orbit_atom_map a).get (or.inl ha) = (w.atom_map a).get ha :=
or.elim'_left _ _ _ _

lemma orbit_atom_map_eq_of_mem_next_image_domain (a : atom) (ha : a ∈ w.next_image_domain) :
  (w.orbit_atom_map a).get (or.inr ha) = w.next_image a ha :=
or.elim'_right _ _ _ (id set.disjoint_right.mp w.disjoint_atom_map_dom_next_image_domain ha)

lemma orbit_atom_map_eq_of_need_forward_images (a : atom)
  (ha : a ∈ w.need_forward_images ∧ a.fst ∈ w.litter_perm.domain) :
  (w.orbit_atom_map a).get (or.inr (or.inl ha)) =
  (w.orbit_set_equiv (w.litter_perm a.1)).symm (inr (0, ⟨a, ha.1⟩)) :=
begin
  unfold orbit_atom_map,
  simp only,
  rw or.elim'_right,
  exact w.next_image_eq_of_need_forward_images a ha,
  exact id set.disjoint_right.mp w.disjoint_atom_map_dom_next_image_domain (or.inl ha),
end

lemma orbit_atom_map_eq_of_mem_next_image_core_domain (a : atom)
  (ha : a ∈ w.next_image_core_domain) :
  (w.orbit_atom_map a).get (or.inr (or.inr ha)) =
    w.next_image_core a a.1 (w.mem_orbit_set_of_mem_next_image_core_domain ha) :=
begin
  unfold orbit_atom_map,
  simp only,
  rw or.elim'_right,
  exact w.next_image_eq_of_mem_next_image_core_domain a ha,
  exact id set.disjoint_right.mp w.disjoint_atom_map_dom_next_image_domain (or.inr ha),
end

lemma orbit_atom_map_dom_small : small w.orbit_atom_map.dom :=
small.union w.atom_map_dom_small w.next_image_domain_small

lemma orbit_atom_map_apply_ne_of_need_forward_images ⦃a b : atom⦄
  (ha : (w.atom_map a).dom) (hb : b ∈ w.need_forward_images ∧ b.fst ∈ w.litter_perm.domain) :
  (w.orbit_atom_map a).get (or.inl ha) ≠ (w.orbit_atom_map b).get (or.inr (or.inl hb)) :=
begin
  rw [orbit_atom_map_eq_of_mem_dom, orbit_atom_map_eq_of_need_forward_images],
  intro h,
  have := w.orbit_set_subset _ ((w.orbit_set_equiv _).symm _).prop,
  rw ← h at this,
  exact this.2 (or.inr ⟨a, ha, rfl⟩),
end

lemma orbit_atom_map_apply_ne_of_mem_next_image_core_domain ⦃a b : atom⦄
  (ha : (w.atom_map a).dom) (hb : b ∈ w.next_image_core_domain) :
  (w.orbit_atom_map a).get (or.inl ha) ≠ (w.orbit_atom_map b).get (or.inr (or.inr hb)) :=
begin
  obtain ⟨b', hb'⟩ := (w.orbit_set_equiv b.fst).symm.surjective
    ⟨b, w.mem_orbit_set_of_mem_next_image_core_domain hb⟩,
  rw [orbit_atom_map_eq_of_mem_dom, orbit_atom_map_eq_of_mem_next_image_core_domain,
    next_image_core, ← hb', equiv.apply_symm_apply],
  obtain (⟨_ | n, b'⟩ | ⟨n, b'⟩) := b';
  simp only [elim_inr, elim_inl, nat.nat_zero_eq_zero, next_backward_image, next_forward_image],
  { intro h,
    have := b'.prop.2,
    rw ← h at this,
    exact this ⟨a, ha, rfl⟩, },
  { intro h,
    have := (w.orbit_set_subset _ ((w.orbit_set_equiv _).symm _).prop).2,
    rw ← h at this,
    exact this (or.inr ⟨a, ha, rfl⟩), },
  { intro h,
    have := (w.orbit_set_subset _ ((w.orbit_set_equiv _).symm _).prop).2,
    rw ← h at this,
    exact this (or.inr ⟨a, ha, rfl⟩), },
end

lemma orbit_atom_map_apply_ne ⦃a b : atom⦄
  (ha : (w.atom_map a).dom) (hb : b ∈ w.next_image_domain) :
  (w.orbit_atom_map a).get (or.inl ha) ≠ (w.orbit_atom_map b).get (or.inr hb) :=
begin
  cases hb,
  exact w.orbit_atom_map_apply_ne_of_need_forward_images ha hb,
  exact w.orbit_atom_map_apply_ne_of_mem_next_image_core_domain ha hb,
end

lemma orbit_atom_map_injective ⦃a b : atom⦄
  (ha : (w.orbit_atom_map a).dom) (hb : (w.orbit_atom_map b).dom)
  (h : (w.orbit_atom_map a).get ha = (w.orbit_atom_map b).get hb) : a = b :=
begin
  cases ha;
  cases hb,
  { rw [orbit_atom_map_eq_of_mem_dom, orbit_atom_map_eq_of_mem_dom] at h,
    exact w.atom_map_injective ha hb h, },
  { cases w.orbit_atom_map_apply_ne ha hb h, },
  { cases w.orbit_atom_map_apply_ne hb ha h.symm, },
  { rw [orbit_atom_map_eq_of_mem_next_image_domain,
      orbit_atom_map_eq_of_mem_next_image_domain] at h,
    exact w.next_image_injective a b ha hb h, },
end

lemma next_image_core_atom_mem_litter_map
  (a : atom) (ha : a ∈ w.next_image_core_domain) :
  w.next_image_core a a.fst (w.mem_orbit_set_of_mem_next_image_core_domain ha) ∈
    litter_set (w.litter_perm a.fst) :=
begin
  have hL := w.litter_map_dom_of_mem_next_image_core_domain ha,
  have := w.mem_orbit_set_of_mem_next_image_core_domain ha,
  obtain ⟨a', ha'⟩ := (w.orbit_set_equiv a.fst).symm.surjective
    ⟨a, w.mem_orbit_set_of_mem_next_image_core_domain ha⟩,
  have := w.orbit_set_equiv_elim_of_mem_next_image_core_domain ha,
  rw [next_image_core],
  rw [← ha', equiv.apply_symm_apply] at this ⊢,
  obtain (⟨_ | n, a'⟩ | ⟨n, a'⟩) := a';
  simp only [elim_inr, elim_inl, nat.nat_zero_eq_zero, next_backward_image, next_forward_image,
    mk_mem_next_backward_image_domain, mk_mem_next_forward_image_domain,
    function.iterate_one] at this ⊢,
  { have ha'' := this.2.symm,
    rw local_perm.eq_symm_apply at ha'',
    { exact ha''.symm, },
    { exact hL, },
    { exact this.1, }, },
  exact (w.orbit_set_subset _ ((w.orbit_set_equiv _).symm _).prop).1,
  exact (w.orbit_set_subset _ ((w.orbit_set_equiv _).symm _).prop).1,
end

lemma next_image_core_not_mem_ran
  (a : atom) (ha : a ∈ w.next_image_core_domain) :
  w.next_image_core a a.fst (w.mem_orbit_set_of_mem_next_image_core_domain ha) ∉ w.atom_map.ran :=
begin
  rintro ⟨b, hb₁, hb₂⟩,
  rw next_image_core at hb₂,
  obtain ⟨a', ha'⟩ := (w.orbit_set_equiv a.fst).symm.surjective
    ⟨a, w.mem_orbit_set_of_mem_next_image_core_domain ha⟩,
  rw [← ha', equiv.apply_symm_apply] at hb₂,
  obtain (⟨_ | n, a'⟩ | ⟨n, a'⟩) := a';
  simp only [elim_inr, elim_inl, nat.nat_zero_eq_zero, next_backward_image, next_forward_image,
    mk_mem_next_backward_image_domain, mk_mem_next_forward_image_domain,
    function.iterate_one] at hb₂,
  { exact a'.prop.2 ⟨b, hb₁, hb₂⟩, },
  all_goals { have := w.orbit_set_subset _ ((w.orbit_set_equiv _).symm _).prop,
    rw ← hb₂ at this,
    exact this.2 (or.inr ⟨b, hb₁, rfl⟩), },
end

lemma next_image_core_atom_mem
  (hdiff : ∀ L hL, ((w.litter_map L).get hL : set atom) ∆ litter_set ((w.litter_map L).get hL).1 ⊆
    w.atom_map.ran)
  (a : atom) (ha : a ∈ w.next_image_core_domain)
  (L : litter) (hL : (w.litter_map L).dom) :
  a.fst = L ↔
    w.next_image_core a a.fst (w.mem_orbit_set_of_mem_next_image_core_domain ha) ∈
      (w.litter_map L).get hL :=
begin
  have hamem := w.mem_orbit_set_of_mem_next_image_core_domain ha,
  have ha' := w.next_image_core_atom_mem_litter_map a ha,
  rw mem_litter_set at ha',
  split,
  { rintro rfl,
    have := not_mem_subset (hdiff _ hL) (w.next_image_core_not_mem_ran a ha),
    simp only [mem_symm_diff, set_like.mem_coe, mem_litter_set,
      not_or_distrib, not_and_distrib, not_not] at this,
    refine this.2.resolve_left (not_not.mpr _),
    rw ha',
    rw w.litter_perm_apply_eq _ hL,
    rw w.rough_litter_map_or_else_of_dom,  },
  { intro h,
    have hL' := w.litter_perm_apply_eq L hL,
    rw w.rough_litter_map_or_else_of_dom hL at hL',
    have := not_mem_subset (hdiff _ hL) (w.next_image_core_not_mem_ran a ha),
    simp only [mem_symm_diff, set_like.mem_coe, mem_litter_set, not_not, h, true_and,
      not_true, and_false, or_false] at this,
    rw [ha', ← hL', ← local_perm.eq_symm_apply, local_perm.left_inv] at this,
    exact this,
    exact or.inl (or.inl (or.inl hL)),
    exact w.litter_map_dom_of_mem_next_image_core_domain ha,
    exact local_perm.map_domain _ (or.inl (or.inl (or.inl hL))), },
end

lemma orbit_set_equiv_atom_mem
  (hdiff : ∀ L hL, ((w.litter_map L).get hL : set atom) ∆ litter_set ((w.litter_map L).get hL).1 ⊆
    w.atom_map.ran)
  (a : atom) (ha : a ∈ w.need_forward_images ∧ a.fst ∈ w.litter_perm.domain)
  (L : litter) (hL : (w.litter_map L).dom) :
  a.fst = L ↔ ((w.orbit_set_equiv (w.litter_perm a.fst)).symm (inr (0, ⟨a, ha.1⟩)) : atom) ∈
    (w.litter_map L).get hL :=
begin
  have ha' : _ ∧ _ := w.orbit_set_subset _
    ((w.orbit_set_equiv (w.litter_perm a.fst)).symm (inr (0, ⟨a, ha.1⟩))).prop,
  rw mem_litter_set at ha',
  split,
  { rintro rfl,
    have := not_mem_subset (hdiff _ hL) _,
    simp only [mem_symm_diff, set_like.mem_coe, mem_litter_set,
      not_or_distrib, not_and_distrib, not_not] at this,
    refine this.2.resolve_left (not_not.mpr _),
    { rw ha'.1,
      rw w.litter_perm_apply_eq _ hL,
      rw w.rough_litter_map_or_else_of_dom, },
    { exact ha'.2 ∘ or.inr, }, },
  { intro h,
    have := @not_mem_subset _
      ((w.orbit_set_equiv (w.litter_perm a.fst)).symm (inr (0, ⟨a, ha.1⟩)) : atom) _ _
      (hdiff L hL) (ha'.2 ∘ or.inr),
    simp only [mem_symm_diff, h, set_like.mem_coe, mem_litter_set, true_and, not_true, and_false,
      or_false, not_not] at this,
    rw [ha'.1, ← rough_litter_map_or_else_of_dom, ← litter_perm_apply_eq,
      ← local_perm.eq_symm_apply, local_perm.left_inv] at this,
    exact this,
    { exact or.inl (or.inl (or.inl hL)), },
    { exact ha.2, },
    { exact w.litter_perm.map_domain (or.inl (or.inl (or.inl hL))), },
    { exact hL, }, },
end

lemma orbit_atom_mem
  (hdiff : ∀ L hL, ((w.litter_map L).get hL : set atom) ∆ litter_set ((w.litter_map L).get hL).1 ⊆
    w.atom_map.ran)
  (a : atom) (ha : (w.orbit_atom_map a).dom)
  (L : litter) (hL : (w.litter_map L).dom) :
  a.fst = L ↔ (w.orbit_atom_map a).get ha ∈ (w.litter_map L).get hL :=
begin
  obtain ha | ha | ha := ha,
  { rw orbit_atom_map_eq_of_mem_dom,
    exact w.atom_mem a ha L hL, },
  { rw orbit_atom_map_eq_of_need_forward_images,
    exact w.orbit_set_equiv_atom_mem hdiff a ha L hL, },
  { rw orbit_atom_map_eq_of_mem_next_image_core_domain,
    rw w.next_image_core_atom_mem hdiff a ha L hL, },
end

noncomputable def fill_atom_orbits
  (hdiff : ∀ L hL, ((w.litter_map L).get hL : set atom) ∆ litter_set ((w.litter_map L).get hL).1 ⊆
    w.atom_map.ran) : weak_near_litter_approx := {
  atom_map := w.orbit_atom_map,
  litter_map := w.litter_map,
  atom_map_dom_small := w.orbit_atom_map_dom_small,
  litter_map_dom_small := w.litter_map_dom_small,
  atom_map_injective := w.orbit_atom_map_injective,
  litter_map_injective := w.litter_map_injective,
  atom_mem := w.orbit_atom_mem hdiff,
}

variables {w} {hdiff : ∀ L hL,
  ((w.litter_map L).get hL : set atom) ∆ litter_set ((w.litter_map L).get hL).1 ⊆ w.atom_map.ran}

@[simp] lemma fill_atom_orbits_atom_map :
  (w.fill_atom_orbits hdiff).atom_map = w.orbit_atom_map := rfl

@[simp] lemma fill_atom_orbits_litter_map :
  (w.fill_atom_orbits hdiff).litter_map = w.litter_map := rfl

lemma subset_orbit_atom_map_dom : w.atom_map.dom ⊆ w.orbit_atom_map.dom :=
subset_union_left _ _

lemma subset_orbit_atom_map_ran : w.atom_map.ran ⊆ w.orbit_atom_map.ran :=
begin
  rintro _ ⟨a, ha, rfl⟩,
  exact ⟨a, subset_orbit_atom_map_dom ha, w.orbit_atom_map_eq_of_mem_dom _ _⟩,
end

lemma fst_mem_litter_perm_domain_of_mem_map ⦃L : litter⦄ (hL : (w.litter_map L).dom)
  ⦃a : atom⦄ (ha : a ∈ (w.litter_map L).get hL) :
  a.1 ∈ w.litter_perm.domain :=
begin
  by_cases a.1 = ((w.litter_map L).get hL).1,
  { rw h,
    refine or.inl (or.inl (or.inr ⟨L, hL, _⟩)),
    rw rough_litter_map_or_else_of_dom, },
  { by_cases h' : a.fst ∈ w.litter_perm'.domain,
    exact or.inl h',
    exact or.inr ⟨banned_litter.diff L hL a ⟨ha, h⟩, h'⟩, },
end

lemma fst_mem_litter_perm_domain_of_dom ⦃a : atom⦄ (ha : a ∈ w.atom_map.dom) :
  a.fst ∈ w.litter_perm.domain :=
begin
  by_cases h' : a.fst ∈ w.litter_perm'.domain,
  exact or.inl h',
  exact or.inr ⟨banned_litter.atom_dom a ha, h'⟩,
end

lemma fst_mem_litter_perm_domain_of_ran ⦃a : atom⦄ (ha : a ∈ w.atom_map.ran) :
  a.fst ∈ w.litter_perm.domain :=
begin
  by_cases h' : a.fst ∈ w.litter_perm'.domain,
  exact or.inl h',
  obtain ⟨b, hb, rfl⟩ := ha,
  exact or.inr ⟨banned_litter.atom_map b hb, h'⟩,
end

lemma fill_atom_orbits_precise
  (hdiff : ∀ L hL, ((w.litter_map L).get hL : set atom) ∆ litter_set ((w.litter_map L).get hL).1 ⊆
    w.atom_map.ran) : precise (w.fill_atom_orbits hdiff) :=
begin
  intros L hL,
  constructor,
  { exact subset_trans (hdiff L hL) subset_orbit_atom_map_ran, },
  { intros a ha ha',
    simp only [fill_atom_orbits_atom_map, fill_atom_orbits_litter_map, mem_litter_set,
      orbit_atom_map_dom_iff] at *,
    obtain ha | ha | ha := ha,
    { have := w.orbit_atom_map_eq_of_mem_dom a ha,
      generalize_proofs at this ha' ⊢,
      rw [this, or_iff_not_imp_left],
      intro hmap,
      have hfwd : (w.atom_map a).get ha ∈ w.need_forward_images := ⟨⟨a, _, rfl⟩, hmap⟩,
      refine or.inl ⟨hfwd, or.inl (or.inl _)⟩,
      refine mem_of_eq_of_mem _ (or.inl hL),
      rw [← ha', this], },
    { refine or.inr (or.inr ⟨_, ⟨L, rfl⟩, _⟩),
      simp only [pfun.mem_dom, Union_exists, mem_Union, mem_image, mem_set_of_eq, set_coe.exists,
        subtype.coe_mk, exists_and_distrib_right, exists_eq_right, exists_prop],
      have haL : L = w.litter_perm a.fst,
      { have := (congr_arg prod.fst
          (w.orbit_atom_map_eq_of_need_forward_images a ha)).symm.trans ha',
        rw ← this,
        exact (w.orbit_set_subset _ ((w.orbit_set_equiv _).symm _).prop).1, },
      refine ⟨or.inl (or.inl (or.inl hL)), _, _⟩,
      { refine mem_of_eq_of_mem (w.orbit_atom_map_eq_of_need_forward_images a ha) _,
        rw haL,
        exact ((w.orbit_set_equiv _).symm _).prop, },
      { have := w.orbit_atom_map_eq_of_need_forward_images a ha,
        obtain ⟨hm₁, hm₂⟩ := subtype.coe_eq_iff.mp this.symm,
        rw [equiv.symm_apply_eq, w.orbit_set_equiv_congr hm₁ haL.symm] at hm₂,
        refine mem_of_eq_of_mem hm₂.symm _,
        change sum.elim (λ b, b ∈ w.next_backward_image_domain L)
          (λ b, b ∈ w.next_forward_image_domain L) (inr (0, ⟨a, ha.1⟩)),
        refine ⟨ha.2, _⟩,
        simp only [subtype.coe_mk, function.iterate_one],
        exact haL.symm, }, },
    { have := w.orbit_atom_map_eq_of_mem_next_image_core_domain a ha,
      generalize_proofs at this ha' ⊢,
      rw [this, next_image_core],
      obtain ⟨_, ⟨L', rfl⟩, _, ⟨hL', rfl⟩, a, hbL, rfl⟩ := ha,
      set b := w.orbit_set_equiv L' a with hb,
      clear_value b,
      simp only [mem_set_of_eq] at hbL,
      rw ← hb at hbL,
      have haL' := (w.orbit_set_subset _ a.prop).1,
      rw mem_litter_set at haL',
      have := w.orbit_set_equiv_congr (w.mem_orbit_set_of_mem_next_image_core_domain _)
        (w.orbit_set_subset _ a.prop).1,
      rw subtype.coe_eta at this,
      rw [this, ← hb],
      obtain (⟨_ | n, b⟩ | ⟨n, b⟩) := b;
      simp only [need_backward_images, need_forward_images, elim_inl, elim_inr,
        next_backward_image, next_forward_image] at hbL ⊢,
      { exact or.inl b.prop.1, },
      { refine or.inr (or.inr _),
        have hbL' := hbL.2,
        symmetry' at hbL',
        rw [function.iterate_succ_apply',
          local_perm.eq_symm_apply _ hL' (w.litter_perm.symm.iterate_domain hbL.1)] at hbL',
        refine ⟨_, ⟨w.litter_perm.symm^[n + 1] (b : atom).1, rfl⟩, _, ⟨_, rfl⟩,
          ⟨(w.orbit_set_equiv (w.litter_perm (a : atom).1)).symm (inl (n, b)), _⟩, _⟩,
        { exact w.litter_perm.symm.iterate_domain hbL.1, },
        { rw ← hbL',
          have := (((w.orbit_set_equiv (w.litter_perm (a : atom).1)).symm (inl (n, b)))).prop,
          rw haL' at this ⊢,
          exact this, },
        { simp only [function.comp_app, mem_set_of_eq, subtype.coe_mk,
            eq_self_iff_true, and_true],
          rw [w.orbit_set_equiv_congr _ hbL'.symm,
            w.orbit_set_equiv_congr _ (congr_arg w.litter_perm haL'.symm)],
          simp only [subtype.coe_eta, equiv.apply_symm_apply, elim_inl],
          exact ⟨hbL.1, rfl⟩, }, },
      { refine or.inr (or.inr _),
        refine ⟨_, ⟨w.litter_perm^[n + 2] (b : atom).1, rfl⟩, _, ⟨_, rfl⟩,
          ⟨(w.orbit_set_equiv (w.litter_perm (a : atom).1)).symm (inr (n + 1, b)), _⟩, _⟩,
        { exact w.litter_perm.iterate_domain hbL.1, },
        { rw [function.iterate_succ_apply', hbL.2, haL'],
          exact ((w.orbit_set_equiv _).symm _).prop, },
        { simp only [function.comp_app, mem_set_of_eq,
            subtype.coe_mk, eq_self_iff_true, and_true],
          have := congr_arg w.litter_perm hbL.2,
          rw ← function.iterate_succ_apply' w.litter_perm (n + 1) at this,
          rw [w.orbit_set_equiv_congr _ this,
            w.orbit_set_equiv_congr _ (congr_arg w.litter_perm haL'.symm)],
          simp only [function.iterate_succ, function.comp_app, subtype.coe_eta,
            equiv.apply_symm_apply, elim_inr],
          exact ⟨hbL.1, rfl⟩, }, },
      { refine ⟨_, ⟨L', rfl⟩, _, ⟨hL', rfl⟩, a, _, rfl⟩,
        rw [mem_set_of_eq, ← hb],
        exact hbL, }, }, },
  { rw fill_atom_orbits_litter_map at hL,
    rintros a ⟨ha₁ | ⟨ha₁, ha₁'⟩ | ha₁, ha₂⟩;
    simp only [fill_atom_orbits_atom_map, fill_atom_orbits_litter_map, orbit_atom_map_dom,
      mem_inter_iff, mem_union, set_like.mem_coe] at *,
    { by_cases ha₃ : a ∈ w.atom_map.ran,
      { obtain ⟨b, hb₁, hb₂⟩ := ha₃,
        refine ⟨b, or.inl hb₁, _⟩,
        rw orbit_atom_map_eq_of_mem_dom,
        exact hb₂, },
      { refine ⟨(w.orbit_set_equiv (w.litter_perm.symm a.1)).symm (inl (0, ⟨a, ha₁, ha₃⟩)), _, _⟩,
        { refine or.inr (or.inr ⟨_, ⟨w.litter_perm.symm a.1, rfl⟩, _, ⟨_, rfl⟩, _⟩),
          { exact w.litter_perm.symm.map_domain (fst_mem_litter_perm_domain_of_mem_map hL ha₂), },
          refine ⟨_, _, rfl⟩,
          simp only [mem_set_of_eq, equiv.apply_symm_apply, elim_inl],
          exact ⟨fst_mem_litter_perm_domain_of_mem_map hL ha₂, rfl⟩, },
        { rw [orbit_atom_map_eq_of_mem_next_image_core_domain, next_image_core],
          have : (((w.orbit_set_equiv (w.litter_perm.symm a.fst)).symm)
            (inl (0, ⟨a, _⟩)) : atom).fst = w.litter_perm.symm a.fst,
          { exact (w.orbit_set_subset _ ((w.orbit_set_equiv _).symm _).prop).1,
            exact ⟨ha₁, ha₃⟩, },
          rw w.orbit_set_equiv_congr _ this,
          simp only [equiv.apply_symm_apply, elim_inl, subtype.coe_eta, next_backward_image,
            subtype.coe_mk], }, }, },
    { obtain ⟨⟨b, hb₁, hb₂⟩, ha₁⟩ := ha₁,
      rw ← hb₂,
      refine ⟨b, or.inl hb₁, _⟩,
      rw orbit_atom_map_eq_of_mem_dom, },
    { obtain ⟨a', ha'⟩ := (w.orbit_set_equiv a.fst).symm.surjective
        ⟨a, w.mem_orbit_set_of_mem_next_image_core_domain ha₁⟩,
      obtain (⟨n, a'⟩ | ⟨_ | n, a'⟩) := a',
      { have : ((w.orbit_set_equiv (w.litter_perm.symm^[n + 2] (a' : atom).fst)).symm
          (inl (n + 1, a')) : atom) ∈ w.next_image_core_domain,
        { refine ⟨_, ⟨w.litter_perm.symm^[n + 2] (a' : atom).fst, rfl⟩, _, ⟨_, rfl⟩, _⟩,
          exact w.litter_perm.symm.iterate_domain (fst_mem_litter_perm_domain_of_dom a'.prop.1),
          refine ⟨_, _, rfl⟩,
          simp only [mem_set_of_eq, equiv.apply_symm_apply, elim_inl],
          exact ⟨fst_mem_litter_perm_domain_of_dom a'.prop.1, rfl⟩, },
        refine ⟨_, or.inr (or.inr this), _⟩,
        rw orbit_atom_map_eq_of_mem_next_image_core_domain,
        rw next_image_core,
        have : (((w.orbit_set_equiv (w.litter_perm.symm^[n + 2] (a' : atom).fst)).symm)
            (inl (n + 1, a')) : atom).fst = (w.litter_perm.symm^[n + 2] (a' : atom).fst) :=
          (w.orbit_set_subset _ ((w.orbit_set_equiv _).symm _).prop).1,
        rw w.orbit_set_equiv_congr _ this,
        simp only [subtype.coe_eta, equiv.apply_symm_apply, elim_inl, next_backward_image],
        have := congr_arg subtype.val ha',
        simp only [subtype.val_eq_coe] at this,
        rw ← this,
        refine w.orbit_set_equiv_symm_congr _,
        have := (w.orbit_set_subset _ ((w.orbit_set_equiv _).symm _).prop).1,
        rw mem_litter_set at this,
        rw this,
        have := w.orbit_set_equiv_elim_of_mem_next_image_core_domain ha₁,
        rw ← ha' at this,
        simp only [equiv.apply_symm_apply, elim_inl, next_backward_image_domain,
          function.comp_app, mem_set_of_eq] at this,
        rw [← this.2, function.iterate_succ_apply', local_perm.right_inv],
        exact w.litter_perm.symm.iterate_domain this.1, },
      { have := w.orbit_set_equiv_elim_of_mem_next_image_core_domain ha₁,
        rw ← ha' at this,
        simp only [equiv.apply_symm_apply, elim_inr, next_forward_image_domain,
          function.comp_app, mem_set_of_eq, function.iterate_one] at this,
        refine ⟨a', or.inr (or.inl ⟨a'.prop, this.1⟩), _⟩,
        rw [orbit_atom_map_eq_of_need_forward_images, w.orbit_set_equiv_symm_congr this.2,
          subtype.coe_eta, ha'],
        refl, },
      { have : ((w.orbit_set_equiv (w.litter_perm^[n + 1] (a' : atom).fst)).symm
          (inr (n, a')) : atom) ∈ w.next_image_core_domain,
        { refine ⟨_, ⟨w.litter_perm^[n + 1] (a' : atom).fst, rfl⟩, _, ⟨_, rfl⟩, _⟩,
          exact w.litter_perm.iterate_domain (fst_mem_litter_perm_domain_of_ran a'.prop.1),
          refine ⟨_, _, rfl⟩,
          simp only [mem_set_of_eq, equiv.apply_symm_apply, elim_inl],
          exact ⟨fst_mem_litter_perm_domain_of_ran a'.prop.1, rfl⟩, },
        refine ⟨_, or.inr (or.inr this), _⟩,
        rw orbit_atom_map_eq_of_mem_next_image_core_domain,
        rw next_image_core,
        have : (((w.orbit_set_equiv (w.litter_perm^[n + 1] (a' : atom).fst)).symm)
            (inr (n, a')) : atom).fst = (w.litter_perm^[n + 1] (a' : atom).fst) :=
          (w.orbit_set_subset _ ((w.orbit_set_equiv _).symm _).prop).1,
        rw w.orbit_set_equiv_congr _ this,
        simp only [subtype.coe_eta, equiv.apply_symm_apply, elim_inl, next_backward_image],
        have := congr_arg subtype.val ha',
        simp only [subtype.val_eq_coe] at this,
        rw ← this,
        refine w.orbit_set_equiv_symm_congr _,
        have := (w.orbit_set_subset _ ((w.orbit_set_equiv _).symm _).prop).1,
        rw mem_litter_set at this,
        rw this,
        have := w.orbit_set_equiv_elim_of_mem_next_image_core_domain ha₁,
        rw ← ha' at this,
        simp only [equiv.apply_symm_apply, elim_inr, next_forward_image_domain,
          function.comp_app, mem_set_of_eq] at this,
        rw [← this.2, function.iterate_succ_apply', function.iterate_succ_apply',
          function.iterate_succ_apply'], }, }, },
end

end weak_near_litter_approx

end con_nf
