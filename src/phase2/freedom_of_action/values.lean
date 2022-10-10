import phase2.freedom_of_action.allowable
import tactic.by_contra

/-!
# Value API for allowable partial permutations

Allowable partial permutations satisfy a "one-to-one" condition that means that if `(x, A)` lies in
the domain of `σ` (for example), then there is a unique value `y` that `x` is mapped to under any
allowable permutation satisfying the specification. This API allows us to retrieve these values.
Since this data is behind existentials, many of the definitions are noncomputable.
-/

section
variables {α : Type*} [generalized_boolean_algebra α]

@[simp] lemma inf_symm_diff_left (a b : α) : a ⊓ a ∆ b = a \ b :=
by rw [(∆), inf_sup_left, inf_of_le_right sdiff_le, inf_sdiff_self_right, sup_bot_eq]

@[simp] lemma inf_symm_diff_right (a b : α) : a ⊓ b ∆ a = a \ b :=
by rw [symm_diff_comm, inf_symm_diff_left]

@[simp] lemma symm_diff_inf_left (a b : α) : a ∆ b ⊓ a = a \ b :=
by rw [inf_comm, inf_symm_diff_left]

@[simp] lemma symm_diff_inf_right (a b : α) : b ∆ a ⊓ a = a \ b :=
by rw [inf_comm, inf_symm_diff_right]

end

namespace set
variables {α : Type*} {s t : set α}

lemma symm_diff_of_subset : s ⊆ t → s ∆ t = t \ s := @symm_diff_of_le (set α) _ _ _
lemma symm_diff_of_superset : t ⊆ s → s ∆ t = s \ t := @symm_diff_of_ge (set α) _ _ _

@[simp] lemma inter_symm_diff_left (s t : set α) : s ∩ s ∆ t = s \ t := inf_symm_diff_left _ _
@[simp] lemma inter_symm_diff_right (s t : set α) : s ∩ t ∆ s = s \ t := inf_symm_diff_right _ _
@[simp] lemma symm_diff_inter_left (s t : set α) : s ∆ t ∩ s = s \ t := symm_diff_inf_left _ _
@[simp] lemma symm_diff_inter_right (s t : set α) : t ∆ s ∩ s = s \ t := symm_diff_inf_right _ _

end set

open cardinal set sum

universe u

namespace con_nf
namespace allowable_spec
variables [params.{u}] {α : Λ} [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [typed_positions.{}] [phase_2_assumptions α] {B : le_index α} {L₁ L₂ : litter}
  {M₁ M₂ N₁ N₂ : near_litter} {a b : atom}

open spec

/-- Gets the value that a given input atom `b` is mapped to
under any allowable `π` extending `σ`. -/
noncomputable def atom_value (σ : allowable_spec B) (A : extended_index B)
  (b : atom) (hb : (inl b, A) ∈ (σ : spec B).domain) : atom :=
@sum.rec _ _ (λ (c : atom × atom ⊕ near_litter × near_litter),
  c.elim (λ atoms, inl atoms.fst) (λ Ns, inr Ns.fst) = inl b → atom)
  (λ lhs _, lhs.snd) (λ lhs h, by cases h)
  (mem_domain.mp hb).some.1
  (congr_arg prod.fst (mem_domain.mp hb).some_spec.2)

lemma atom_value_spec (σ : allowable_spec B) (A : extended_index B) (b : atom)
  (hb : (inl b, A) ∈ (σ : spec B).domain) :
  (inl (b, atom_value σ A b hb), A) ∈ (σ : spec B) :=
begin
  unfold atom_value,
  rw mem_domain at hb,
  generalize hc : hb.some = c,
  obtain ⟨hc₁, hc₂⟩ := hb.some_spec,
  simp_rw hc at hc₁ hc₂ ⊢,
  obtain ⟨⟨b₁, b₂⟩ | Ns, C⟩ := c,
  { obtain ⟨⟨⟨d₁, d₂⟩ | _, D⟩, hd₁, hd₂⟩ := hb; cases hd₂,
    rw ← hc₂ at hd₂, cases hd₂,
    convert hd₁,
    exact (σ.prop.backward.one_to_one A).atom b hc₁ hd₁ },
  { cases hc₂ }
end

lemma atom_value_spec_range (σ : allowable_spec B) (A : extended_index B) (b : atom)
  (hb : (inl b, A) ∈ (σ : spec B).domain) :
  (inl (atom_value σ A b hb), A) ∈ (σ : spec B).range :=
spec.mem_range.2 ⟨(inl (b, atom_value σ A b hb), A), atom_value_spec σ A b hb, rfl⟩

@[simp] lemma atom_value_eq_of_mem {σ : allowable_spec B} {A : extended_index B}
  (hab : (inl (a, b), A) ∈ (σ : spec B)) :
  atom_value σ A a (mem_domain.2 ⟨_, hab, rfl⟩) = b :=
(σ.prop.backward.one_to_one A).atom a (atom_value_spec σ A a $ mem_domain.2 ⟨_, hab, rfl⟩) hab

@[simp] lemma atom_value_eq_of_mem_inv {σ : allowable_spec B} {A : extended_index B}
  (hab : (inl (a, b), A) ∈ (σ : spec B)) :
  atom_value σ⁻¹ A b (inl_mem_range hab) = a :=
(σ.prop.forward.one_to_one A).atom b (atom_value_spec σ⁻¹ A b $ (inl_mem_range hab)) hab

lemma atom_value_injective {σ : allowable_spec B} {A : extended_index B}
  {ha : (inl a, A) ∈ (σ : spec B).domain} {hb : (inl b, A) ∈ (σ : spec B).domain} :
  σ.atom_value A a ha = σ.atom_value A b hb → a = b :=
begin
  have h₁ := atom_value_spec σ A a ha,
  have h₂ := atom_value_spec σ A b hb,
  intro hb,
  rw ← hb at h₂,
  exact (σ.prop.forward.one_to_one A).atom (atom_value σ A a ha) h₁ h₂,
end

noncomputable def atom_value_inj (σ : allowable_spec B) (A : extended_index B) :
  {b | (inl b, A) ∈ (σ : spec B).domain} ↪ atom :=
⟨λ b, atom_value σ A b b.prop, λ b₁ b₂ hb, subtype.coe_injective $ atom_value_injective hb⟩

lemma atom_value_mem_inv (σ : allowable_spec B) (A : extended_index B) (b : atom)
  (hb : (inl b, A) ∈ (σ : spec B).domain) :
  (inl (atom_value σ A b hb, b), A) ∈ (σ⁻¹ : spec B) :=
atom_value_spec σ A b hb

lemma atom_value_mem_range (σ : allowable_spec B) (A : extended_index B) (b : atom)
  (hb : (inl b, A) ∈ (σ : spec B).domain) :
  (inl (atom_value σ A b hb), A) ∈ (σ : spec B).range :=
by { rw spec.mem_range, exact ⟨_, atom_value_spec σ A b hb, rfl⟩ }

/-- Composing the `atom_value` operation with the inverse permutation does nothing. -/
lemma atom_value_inv (σ : allowable_spec B) (A : extended_index B) (b : atom)
  (hb : (inl b, A) ∈ (σ : spec B).domain) :
  atom_value σ⁻¹ A (atom_value σ A b hb) (atom_value_mem_range σ A b hb) = b :=
begin
  have := atom_value_spec σ⁻¹ A (atom_value σ A b hb) (atom_value_mem_range σ A b hb),
  simp_rw [allowable_spec.coe_inv, spec.mem_inv] at this,
  exact (σ.prop.forward.one_to_one A).atom _ this (atom_value_spec σ A b hb),
end

/-- Gets the value that a given input near litter `N` is mapped to
under any allowable `π` extending `σ`. -/
noncomputable def near_litter_value (σ : allowable_spec B) (A : extended_index B)
  (N : near_litter) (hb : (inr N, A) ∈ (σ : spec B).domain) : near_litter :=
@sum.rec _ _ (λ (c : atom × atom ⊕ near_litter × near_litter),
  c.elim (λ atoms, inl atoms.fst) (λ Ns, inr Ns.fst) = inr N → near_litter)
  (λ lhs h, by cases h) (λ lhs _, lhs.snd)
  (mem_domain.mp hb).some.1
  (congr_arg prod.fst (mem_domain.mp hb).some_spec.2)

lemma near_litter_value_spec (σ : allowable_spec B) (A : extended_index B) (N : near_litter)
  (hN : (inr N, A) ∈ (σ : spec B).domain) :
  (inr (N, near_litter_value σ A N hN), A) ∈ (σ : spec B) :=
begin
  unfold near_litter_value,
  rw mem_domain at hN,
  generalize hc : hN.some = c,
  obtain ⟨hc₁, hc₂⟩ := hN.some_spec,
  simp_rw hc at hc₁ hc₂ ⊢,
  obtain ⟨_ | ⟨N₁, N₂⟩, C⟩ := c,
  { cases hc₂ },
  obtain ⟨⟨_ | ⟨N₃, N₄⟩, D⟩, hd₁, hd₂⟩ := hN; cases hd₂,
  rw ← hc₂ at hd₂,
  cases hd₂,
  convert hd₁,
  exact (σ.prop.backward.one_to_one A).near_litter N hc₁ hd₁,
end

lemma near_litter_value_spec_range (σ : allowable_spec B) (A : extended_index B) (N : near_litter)
  (hN : (inr N, A) ∈ (σ : spec B).domain) :
  (inr (near_litter_value σ A N hN), A) ∈ (σ : spec B).range :=
spec.mem_range.2 ⟨(inr (N, near_litter_value σ A N hN), A), near_litter_value_spec σ A N hN, rfl⟩

lemma near_litter_value_injective (σ : allowable_spec B) (A : extended_index B) :
  ∀ hN₁ hN₂, near_litter_value σ A N₁ hN₁ = near_litter_value σ A N₂ hN₂ → N₁ = N₂ :=
begin
  intros hN₁ hN₂ hN,
  have h₁ := near_litter_value_spec σ A N₁ hN₁,
  have h₂ := near_litter_value_spec σ A N₂ hN₂,
  rw ← hN at h₂,
  exact (σ.prop.forward.one_to_one A).near_litter _ h₁ h₂,
end

noncomputable def near_litter_value_inj (σ : allowable_spec B) (A : extended_index B) :
  {N | (inr N, A) ∈ (σ : spec B).domain} ↪ near_litter :=
⟨λ N, near_litter_value σ A N.val N.prop, begin
  intros N₁ N₂ hN,
  exact subtype.coe_inj.mp (near_litter_value_injective _ _ _ _ hN),
end⟩

/-- If the images of two litters under `σ` intersect, the litters must intersect, and therefore are
equal. This is a rather technical result depending on various allowability conditions. -/
lemma litter_eq_of_image_inter (σ : allowable_spec B) (A : extended_index B)
  (hL₁ : (inr (L₁.to_near_litter, N₁), A) ∈ (σ : spec B))
  (hL₂ : (inr (L₂.to_near_litter, N₂), A) ∈ (σ : spec B))
  (a : atom) (haN₁ : a ∈ N₁) (haN₂ : a ∈ N₂) : L₁ = L₂ :=
begin
  obtain ⟨N, h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N, hN, h₁, h₂⟩ :=
    σ.prop.forward.atom_cond L₁ A,
  { cases (σ.prop.backward.one_to_one A).near_litter _ hL₁ h₁,
    rw [←set_like.mem_coe, h₃] at haN₁,
    obtain ⟨a₁, ha₁⟩ := haN₁,
    have map₁ := h₂ a₁ a₁.prop,
    rw subtype.coe_eta at map₁,
    rw ha₁ at map₁,

    obtain ⟨N', h₁', atom_map', h₂', h₃'⟩ | ⟨h₁', h₂'⟩ | ⟨N', hN', h₁', h₂'⟩ :=
      σ.prop.forward.atom_cond L₂ A,
    { cases (σ.prop.backward.one_to_one A).near_litter _ hL₂ h₁',
      rw [←set_like.mem_coe, h₃'] at haN₂,
      obtain ⟨a₂, ha₂⟩ := haN₂,
      have map₂ := h₂' a₂ a₂.prop,
      rw subtype.coe_eta at map₂,
      rw ha₂ at map₂,
      obtain ⟨⟨a₁L, a₁⟩, ha₁'⟩ := a₁,
      obtain ⟨⟨a₂L, a₂⟩, ha₂'⟩ := a₂,
      cases (σ.prop.forward.one_to_one A).atom a map₁ map₂, cases ha₁', cases ha₂', refl },
    { rw mem_domain at h₁', cases h₁' ⟨_, hL₂, rfl⟩ },
    { cases (σ.prop.backward.one_to_one A).near_litter _ hL₂ hN',
      have := h₂' (h₂ a₁ a₁.prop),
      rw subtype.coe_eta at this,
      rw ha₁ at this,
      obtain ⟨⟨a₁L, a₁⟩, ha₁'⟩ := a₁,
      cases this.mpr haN₂, cases ha₁', refl } },
  { rw mem_domain at h₁, cases h₁ ⟨_, hL₁, rfl⟩ },
  cases (σ.prop.backward.one_to_one A).near_litter _ hL₁ hN,
  obtain ⟨N', h₁', atom_map', h₂', h₃'⟩ | ⟨h₁', h₂'⟩ | ⟨N', hN', h₁', h₂'⟩ :=
    σ.prop.forward.atom_cond L₂ A,
  { cases (σ.prop.backward.one_to_one A).near_litter _ hL₂ h₁',
    rw [←set_like.mem_coe, h₃'] at haN₂,
    obtain ⟨a₂, ha₂⟩ := haN₂,
    have map₂ := h₂' a₂ a₂.prop,
    rw subtype.coe_eta at map₂,
    rw ha₂ at map₂,
    have := h₂ (h₂' a₂ a₂.prop),
    rw subtype.coe_eta at this,
    rw ha₂ at this,
    obtain ⟨⟨a₂L, a₂⟩, ha₂'⟩ := a₂,
    cases this.mpr haN₁, cases ha₂', refl },
  { rw mem_domain at h₁', cases h₁' ⟨_, hL₂, rfl⟩ },
  cases (σ.prop.backward.one_to_one A).near_litter _ hL₂ hN',
  obtain ⟨M₁, hM₁, s₁, hs₁, gs₁⟩ := σ.prop.backward.near_litter_cond _ _ A hL₁,
  obtain ⟨M₂, hM₂, s₂, hs₂, gs₂⟩ := σ.prop.backward.near_litter_cond _ _ A hL₂,
  dsimp only at gs₁ gs₂,
  cases eq_empty_or_nonempty (↑N₁ \ litter_set N₁.fst ∩ N₂) with hN₁ hN₁,
  { cases eq_empty_or_nonempty (↑N₂ \ litter_set N₂.fst ∩ N₁) with hN₂ hN₂,
    { rw eq_empty_iff_forall_not_mem at hN₁ hN₂, specialize hN₁ a, specialize hN₂ a,
      rw [mem_inter_iff, and_comm, mem_diff] at hN₁ hN₂,
      push_neg at hN₁ hN₂, specialize hN₁ haN₂ haN₁, specialize hN₂ haN₁ haN₂,
      have := eq_of_mem_litter_set_of_mem_litter_set hN₁ hN₂,
      rw this at hM₁,
      have M₁_eq_M₂ := (σ.prop.forward.one_to_one A).near_litter _ hM₁ hM₂,
      dsimp only at M₁_eq_M₂, subst M₁_eq_M₂,
      refine is_near_litter_litter_set_iff.1 _,
      unfold is_near_litter is_near,
      simp only [near_litter.coe_mk, subtype.coe_mk] at gs₁ gs₂,
      rw [gs₁, gs₂, symm_diff_left_comm, ← symm_diff_assoc, symm_diff_symm_diff_cancel_left],
      exact small.symm_diff (mk_range_le.trans_lt N₁.2.2) (mk_range_le.trans_lt N₂.2.2) },
    { obtain ⟨aN₂, haN₂, haN₂'⟩ := hN₂,
      have := hs₂ ⟨aN₂, or.inr haN₂⟩,
      exact eq_of_mem_litter_set_of_mem_litter_set
        ((h₂ this).symm.mp haN₂') ((h₂' this).symm.mp haN₂.left) } },
  { obtain ⟨aN₁, haN₁, haN₁'⟩ := hN₁,
    have := hs₁ ⟨aN₁, or.inr haN₁⟩,
    exact eq_of_mem_litter_set_of_mem_litter_set
      ((h₂ this).symm.mp haN₁.left) ((h₂' this).symm.mp haN₁') }
end

lemma litter_image_disjoint (σ : allowable_spec B) (A : extended_index B)
  (hN₁ : (inr (L₁.to_near_litter, N₁), A) ∈ (σ : spec B))
  (hN₂ : (inr (L₂.to_near_litter, N₂), A) ∈ (σ : spec B)) :
  L₁ ≠ L₂ → disjoint (N₁ : set atom) N₂ :=
begin
  contrapose!,
  rw not_disjoint_iff,
  rintro ⟨a, ha₁, ha₂⟩,
  exact litter_eq_of_image_inter σ A hN₁ hN₂ a ha₁ ha₂,
end

lemma not_small_litter_set (i : litter) : ¬ small (litter_set i) := by simp [small]

lemma litter_ne_of_disjoint (h : disjoint (N₁ : set atom) N₂) : N₁.1 ≠ N₂.1 :=
begin
  obtain ⟨i, s⟩ := N₁,
  obtain ⟨_, t⟩ := N₂,
  dsimp at ⊢ h,
  rintro rfl,
  exact not_small_litter_set _
    ((s.prop.union t.prop).mono $ subset_symm_diff_union_symm_diff_right h),
end

/-- An application of the near litter condition using `litter_image_disjoint`. -/
lemma near_litter_image_disjoint (σ : allowable_spec B) (A : extended_index B)
  {N M N' M' : near_litter}
  (hN : (inr (N, N'), A) ∈ (σ : spec B)) (hM : (inr (M, M'), A) ∈ (σ : spec B)) :
  disjoint (N : set atom) M → disjoint (N' : set atom) M' :=
begin
  intro hdisj,
  have h : ∀ (L : litter) (L' : near_litter) (h : (inr (L.to_near_litter, L'), A) ∈ (σ : spec B))
    (a b : atom) (hab : (inl (a, b), A) ∈ (σ : spec B)), a ∈ litter_set L ↔ b ∈ L',
  { intros,
    obtain ⟨L'', hL, atom_map, hall, hall2⟩ | ⟨ha, hL, hsmall_out⟩ | ⟨L'', hL, hsmall_in, hsmall_in2⟩
      := σ.prop.forward.atom_cond L A,
    { have := (σ.prop.backward.one_to_one A).near_litter _ h hL,
      subst this,
      rw [←set_like.mem_coe, hall2],
      unfold range,
      simp only [set_coe.exists, mem_set_of_eq],
      refine ⟨λ ha, _, _⟩,
      { have := hall a ha,
        have := (σ.prop.backward.one_to_one A).atom _ hab this,
        subst this,
        exact ⟨_, ha, rfl⟩ },
      rintro ⟨x, hx, hx2⟩,
      have := hall x hx,
      rw hx2 at this,
      have := (σ.prop.forward.one_to_one A).atom _ hab this,
      subst this,
      exact hx },
    { simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and] at ha,
      have := ha _ h,
      simp only [binary_condition.domain_mk, map_inr, eq_self_iff_true, not_true] at this,
      cases this },
    { have := (σ.prop.backward.one_to_one A).near_litter _ h hL,
      subst this,
      exact hsmall_in2 hab } },
  have h2 : ∀ {N M N' M' Nf Mf : near_litter} (hN : (inr (N, N'), A) ∈ (σ : spec B))
    (hN2 : (inr (N.fst.to_near_litter, Nf), A) ∈ (σ : spec B))
    (hM : (inr (M, M'), A) ∈ (σ : spec B))
    (hM2 : (inr (M.fst.to_near_litter, Mf), A) ∈ (σ : spec B))
    (hdisj : disjoint (N.2 : set atom) M) (a b : atom) (hab : (inl (a, b), A) ∈ (σ : spec B))
    (hb1 : b ∈ (N' : set atom) \ Nf) (hb2 : b ∈ (Mf : set atom) ∩ M'), false,
  { clear hdisj hN hM N M N' M',
    intros,
    obtain ⟨Nf', hNf', symm_diff_N, hsdN1, hsdN2⟩ := σ.prop.forward.near_litter_cond _ _ _ hN,
    have := (σ.prop.backward.one_to_one A).near_litter _ hN2 hNf',
    subst this,
    obtain ⟨Mf', hMf', symm_diff_M, hsdM1, hsdM2⟩ := σ.prop.forward.near_litter_cond _ _ _ hM,
    have := (σ.prop.backward.one_to_one A).near_litter _ hM2 hMf',
    subst this,
    have ha3 := hb1,
    rw [hsdN2, symm_diff_def, sup_eq_union, set.union_diff_distrib] at ha3,
    simp only [subtype.val_eq_coe, sdiff_sdiff_self, bot_eq_empty, sdiff_idem, empty_union,
      mem_diff, set.mem_range, set_coe.exists] at ha3,
    obtain ⟨⟨c, hc1, hc2⟩, _⟩ := ha3,
    have := hsdN1 ⟨c, hc1⟩,
    rw hc2 at this,
    rw ← subtype.val_eq_coe at this,
    simp only at this,
    obtain rfl := (σ.prop.forward.one_to_one A).atom _ hab this,
    cases hc1,
    exact hb1.2 ((h N.fst Nf hN2 a b hab).mp hc1.1),
    have := (h M.fst Mf hM2 a b hab).mpr (hb2.1),
    have : a ∈ litter_set M.fst ∆ M,
    { by_cases ha : a ∈ M,
      cases hdisj ⟨mem_of_mem_diff hc1, ha⟩,
      exact or.inl ⟨this, ha⟩ },
    have := hsdM1 ⟨a, this⟩,
    rw ← subtype.val_eq_coe at this,
    simp only at this,
    obtain rfl := (σ.prop.backward.one_to_one A).atom _ hab this,
    rw [hsdM2, inter_symm_diff_left] at hb2,
    exact hb2.2 (mem_range_self _) },
  rintro b ⟨hb1, hb2⟩,
  obtain ⟨Nf, hNf, symm_diff_N, hsdN1, hsdN2⟩ := σ.prop.forward.near_litter_cond _ _ _ hN,
  obtain ⟨Mf, hMf, symm_diff_M, hsdM1, hsdM2⟩ := σ.prop.forward.near_litter_cond _ _ _ hM,
  by_cases hb3 : b ∈ Nf; by_cases hb4 : b ∈ Mf,
  { refine (litter_image_disjoint σ A hNf hMf _) ⟨hb3, hb4⟩,
    exact litter_ne_of_disjoint hdisj },
  { have := hb2, rw hsdM2 at this,
    cases this,
    exact hb4 this.1,
    have := this.1,
    simp only [set.mem_range, set_coe.exists] at this,
    obtain ⟨a, ha1, ha2⟩ := this,
    have hab := hsdM1 ⟨a, ha1⟩, rw ha2 at hab,
    exact h2 hM hMf hN hNf (disjoint.symm hdisj) a b hab ⟨hb2, hb4⟩ ⟨hb3, hb1⟩ },
  { have := hb1, rw hsdN2 at this,
    cases this, exact hb3 this.1,
    have := this.1,
    simp only [set.mem_range, set_coe.exists] at this,
    obtain ⟨a, ha1, ha2⟩  := this,
    have hab := hsdN1 ⟨a, ha1⟩,
    rw ha2 at hab,
    exact h2 hN hNf hM hMf hdisj a b hab ⟨hb1, hb3⟩ ⟨hb4, hb2⟩ },
  have := hb2,
  rw hsdM2 at this,
  cases this,
  exact hb4 this.1,
  have := this.1,
  simp only [set.mem_range, set_coe.exists] at this,
  obtain ⟨a, ha1, rfl⟩ := this,
  clear this,
  rw hsdN2 at hb1,
  cases hb1,
  exact hb3 hb1.1,
  have := hb1.1,
  simp only [set.mem_range, set_coe.exists] at this,
  obtain ⟨a', ha'1, ha'2⟩ := this,
  have hab := hsdM1 ⟨a, ha1⟩,
  have ha'b := hsdN1 ⟨a', ha'1⟩,
  rw ha2 at hab,
  rw ha'2 at ha'b,
  rw ← subtype.val_eq_coe at hab ha'b,
  simp only at hab ha'b,
  have := (σ.prop.forward.one_to_one A).atom _ hab ha'b,
  subst this,
  cases ha1,
  exact hb4 ((h M.fst Mf hMf a b hab).mp ha1.1),
  cases ha'1,
  exact hb3 ((h N.fst Nf hNf a b hab).mp ha'1.1),
  exact hdisj ⟨ha'1.1, ha1.1⟩,
end

lemma value_mem_value_iff_mem {σ : allowable_spec B} {A : extended_index B} {a : atom}
  (ha : (inl a, A) ∈ (σ : spec B).domain) {N : near_litter}
  (hN : (inr N, A) ∈ (σ : spec B).domain) :
  σ.atom_value A a ha ∈ σ.near_litter_value A N hN ↔ a ∈ N :=
begin
  revert σ a N,
  suffices : ∀ {σ : allowable_spec B} {a : atom} {N : near_litter}
    (ha : (inl a, A) ∈ (σ : spec B).domain) (hN : (inr N, A) ∈ (σ : spec B).domain)
    (h : σ.atom_value A a ha ∈ (σ.near_litter_value A N hN)), a ∈ (N.2 : set atom),
  { intros,
    refine ⟨this _ _, λ h, _⟩,
    specialize @this σ⁻¹ (σ.atom_value A a ha) (σ.near_litter_value A N hN) _ _ _,
    apply atom_value_spec_range, apply near_litter_value_spec_range,
    rw atom_value_eq_of_mem_inv,
    have : σ⁻¹.near_litter_value A (σ.near_litter_value A N hN) _ = N,
    { apply (σ.prop.forward.one_to_one A).near_litter,
      simp only [ mem_set_of_eq],
      apply near_litter_value_spec σ⁻¹ A (σ.near_litter_value A N hN),
      simp only [mem_set_of_eq],
      exact near_litter_value_spec _ _ _ _ },
    rw this,
    exact h,
    apply atom_value_spec,
    exact this },
  intros,
  simp only [subtype.val_eq_coe, mem_domain] at hN,
  obtain ⟨⟨⟨_, _⟩ | ⟨N', N₂⟩, A'⟩, hcond, hcond2⟩ :=hN, {simp only [binary_condition.domain_mk,
  map_inl, prod.mk.inj_iff, false_and] at hcond2, exfalso, exact hcond2,},
  simp only [binary_condition.domain_mk, map_inr, prod.mk.inj_iff] at hcond2,
  obtain ⟨rfl, rfl⟩ := hcond2,
  obtain ⟨M, ⟨hM, ⟨sd,hsd1,hsd2⟩ ⟩ ⟩ :=  σ.prop.forward.near_litter_cond N' N₂ A' hcond,
  have : σ.near_litter_value A' N' hN = N₂,
  rw ← (σ.prop.backward.one_to_one A').near_litter _ (near_litter_value_spec σ A' N' hN) hcond, refl,
  rw [this,hsd2] at h,
  by_cases ha2 : a ∈ litter_set (N'.fst),
  { --have : σ.atom_value A' a ha ∈ M
    by_contra h4,
    obtain ⟨N₃, h3, atom_map, ham, ham2⟩ | ⟨hL, h2⟩ | ⟨L', hL, h2, h3⟩ :=
      σ.prop.forward.atom_cond N'.1 A',
    { obtain rfl := (σ.prop.backward.one_to_one A').near_litter _ hM h3,
      rw ham2 at h,
      cases h, all_goals {have h := h.2, dsimp[(range)] at h, push_neg at h_1},
      { have := (σ.prop.backward.one_to_one A').atom _ (atom_value_spec σ A' a ha)
        (hsd1 ⟨a, or.inl ⟨ha2, h4⟩⟩),--⟨a, or.inl ⟨ha2, h4⟩⟩
        specialize h_1 ⟨a, or.inl ⟨ha2, h4⟩⟩,
        exact h_1 (eq.symm this) },
      have := (σ.prop.backward.one_to_one A').atom _ (atom_value_spec σ A' a ha) (ham a ha2),
      --⟨a, or.inl ⟨ha2, h4⟩⟩
      specialize h_1 ⟨a, ha2⟩,
      exact h_1 (eq.symm this) },
    { simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and] at hL,
      specialize hL _ hM,
      simpa only [binary_condition.domain_mk, map_inr, eq_self_iff_true, not_true] using hL },
    { obtain rfl := (σ.prop.backward.one_to_one A').near_litter _ hM hL,
      have : σ.atom_value A' a ha ∉ range sd,
      { cases h,
        exact h.2,
        cases h.2 ((h3 (atom_value_spec σ A' a ha)).mp ha2) },
      dsimp [(range)] at this,
      push_neg at this_1,
      have h5 := (σ.prop.backward.one_to_one A').atom _ (atom_value_spec σ A' a ha)
        (hsd1 ⟨a, or.inl ⟨ha2, h4⟩⟩), --⟨a, or.inl ⟨ha2, h4⟩⟩
      specialize this_1 ⟨a, or.inl ⟨ha2, h4⟩⟩,
      exact this_1 h5.symm } },
  suffices : σ.atom_value A' a ha ∈ range sd,
  { simp only [set.mem_range, set_coe.exists] at this,
    obtain ⟨a', ha', ha'2⟩ := this,
    specialize hsd1 ⟨a', ha'⟩, rw ha'2 at hsd1,
    simp only [subtype.coe_mk, subtype.val_eq_coe] at hsd1,
    obtain rfl := (σ.prop.forward.one_to_one A').atom _ (atom_value_spec σ A' a ha) hsd1,
    rw symm_diff_def at ha',
    cases ha',
    cases ha2 ha'_1.1,
    exact ha'_1.1 },
  cases h,
  { exfalso,
    obtain ⟨N₃, h3, atom_map, ham, ham2⟩ | ⟨hL, h2⟩ | ⟨L', hL, h2, h3⟩ :=
      σ.prop.forward.atom_cond N'.1 A',
    { obtain rfl := (σ.prop.backward.one_to_one A').near_litter _ h3 hM,
      rw ham2 at h, have h := h.1,
      simp only [set.mem_range, set_coe.exists] at h,
      obtain ⟨a', ha', ha'2⟩ := h,
      specialize ham a' ha',
      rw ha'2 at ham,
      obtain rfl := (σ.prop.forward.one_to_one A').atom _ (atom_value_spec σ A' a ha) ham,
      exact ha2 ha' },
    { simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and] at hL,
      specialize hL _ hM,
      simpa only [binary_condition.domain_mk, map_inr, eq_self_iff_true, not_true] using hL },
    { obtain rfl := (σ.prop.backward.one_to_one A').near_litter _ hM hL,
      exact ha2 ((h3 (atom_value_spec σ A' a ha)).mpr h.1) } },
  exact h.1,
end

lemma mem_value_iff_value_mem {σ : allowable_spec B} {A : extended_index B} {a : atom}
  (ha : (inl a, A) ∈ (σ : spec B).range) {N : near_litter} (hN : (inr N, A) ∈ (σ : spec B).domain) :
  a ∈ σ.near_litter_value A N hN ↔ σ⁻¹.atom_value A a ha ∈ N :=
begin
  suffices : σ.atom_value A (σ⁻¹.atom_value A a ha) (atom_value_mem_range σ⁻¹ A a ha)
    ∈ σ.near_litter_value A N hN ↔ σ⁻¹.atom_value A a ha ∈ N,
  convert this,
  symmetry,
  convert atom_value_inv σ⁻¹ A a ha,
  simp only [inv_inv],
  apply value_mem_value_iff_mem,
end

end allowable_spec
end con_nf
