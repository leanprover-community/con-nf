import phase2.freedom_of_action.allowable

/-!
# Value API for allowable partial permutations

Allowable partial permutations satisfy a "one-to-one" condition that means that if `(x, A)` lies in
the domain of `σ` (for example), then there is a unique value `y` that `x` is mapped to under any
allowable permutation satisfying the specification. This API allows us to retrieve these values.
Since this data is behind existentials, many of the definitions are noncomputable.
-/

open set sum

universe u

namespace con_nf
namespace allowable_partial_perm

variables [params.{u}]

variables {α : Λ} [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [phase_2_assumptions α] {B : le_index α}

open spec

/-- Gets the value that a given input atom `b` is mapped to
under any allowable `π` extending `σ`. -/
noncomputable def atom_value (σ : allowable_partial_perm B) (A : extended_index B)
  (b : atom) (hb : (inl b, A) ∈ σ.val.domain) : atom :=
@sum.rec _ _ (λ (c : atom × atom ⊕ near_litter × near_litter),
  c.elim (λ atoms, inl atoms.fst) (λ Ns, inr Ns.fst) = inl b → atom)
  (λ lhs _, lhs.snd) (λ lhs h, by cases h)
  (mem_domain.mp hb).some.1
  (congr_arg prod.fst (mem_domain.mp hb).some_spec.2)

lemma atom_value_spec (σ : allowable_partial_perm B) (A : extended_index B) (b : atom)
  (hb : (inl b, A) ∈ σ.val.domain) :
  (inl (b, atom_value σ A b hb), A) ∈ σ.val :=
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
    exact (σ.property.backward.one_to_one A).atom b hc₁ hd₁ },
  { cases hc₂ }
end

lemma atom_value_spec_range (σ : allowable_partial_perm B) (A : extended_index B) (b : atom)
  (hb : (inl b, A) ∈ σ.val.domain) :
  (inl (atom_value σ A b hb), A) ∈ σ.val.range :=
spec.mem_range.2 ⟨(inl (b, atom_value σ A b hb), A), atom_value_spec σ A b hb, rfl⟩

@[simp] lemma atom_value_eq_of_mem (σ : allowable_partial_perm B) (A : extended_index B)
  (a b : atom) (hab : (inl (a, b), A) ∈ σ.val) :
  atom_value σ A a (mem_domain.2 ⟨_, hab, rfl⟩) = b :=
(σ.property.backward.one_to_one A).atom a (atom_value_spec σ A a $ mem_domain.2 ⟨_, hab, rfl⟩) hab

noncomputable def atom_value_inj (σ : allowable_partial_perm B) (A : extended_index B) :
  {b | (inl b, A) ∈ σ.val.domain} ↪ atom :=
⟨λ b, atom_value σ A b.val b.property, λ b₁ b₂ hb, begin
  have h₁ := atom_value_spec σ A b₁ b₁.property,
  have h₂ := atom_value_spec σ A b₂ b₂.property,
  dsimp at hb, rw ← hb at h₂,
  exact subtype.coe_inj.mp
    ((σ.property.forward.one_to_one A).atom (atom_value σ A b₁ b₁.property) h₁ h₂),
end⟩

lemma atom_value_mem_inv (σ : allowable_partial_perm B) (A : extended_index B) (b : atom)
  (hb : (inl b, A) ∈ σ.val.domain) :
  (inl (atom_value σ A b hb, b), A) ∈ σ⁻¹.val :=
atom_value_spec σ A b hb

lemma atom_value_mem_range (σ : allowable_partial_perm B) (A : extended_index B) (b : atom)
  (hb : (inl b, A) ∈ σ.val.domain) :
  (inl (atom_value σ A b hb), A) ∈ σ.val.range :=
begin
  rw spec.mem_range,
  exact ⟨_, atom_value_spec σ A b hb, rfl⟩,
end

/-- Composing the `atom_value` operation with the inverse permutation does nothing. -/
lemma atom_value_inv (σ : allowable_partial_perm B) (A : extended_index B) (b : atom)
  (hb : (inl b, A) ∈ σ.val.domain) :
  atom_value σ⁻¹ A (atom_value σ A b hb) (atom_value_mem_range σ A b hb) = b :=
begin
  have := atom_value_spec σ⁻¹ A (atom_value σ A b hb) (atom_value_mem_range σ A b hb),
  simp_rw [allowable_partial_perm.val_inv, spec.inl_mem_inv] at this,
  exact (σ.property.forward.one_to_one A).atom _ this (atom_value_spec σ A b hb),
end

/-- Gets the value that a given input near litter `N` is mapped to
under any allowable `π` extending `σ`. -/
noncomputable def near_litter_value (σ : allowable_partial_perm B) (A : extended_index B)
  (N : near_litter) (hb : (inr N, A) ∈ σ.val.domain) : near_litter :=
@sum.rec _ _ (λ (c : atom × atom ⊕ near_litter × near_litter),
  c.elim (λ atoms, inl atoms.fst) (λ Ns, inr Ns.fst) = inr N → near_litter)
  (λ lhs h, by cases h) (λ lhs _, lhs.snd)
  (mem_domain.mp hb).some.1
  (congr_arg prod.fst (mem_domain.mp hb).some_spec.2)

lemma near_litter_value_spec (σ : allowable_partial_perm B) (A : extended_index B) (N : near_litter)
  (hN : (inr N, A) ∈ σ.val.domain) :
  (inr (N, near_litter_value σ A N hN), A) ∈ σ.val :=
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
  exact (σ.property.backward.one_to_one A).near_litter N hc₁ hd₁,
end

lemma near_litter_value_spec_range (σ : allowable_partial_perm B) (A : extended_index B)
  (N : near_litter) (hN : (inr N, A) ∈ σ.val.domain) :
  (inr (near_litter_value σ A N hN), A) ∈ σ.val.range :=
spec.mem_range.2 ⟨(inr (N, near_litter_value σ A N hN), A), near_litter_value_spec σ A N hN, rfl⟩

noncomputable def near_litter_value_inj (σ : allowable_partial_perm B) (A : extended_index B) :
  {N | (inr N, A) ∈ σ.val.domain} ↪ near_litter :=
⟨λ N, near_litter_value σ A N.val N.property, begin
  intros N₁ N₂ hN,
  have h₁ := near_litter_value_spec σ A N₁ N₁.property,
  have h₂ := near_litter_value_spec σ A N₂ N₂.property,
  dsimp at hN, rw ← hN at h₂,
  exact subtype.coe_inj.mp
    ((σ.property.forward.one_to_one A).near_litter (near_litter_value σ A N₁ N₁.property) h₁ h₂),
end⟩

/-- If the images of two litters under `σ` intersect, the litters must intersect, and therefore are
equal. This is a rather technical result depending on various allowability conditions. -/
lemma litter_eq_of_image_inter (σ : allowable_partial_perm B) (A : extended_index B)
  {L₁ L₂ : litter} {N₁ N₂ : near_litter}
  (hL₁ : (inr (L₁.to_near_litter, N₁), A) ∈ σ.val)
  (hL₂ : (inr (L₂.to_near_litter, N₂), A) ∈ σ.val)
  (a : atom)
  (haN₁ : a ∈ N₁.snd.val)
  (haN₂ : a ∈ N₂.snd.val) : L₁ = L₂ :=
begin
  obtain ⟨N, h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N, hN, h₁, h₂⟩ :=
    σ.property.forward.atom_cond L₁ A,
  { cases (σ.property.backward.one_to_one A).near_litter _ hL₁ h₁,
    rw h₃ at haN₁,
    obtain ⟨a₁, ha₁⟩ := haN₁,
    have map₁ := h₂ a₁ a₁.property,
    rw subtype.coe_eta at map₁,
    rw ha₁ at map₁,

    obtain ⟨N', h₁', atom_map', h₂', h₃'⟩ | ⟨h₁', h₂'⟩ | ⟨N', hN', h₁', h₂'⟩ :=
      σ.property.forward.atom_cond L₂ A,
    { cases (σ.property.backward.one_to_one A).near_litter _ hL₂ h₁',
      rw h₃' at haN₂,
      obtain ⟨a₂, ha₂⟩ := haN₂,
      have map₂ := h₂' a₂ a₂.property,
      rw subtype.coe_eta at map₂,
      rw ha₂ at map₂,
      obtain ⟨⟨a₁L, a₁⟩, ha₁'⟩ := a₁,
      obtain ⟨⟨a₂L, a₂⟩, ha₂'⟩ := a₂,
      cases (σ.property.forward.one_to_one A).atom a map₁ map₂, cases ha₁', cases ha₂', refl },
    { rw mem_domain at h₁', cases h₁' ⟨_, hL₂, rfl⟩ },
    { cases (σ.property.backward.one_to_one A).near_litter _ hL₂ hN',
      have := h₂' (h₂ a₁ a₁.property),
      rw subtype.coe_eta at this,
      rw ha₁ at this,
      obtain ⟨⟨a₁L, a₁⟩, ha₁'⟩ := a₁,
      cases this.mpr haN₂, cases ha₁', refl } },
  { rw mem_domain at h₁, cases h₁ ⟨_, hL₁, rfl⟩ },
  cases (σ.property.backward.one_to_one A).near_litter _ hL₁ hN,
  obtain ⟨N', h₁', atom_map', h₂', h₃'⟩ | ⟨h₁', h₂'⟩ | ⟨N', hN', h₁', h₂'⟩ :=
    σ.property.forward.atom_cond L₂ A,
  { cases (σ.property.backward.one_to_one A).near_litter _ hL₂ h₁',
    rw h₃' at haN₂,
    obtain ⟨a₂, ha₂⟩ := haN₂,
    have map₂ := h₂' a₂ a₂.property,
    rw subtype.coe_eta at map₂,
    rw ha₂ at map₂,
    have := h₂ (h₂' a₂ a₂.property),
    rw subtype.coe_eta at this,
    rw ha₂ at this,
    obtain ⟨⟨a₂L, a₂⟩, ha₂'⟩ := a₂,
    cases this.mpr haN₁, cases ha₂', refl },
  { rw mem_domain at h₁', cases h₁' ⟨_, hL₂, rfl⟩ },
  cases (σ.property.backward.one_to_one A).near_litter _ hL₂ hN',
  obtain ⟨M₁, hM₁, s₁, hs₁, gs₁⟩ := σ.property.backward.near_litter_cond _ _ A hL₁,
  obtain ⟨M₂, hM₂, s₂, hs₂, gs₂⟩ := σ.property.backward.near_litter_cond _ _ A hL₂,
  dsimp only at gs₁ gs₂,
  cases eq_empty_or_nonempty ((N₁.snd.val \ litter_set N₁.fst) ∩ N₂.snd) with hN₁ hN₁,
  { cases eq_empty_or_nonempty ((N₂.snd.val \ litter_set N₂.fst) ∩ N₁.snd) with hN₂ hN₂,
    { rw eq_empty_iff_forall_not_mem at hN₁ hN₂, specialize hN₁ a, specialize hN₂ a,
      rw [mem_inter_iff, and_comm, mem_diff] at hN₁ hN₂,
      push_neg at hN₁ hN₂, specialize hN₁ haN₂ haN₁, specialize hN₂ haN₁ haN₂,
      have := eq_of_mem_litter_set_of_mem_litter_set hN₁ hN₂,
      rw this at hM₁,
      have M₁_eq_M₂ := (σ.property.forward.one_to_one A).near_litter _ hM₁ hM₂,
      dsimp only at M₁_eq_M₂, subst M₁_eq_M₂,
      refine is_near_litter_litter_set_iff.1 _,
      unfold is_near_litter is_near,
      rw [gs₁, gs₂, symm_diff_left_comm, ← symm_diff_assoc, symm_diff_symm_diff_cancel_left],
      refine ((cardinal.mk_le_mk_of_subset $ symm_diff_le_sup (range s₁) $ range s₂).trans $
        cardinal.mk_union_le _ _).trans_lt _,
      exact cardinal.add_lt_of_lt κ_regular.aleph_0_le
        (cardinal.mk_range_le.trans_lt N₁.2.2) (cardinal.mk_range_le.trans_lt N₂.2.2) },
    { obtain ⟨aN₂, haN₂, haN₂'⟩ := hN₂,
      have := hs₂ ⟨aN₂, or.inr haN₂⟩,
      exact eq_of_mem_litter_set_of_mem_litter_set
        ((h₂ this).symm.mp haN₂') ((h₂' this).symm.mp haN₂.left) } },
  { obtain ⟨aN₁, haN₁, haN₁'⟩ := hN₁,
      have := hs₁ ⟨aN₁, or.inr haN₁⟩,
      exact eq_of_mem_litter_set_of_mem_litter_set
        ((h₂ this).symm.mp haN₁.left) ((h₂' this).symm.mp haN₁') }
end

lemma litter_image_disjoint (σ : allowable_partial_perm B) (A : extended_index B)
  {L₁ L₂ : litter} {N₁ N₂ : near_litter}
  (hN₁ : (inr (L₁.to_near_litter, N₁), A) ∈ σ.val)
  (hN₂ : (inr (L₂.to_near_litter, N₂), A) ∈ σ.val) :
  L₁ ≠ L₂ → disjoint N₁.snd.val N₂.snd.val :=
begin
  contrapose!,
  rw not_disjoint_iff,
  rintro ⟨a, ha₁, ha₂⟩,
  exact litter_eq_of_image_inter σ A hN₁ hN₂ a ha₁ ha₂,
end

-- An application of the near litter condition using litter_image_disjoint.
lemma near_litter_image_disjoint (σ : allowable_partial_perm B) (A : extended_index B)
  {N M N' M' : near_litter}
  (hN : (inr (N, N'), A) ∈ σ.val) (hM : (inr (M, M'), A) ∈ σ.val) :
  disjoint N.snd.val M.snd.val → disjoint N'.snd.val M'.snd.val :=
sorry

end allowable_partial_perm
end con_nf
