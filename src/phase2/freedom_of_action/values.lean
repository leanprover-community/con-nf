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
namespace allowable_spec

variables [params.{u}]

variables {α : Λ} [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [typed_positions.{}] [phase_2_assumptions α] {B : le_index α}

open spec

/-- Gets the value that a given input atom `b` is mapped to
under any allowable `π` extending `σ`. -/
noncomputable def atom_value (σ : allowable_spec B) (A : extended_index B)
  (b : atom) (hb : (inl b, A) ∈ σ.val.domain) : atom :=
@sum.rec _ _ (λ (c : atom × atom ⊕ near_litter × near_litter),
  c.elim (λ atoms, inl atoms.fst) (λ Ns, inr Ns.fst) = inl b → atom)
  (λ lhs _, lhs.snd) (λ lhs h, by cases h)
  (mem_domain.mp hb).some.1
  (congr_arg prod.fst (mem_domain.mp hb).some_spec.2)

lemma atom_value_spec (σ : allowable_spec B) (A : extended_index B) (b : atom)
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

lemma atom_value_spec_range (σ : allowable_spec B) (A : extended_index B) (b : atom)
  (hb : (inl b, A) ∈ σ.val.domain) :
  (inl (atom_value σ A b hb), A) ∈ σ.val.range :=
spec.mem_range.2 ⟨(inl (b, atom_value σ A b hb), A), atom_value_spec σ A b hb, rfl⟩

@[simp] lemma atom_value_eq_of_mem {σ : allowable_spec B} {A : extended_index B}
  {a b : atom} (hab : (inl (a, b), A) ∈ σ.val) :
  atom_value σ A a (mem_domain.2 ⟨_, hab, rfl⟩) = b :=
(σ.property.backward.one_to_one A).atom a (atom_value_spec σ A a $ mem_domain.2 ⟨_, hab, rfl⟩) hab

@[simp] lemma atom_value_eq_of_mem_inv {σ : allowable_spec B} {A : extended_index B}
  {a b : atom} (hab : (inl (a, b), A) ∈ σ.val) :
  atom_value σ⁻¹ A b (inl_mem_range hab) = a :=
(σ.property.forward.one_to_one A).atom b (atom_value_spec σ⁻¹ A b $ (inl_mem_range hab)) hab

lemma atom_value_injective {σ : allowable_spec B} {A : extended_index B}
  {b₁ b₂ : atom} {hb₁ : (inl b₁, A) ∈ σ.val.domain} {hb₂ : (inl b₂, A) ∈ σ.val.domain} :
  σ.atom_value A b₁ hb₁ = σ.atom_value A b₂ hb₂ → b₁ = b₂ :=
begin
  have h₁ := atom_value_spec σ A b₁ hb₁,
  have h₂ := atom_value_spec σ A b₂ hb₂,
  intro hb, rw ← hb at h₂,
  exact (σ.property.forward.one_to_one A).atom (atom_value σ A b₁ hb₁) h₁ h₂,
end

noncomputable def atom_value_inj (σ : allowable_spec B) (A : extended_index B) :
  {b | (inl b, A) ∈ σ.val.domain} ↪ atom :=
⟨λ b, atom_value σ A b.val b.property, λ b₁ b₂ hb, subtype.coe_injective (atom_value_injective hb)⟩

lemma atom_value_mem_inv (σ : allowable_spec B) (A : extended_index B) (b : atom)
  (hb : (inl b, A) ∈ σ.val.domain) :
  (inl (atom_value σ A b hb, b), A) ∈ σ⁻¹.val :=
atom_value_spec σ A b hb

lemma atom_value_mem_range (σ : allowable_spec B) (A : extended_index B) (b : atom)
  (hb : (inl b, A) ∈ σ.val.domain) :
  (inl (atom_value σ A b hb), A) ∈ σ.val.range :=
begin
  rw spec.mem_range,
  exact ⟨_, atom_value_spec σ A b hb, rfl⟩,
end

/-- Composing the `atom_value` operation with the inverse permutation does nothing. -/
lemma atom_value_inv (σ : allowable_spec B) (A : extended_index B) (b : atom)
  (hb : (inl b, A) ∈ σ.val.domain) :
  atom_value σ⁻¹ A (atom_value σ A b hb) (atom_value_mem_range σ A b hb) = b :=
begin
  have := atom_value_spec σ⁻¹ A (atom_value σ A b hb) (atom_value_mem_range σ A b hb),
  simp_rw [allowable_spec.val_inv, spec.inl_mem_inv] at this,
  exact (σ.property.forward.one_to_one A).atom _ this (atom_value_spec σ A b hb),
end

/-- Gets the value that a given input near litter `N` is mapped to
under any allowable `π` extending `σ`. -/
noncomputable def near_litter_value (σ : allowable_spec B) (A : extended_index B)
  (N : near_litter) (hb : (inr N, A) ∈ σ.val.domain) : near_litter :=
@sum.rec _ _ (λ (c : atom × atom ⊕ near_litter × near_litter),
  c.elim (λ atoms, inl atoms.fst) (λ Ns, inr Ns.fst) = inr N → near_litter)
  (λ lhs h, by cases h) (λ lhs _, lhs.snd)
  (mem_domain.mp hb).some.1
  (congr_arg prod.fst (mem_domain.mp hb).some_spec.2)

lemma near_litter_value_spec (σ : allowable_spec B) (A : extended_index B) (N : near_litter)
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

lemma near_litter_value_spec_range (σ : allowable_spec B) (A : extended_index B)
  (N : near_litter) (hN : (inr N, A) ∈ σ.val.domain) :
  (inr (near_litter_value σ A N hN), A) ∈ σ.val.range :=
spec.mem_range.2 ⟨(inr (N, near_litter_value σ A N hN), A), near_litter_value_spec σ A N hN, rfl⟩

lemma near_litter_value_injective (σ : allowable_spec B) (A : extended_index B) :
  ∀ N₁ hN₁ N₂ hN₂, near_litter_value σ A N₁ hN₁ = near_litter_value σ A N₂ hN₂ → N₁ = N₂ :=
begin
  intros N₁ hN₁ N₂ hN₂ hN,
  have h₁ := near_litter_value_spec σ A N₁ hN₁,
  have h₂ := near_litter_value_spec σ A N₂ hN₂,
  rw ← hN at h₂,
  exact (σ.property.forward.one_to_one A).near_litter _ h₁ h₂,
end

noncomputable def near_litter_value_inj (σ : allowable_spec B) (A : extended_index B) :
  {N | (inr N, A) ∈ σ.val.domain} ↪ near_litter :=
⟨λ N, near_litter_value σ A N.val N.property, begin
  intros N₁ N₂ hN,
  exact subtype.coe_inj.mp (near_litter_value_injective _ _ _ _ _ _ hN),
end⟩

/-- If the images of two litters under `σ` intersect, the litters must intersect, and therefore are
equal. This is a rather technical result depending on various allowability conditions. -/
lemma litter_eq_of_image_inter (σ : allowable_spec B) (A : extended_index B)
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

lemma litter_image_disjoint (σ : allowable_spec B) (A : extended_index B)
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

lemma litter_ne_of_disjoint {N M : near_litter} (h : disjoint N.2.1 M.2.1) : N.1 ≠ M.1 :=
begin
by_contra h2, cases N, cases M, simp only at h h2, subst h2,
have : litter_set N_fst ⊆ (litter_set N_fst ∆ N_snd.val) ∪(litter_set N_fst ∆ M_snd.val),
{intros x hx, simp only [subtype.val_eq_coe, mem_union_eq], by_contra h3, push_neg at h3,
rw ← symm_diff_symm_diff_cancel_right (litter_set N_fst) N_snd.val at h,
rw ← symm_diff_symm_diff_cancel_right (litter_set N_fst) M_snd.val at h,
apply @h x, rw [symm_diff_comm _ ↑N_snd,symm_diff_comm _ ↑M_snd] at h3,
exact ⟨or.inr ⟨hx, h3.left⟩, or.inr ⟨hx, h3.right⟩⟩,
},
have := lt_of_le_of_lt (le_trans (cardinal.mk_le_mk_of_subset this) (cardinal.mk_union_le _ _))
(cardinal.add_lt_of_lt κ_regular.aleph_0_le N_snd.property M_snd.property),
have h2:= N_fst.to_near_litter.2.property, dsimp [(litter.to_near_litter)] at h2,
rw is_near_litter.mk_eq_κ h2 at this,
simp only [lt_self_iff_false] at this, exact this,
end

-- An application of the near litter condition using litter_image_disjoint.
lemma near_litter_image_disjoint (σ : allowable_spec B) (A : extended_index B)
  {N M N' M' : near_litter}
  (hN : (inr (N, N'), A) ∈ σ.val) (hM : (inr (M, M'), A) ∈ σ.val) :
  disjoint N.snd.val M.snd.val → disjoint N'.snd.val M'.snd.val :=
begin
intro hdisj,
have h:∀ (L : litter) (L' : near_litter) (h : (inr (L.to_near_litter, L'), A) ∈ σ.val) (a b : atom) (hab : (inl (a, b), A) ∈ σ.val ), a ∈ litter_set L ↔ b ∈ L'.2.1,
{
  intros,
   obtain ⟨L'', hL, atom_map, hall, hall2⟩ | ⟨ha, hL, hsmall_out⟩ | ⟨L'', hL, hsmall_in, hsmall_in2⟩ := σ.property.forward.atom_cond L A,
   {
    have := (σ.property.backward.one_to_one A).near_litter _ h hL, subst this,
    rw hall2, unfold range, simp only [set_coe.exists, mem_set_of_eq],
    split, intro ha,  have := hall a ha,
    have := (σ.property.backward.one_to_one A).atom _ hab this, subst this, exact ⟨_, ha, rfl ⟩,
    rintros ⟨x, hx, hx2⟩, have := hall x hx, rw hx2 at this,
    have := (σ.property.forward.one_to_one A).atom _ hab this, subst this, exact hx,
   },
   {
    simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and] at ha,
    have := ha _ h, simp only [binary_condition.domain_mk, map_inr, eq_self_iff_true, not_true] at this,
    exfalso, exact this,
   },
   {
    have := (σ.property.backward.one_to_one A).near_litter _ h hL, subst this,
    exact hsmall_in2 hab,
   }
},
have h2 : ∀  {N M N' M' Nf' Mf' : near_litter}
  (hN : (inr (N, N'), A) ∈ σ.val) (hN2 : (inr (N.fst.to_near_litter, Nf'), A) ∈ σ.val)
  (hM : (inr (M, M'), A) ∈ σ.val) (hM2 : (inr (M.fst.to_near_litter, Mf'), A) ∈ σ.val)
  (hdisj : disjoint N.snd.val M.snd.val) (a b: atom)  (hab : (inl (a, b), A) ∈ σ.val )
  (hb1 : b ∈ (N'.2.1 \ Nf'.2.1)) (hb2 : b ∈ (Mf'.2.1 ∩ M'.2.1)), false,
  {
    clear hdisj hN hM N M N' M',
    intros,
    obtain ⟨Nf'', hNf'', ⟨symm_diff_N, ⟨hsdN1, hsdN2⟩⟩ ⟩ := σ.property.forward.near_litter_cond _ _ _ hN,
    have := (σ.property.backward.one_to_one A).near_litter _ hN2 hNf'', subst this,
    obtain ⟨Mf'', hMf'', ⟨symm_diff_M, ⟨hsdM1, hsdM2⟩⟩ ⟩ := σ.property.forward.near_litter_cond _ _ _ hM,
    have := (σ.property.backward.one_to_one A).near_litter _ hM2 hMf'', subst this,
    have ha3 := hb1, rw [hsdN2, symm_diff_def, sup_eq_union, set.union_diff_distrib] at ha3,
    simp only [subtype.val_eq_coe, sdiff_sdiff_self, bot_eq_empty, sdiff_idem, empty_union, mem_diff, set.mem_range, set_coe.exists] at ha3,
    obtain ⟨⟨c, hc1, hc2⟩, _⟩ := ha3, have := (hsdN1 ⟨c, hc1⟩), rw hc2 at this, rw ← subtype.val_eq_coe at this, simp only at this,
    have := (σ.property.forward.one_to_one A).atom _ hab this, subst this,
    cases hc1,
    exact (not_mem_of_mem_diff hb1) ((h N.fst Nf' hN2 a b hab).mp (mem_of_mem_diff hc1)),
    have := (h M.fst Mf' hM2 a b hab).mpr (hb2.1),
    have : a ∈ litter_set M.fst ∆ ↑(M.snd),
    {
      by_cases ha : a ∈ ↑(M.snd),
      exfalso, exact hdisj ⟨mem_of_mem_diff hc1, ha⟩,
      exact or.inl ⟨this, ha⟩,
    },
    have := hsdM1 ⟨a, this⟩, rw ← subtype.val_eq_coe at this, simp only at this,
    have := (σ.property.backward.one_to_one A).atom _ hab this, subst this,
    rw hsdM2 at hb2,
    obtain ⟨hb3, hb4⟩ := hb2,
    cases hb4,
    have := not_mem_of_mem_diff hb4, simp only [mem_range_self, not_true] at this, exact this,
    exact (not_mem_of_mem_diff hb4) hb3,
  },

rintros b ⟨hb1, hb2⟩,
obtain ⟨Nf', hNf', ⟨symm_diff_N, ⟨hsdN1,hsdN2⟩⟩⟩ := σ.property.forward.near_litter_cond _ _ _ hN,
obtain ⟨Mf', hMf', ⟨symm_diff_M, ⟨hsdM1,hsdM2⟩⟩⟩ := σ.property.forward.near_litter_cond _ _ _ hM,
by_cases hb3 : b ∈ Nf'.2.1, all_goals {by_cases hb4 : b ∈ Mf'.2.1},
{refine (litter_image_disjoint σ A hNf' hMf' _) ⟨hb3, hb4⟩,
exact litter_ne_of_disjoint hdisj,
},
{have := hb2, rw hsdM2 at this, cases this, exact hb4 (mem_of_mem_diff this), have := this.1,
simp only [set.mem_range, set_coe.exists] at this, obtain ⟨a, ha1, ha2⟩  := this,
have hab := hsdM1 ⟨a, ha1⟩, rw ha2 at hab,
exact h2 hM hMf' hN hNf' (disjoint.symm hdisj) a b hab ⟨hb2, hb4⟩ ⟨hb3, hb1⟩,
},
{have := hb1, rw hsdN2 at this, cases this, exact hb3 (mem_of_mem_diff this), have := this.1,
simp only [set.mem_range, set_coe.exists] at this, obtain ⟨a, ha1, ha2⟩  := this,
have hab := hsdN1 ⟨a, ha1⟩, rw ha2 at hab,
exact h2 hN hNf' hM hMf' hdisj a b hab ⟨hb1, hb3⟩ ⟨hb4, hb2⟩,
},
{
have := hb2, rw hsdM2 at this, cases this, exact hb4 (mem_of_mem_diff this), have := this.1,
simp only [set.mem_range, set_coe.exists] at this, obtain ⟨a, ha1, ha2⟩  := this, clear this,
have := hb1, rw hsdN2 at this, cases this, exact hb3 (mem_of_mem_diff this), have := this.1,
simp only [set.mem_range, set_coe.exists] at this, obtain ⟨a', ha'1, ha'2⟩  := this,
have hab := (hsdM1 ⟨a, ha1⟩), have ha'b := (hsdN1 ⟨a', ha'1⟩), rw ha2 at hab, rw ha'2 at ha'b,
rw ← subtype.val_eq_coe at hab ha'b, simp only at hab ha'b,
have := (σ.property.forward.one_to_one A).atom _ hab ha'b, subst this,
cases ha1, exact hb4 ((h M.fst Mf' hMf' a b hab).mp ha1.1),
cases ha'1, exact hb3 ((h N.fst Nf' hNf' a b hab).mp ha'1.1),
exact hdisj ⟨ha'1.1, ha1.1⟩,
}
end

-- Whoever's proving this, first factor out the one-directional lemma.
-- Then it should follow from symmetry and involutivity.
lemma value_mem_value_iff_mem {σ : allowable_spec B} {A : extended_index B}
  {a : atom} (ha : (inl a, A) ∈ σ.val.domain) {N : near_litter} (hN : (inr N, A) ∈ σ.val.domain) :
  σ.atom_value A a ha ∈ (σ.near_litter_value A N hN).2.val ↔ a ∈ N.2.val :=
sorry

lemma mem_value_iff_value_mem {σ : allowable_spec B} {A : extended_index B}
  {a : atom} (ha : (inl a, A) ∈ σ.val.range) {N : near_litter} (hN : (inr N, A) ∈ σ.val.domain) :
  a ∈ (σ.near_litter_value A N hN).2.val ↔ σ⁻¹.atom_value A a ha ∈ N.2.val :=
sorry

end allowable_spec
end con_nf
