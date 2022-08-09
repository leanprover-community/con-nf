import phase2.freedom_of_action.allowable

/-!
# Applying Zorn's lemma

We define a preorder on partial allowable permutations.
`σ ≤ ρ` (written `σ ⊑ ρ` in the blueprint) means:

* `σ` is a subset of `ρ`;
* if `ρ` has any new `A`-flexible litter, then it has all (in both domain and range);
* within each litter, if `ρ.domain` has any new atom, then it must have all
    atoms in that litter (and hence must also have the litter), and dually for the range.

Note that the second condition is exactly the condition in `spec.flexible_cond.all`.

To prove that Zorn's lemma can be applied, we must show that for any chain `c` of allowable
partial permutations, the union of the specifications in the chain is allowable, and carefully
extends every element of the chain.

The non-trivial part of this proof is the "small or all" conditions for atoms and flexible litters.
Due to the particular construction of the preorder `≤`, if we add any atom (resp. flexible litter),
we must add all of them.
-/

open set sum

universe u

namespace con_nf
namespace allowable_partial_perm

variables [params.{u}]

variables {α : Λ} [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [typed_positions.{}] [phase_2_assumptions α] {B : le_index α}

open spec

structure perm_le (σ ρ : allowable_partial_perm B) : Prop :=
(le : σ.val ≤ ρ.val)
(all_flex_domain (L : litter) (N : near_litter) (A : extended_index B) (hL : flexible L A)
  (hσ : (⟨inr ⟨L.to_near_litter, N⟩, A⟩ : binary_condition B) ∉ σ.val)
  (hρ : (⟨inr ⟨L.to_near_litter, N⟩, A⟩ : binary_condition B) ∈ ρ.val) :
  (∀ L', flexible L' A →
    (⟨inr L'.to_near_litter, A⟩ : support_condition B) ∈ ρ.val.domain ∧
    (⟨inr L'.to_near_litter, A⟩ : support_condition B) ∈ ρ.val.range))
(all_flex_range (L : litter) (N : near_litter) (A : extended_index B) (hL : flexible L A)
  (hσ : (⟨inr ⟨N, L.to_near_litter⟩, A⟩ : binary_condition B) ∉ σ.val)
  (hρ : (⟨inr ⟨N, L.to_near_litter⟩, A⟩ : binary_condition B) ∈ ρ.val) :
  (∀ L', flexible L' A →
    (⟨inr L'.to_near_litter, A⟩ : support_condition B) ∈ ρ.val.domain ∧
    (⟨inr L'.to_near_litter, A⟩ : support_condition B) ∈ ρ.val.range))
(all_atoms_domain (a b : atom) (L : litter) (ha : a ∈ litter_set L) (A : extended_index B)
  (hσ : (⟨inl ⟨a, b⟩, A⟩ : binary_condition B) ∉ σ.val)
  (hρ : (⟨inl ⟨a, b⟩, A⟩ : binary_condition B) ∈ ρ.val) :
  ∀ c ∈ litter_set L, ∃ d, (⟨inl ⟨c, d⟩, A⟩ : binary_condition B) ∈ ρ.val)
(all_atoms_range (a b : atom) (L : litter) (ha : b ∈ litter_set L) (A : extended_index B)
  (hσ : (⟨inl ⟨a, b⟩, A⟩ : binary_condition B) ∉ σ.val)
  (hρ : (⟨inl ⟨a, b⟩, A⟩ : binary_condition B) ∈ ρ.val) :
  ∀ c ∈ litter_set L, ∃ d, (⟨inl ⟨d, c⟩, A⟩ : binary_condition B) ∈ ρ.val)

instance has_le : has_le (allowable_partial_perm B) := ⟨perm_le⟩

/-! We now prove that the claimed preorder really is a preorder. -/

lemma extends_refl (σ : allowable_partial_perm B) : σ ≤ σ :=
⟨subset.rfl,
 λ _ _ _ _ h1 h2, by cases h1 h2,
 λ _ _ _ _ h1 h2, by cases h1 h2,
 λ _ _ _ _ _ h1 h2, by cases h1 h2,
 λ _ _ _ _ _ h1 h2, by cases h1 h2⟩

lemma extends_trans (ρ σ τ : allowable_partial_perm B) (h₁ : ρ ≤ σ) (h₂ : σ ≤ τ) : ρ ≤ τ :=
begin
  obtain ⟨hsub, hflx_domain, hflx_range, hatom_domain, hatom_range⟩ := h₁,
  obtain ⟨hsub', hflx_domain', hflx_range', hatom_domain', hatom_range'⟩ := h₂,
  refine ⟨hsub.trans hsub', λ L N A hLA hnin hin, _, λ L N A hLA hnin hin, _,
    λ a b L hab A hnin hin, _, λ a b L hab A hnin hin, _⟩,
  { by_cases (inr (L.to_near_litter, N), A) ∈ σ.val,
    { intros l hla,
      have := hflx_domain L N A hLA hnin h l hla,
      rw [spec.mem_domain, spec.mem_range] at this ⊢,
      obtain ⟨⟨b, hb, hdom⟩, ⟨c, hc, hrge⟩⟩ := this,
      exact ⟨⟨b, hsub' hb, hdom⟩, ⟨c, hsub' hc, hrge⟩⟩ },
    { exact hflx_domain' L N A hLA h hin } },
  { by_cases (inr (N, L.to_near_litter), A) ∈ σ.val,
    { intros l hla,
      have := hflx_range L N A hLA hnin h l hla,
      rw [spec.mem_domain, spec.mem_range] at this ⊢,
      obtain ⟨⟨b, hb, hdom⟩, ⟨c, hc, hrge⟩⟩ := this,
      exact ⟨⟨b, hsub' hb, hdom⟩, ⟨c, hsub' hc, hrge⟩⟩ },
    { exact hflx_range' L N A hLA h hin } },
  { by_cases (inl (a, b), A) ∈ σ.val,
    { intros c hc,
      obtain ⟨d, hd⟩ := hatom_domain a b L hab A hnin h c hc,
      exact ⟨d, hsub' hd⟩ },
    { exact hatom_domain' a b L hab A h hin } },
  { by_cases (inl (a, b), A) ∈ σ.val,
    { intros c hc,
      obtain ⟨d, hd⟩ := hatom_range a b L hab A hnin h c hc,
      refine ⟨d, hsub' hd⟩ },
    { exact hatom_range' a b L hab A h hin } }
end

instance : preorder (allowable_partial_perm B) :=
{ le := perm_le,
  le_refl := extends_refl,
  le_trans := extends_trans }

lemma domain_subset_of_le {σ τ : allowable_partial_perm B} (hστ : σ ≤ τ) :
  σ.val.domain ⊆ τ.val.domain :=
begin
  rintros x hx,
  rw spec.mem_domain at hx ⊢,
  obtain ⟨b, hb, hdom⟩ := hx,
  exact ⟨b, hστ.le hb, hdom⟩,
end
lemma range_subset_of_le {σ τ : allowable_partial_perm B} (hστ : σ ≤ τ) :
  σ.val.range ⊆ τ.val.range :=
begin
  rintros x hx,
  rw spec.mem_range at hx ⊢,
  obtain ⟨b, hb, hdom⟩ := hx,
  exact ⟨b, hστ.le hb, hdom⟩,
end

/-- A condition required later. -/
lemma inv_mono : monotone (@has_inv.inv (allowable_partial_perm B) _) :=
begin
  rintro σ τ ⟨h1, h2, h3, h4, h5⟩,
  refine ⟨λ x h, h1 h,
          λ L N hLA hnin hin L' A' hLA', _,
          λ L N hLA hnin hin L' A' hLA', _,
          λ a b, h5 b a, λ a b, h4 b a⟩; rw [val_inv, spec.domain_inv, spec.range_inv],
  exacts [(h3 L N hLA hnin hin L' A' hLA').symm, (h2 L N hLA hnin hin L' A' hLA').symm],
end

@[simp] lemma inv_le_inv (σ τ : allowable_partial_perm B) : σ⁻¹ ≤ τ⁻¹ ↔ σ ≤ τ :=
⟨λ h, by simpa only [inv_inv] using inv_mono h, λ h, inv_mono h⟩

section zorn_setup

/-! To set up for Zorn's lemma, we need to show that the union of all allowable partial permutations
in a chain is an upper bound for the chain. In particular, we first show that it is allowable, and
then we show it extends all elements in the chain.

Non-trivial bit: the "small or all" conditions — these are enforced by the "if adding any, add all"
parts of the definition of ≤. -/

variables {c : set (allowable_partial_perm B)}

lemma is_subset_chain_of_is_chain : is_chain (≤) c → is_chain (≤) (subtype.val '' c) :=
is_chain.image _ _ _ $ λ _ _, perm_le.le

lemma one_to_one_Union (hc : is_chain (≤) c) : spec.one_to_one_forward (Sup $ subtype.val '' c) :=
begin
  refine λ A, ⟨_, _⟩,
  all_goals
  { simp_rw mem_Sup,
    rintro b x ⟨σx, Hx, hx⟩ y ⟨σy, Hy, hy⟩,
    have hc' := is_subset_chain_of_is_chain hc Hx Hy,
    by_cases (σx = σy),
    rw ← h at hy,
    obtain ⟨⟨σx,hσx⟩, Hx₁, rfl⟩ := Hx,
    swap,
    specialize hc' h,
    cases hc',
    have hx' := hc' hx,
    obtain ⟨⟨σy,hσy⟩, Hy₁, rfl⟩ := Hy,
    swap,
    have hy' := hc' hy,
    obtain ⟨⟨σx,hσx⟩, Hx₁, rfl⟩ := Hx },
  -- Note: there must be a better way of doing this below.
  exact (hσx.forward.one_to_one A).atom b hx hy',
  exact (hσy.forward.one_to_one A).atom b hx' hy,
  exact (hσx.forward.one_to_one A).atom b hx hy,
  exact (hσx.forward.one_to_one A).near_litter b hx hy',
  exact (hσy.forward.one_to_one A).near_litter b hx' hy,
  exact (hσx.forward.one_to_one A).near_litter b hx hy,
end

lemma atom_cond_Union (hc : is_chain (≤) c) (L A) : spec.atom_cond (Sup (subtype.val '' c)) L A :=
begin
  obtain rfl | ⟨⟨σ, hσ₁⟩, hσ₂⟩ := c.eq_empty_or_nonempty,
  { refine spec.atom_cond.small_out _ _,
    { simp only [image_empty, Sup_empty, not_mem_empty, spec.domain_bot, not_false_iff] },
    { simp only [image_empty, Sup_empty, not_mem_empty, spec.domain_bot, sep_false,
        small_empty] } },
  by_cases h' : ∃ (ρ : allowable_partial_perm B) (hρ : ρ ∈ c) (τ : allowable_partial_perm B)
      (hτ : τ ∈ c) a b (ha : a ∈ litter_set L),
      (inl (a, b), A) ∉ ρ.val ∧ (inl (a, b), A) ∈ τ.val ∧ ρ ≤ τ,
  { obtain ⟨ρ, hρ, τ, hτ, a, b, ha, Hρ, Hτ, hρτ⟩ := h',
    obtain ⟨N, h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N, h₁, h₂, h₃⟩ := τ.prop.forward.atom_cond L A,
    { refine spec.atom_cond.all N _ atom_map _ h₃,
      { exact mem_Sup.2 ⟨_, mem_image_of_mem _ hτ, h₁⟩ },
      { exact λ a' ha',mem_Sup.2 ⟨_, mem_image_of_mem _ hτ, h₂ _ ha'⟩ } },
    all_goals
    { cases h₂.lt.ne _,
      rw ← mk_litter_set L, convert rfl,
      ext a',
      refine (and_iff_left_of_imp $ λ ha', _).symm,
      cases hρτ.all_atoms_domain a b L ha A Hρ Hτ a' ha' with d hd,
      exact mem_domain.2 ⟨_, hd, rfl⟩ } },
  push_neg at h',
  have H' : ∀ (ρ : allowable_partial_perm B), ρ ∈ c → ∀ (τ : allowable_partial_perm B),
              τ ∈ c → ∀ (a b : atom), a ∈ litter_set L →
              (inl (a, b), A) ∈ ρ.val → (inl (a, b), A) ∈ τ.val,
  { refine λ ρ hρ τ hτ a b ha Hρ, of_not_not (λ Hτ, _),
    cases h' τ hτ ρ hρ a b ha Hτ Hρ ((hc hτ hρ _).elim id $ λ h, _),
    { rintro rfl,
      exact Hτ Hρ },
    { cases Hτ (h.1 Hρ) } },
  have : {a ∈ litter_set L | (inl a, A) ∈ (Sup (subtype.val '' c)).domain}
          = {a ∈ litter_set L | (inl a, A) ∈ σ.domain},
  { ext a,
    simp_rw [mem_sep_iff, mem_domain, mem_Sup],
    refine and_congr_right (λ ha, ⟨_, _⟩),
    { rintro ⟨⟨⟨a', b⟩ | _, C⟩, ⟨_, ⟨ρ, hρ, rfl⟩, hb⟩, hab⟩; cases hab,
      refine ⟨_, H' ρ hρ _ hσ₂ a b ha hb, rfl⟩ },
    { exact λ ⟨b, hbσ, hba⟩, ⟨b, ⟨σ, ⟨_, hσ₂, rfl⟩, hbσ⟩, hba⟩ } },
  obtain ⟨N, h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N, hN, h₁, h₂⟩ := hσ₁.forward.atom_cond L A,
  { exact spec.atom_cond.all N (mem_Sup.2 ⟨_, mem_image_of_mem _ hσ₂, h₁⟩) atom_map
        (λ a' ha', mem_Sup.2 ⟨_, mem_image_of_mem _ hσ₂, h₂ _ ha'⟩) h₃ },
  { by_cases (inr L.to_near_litter, A) ∈ (Sup (subtype.val '' c)).domain,
    { rw mem_domain at h,
      obtain ⟨⟨_ | ⟨N₁, N₂⟩, C⟩, hc₁, ⟨⟩⟩ := h,
      refine spec.atom_cond.small_in N₂ hc₁ (by rwa this) _,
      simp_rw mem_Sup at ⊢ hc₁,
      rintro a' b ⟨_, ⟨⟨τ, hτ⟩, hτc, rfl⟩, hτa'⟩,
      obtain ⟨_, ⟨⟨ρ, hρ⟩, hρc, rfl⟩, hρN₂⟩ := hc₁,
      obtain ⟨N', h₁', atom_map', h₂', h₃'⟩ | ⟨h₁', h₂'⟩ | ⟨N', hN', h₁', h₂'⟩ :=
        hρ.forward.atom_cond L A,
      { rw [(hρ.backward.one_to_one A).near_litter _ hρN₂ h₁', h₃'],
        refine ⟨λ ha', ⟨⟨a', ha'⟩,
            (hτ.backward.one_to_one A).atom _ (H' _ hρc _ hτc _ _ ha' (h₂' a' ha')) hτa'⟩, _⟩,
        rintro ⟨⟨b', hb'⟩, rfl⟩,
        have := (hτ.forward.one_to_one A).atom _ (H' _ hρc _ hτc _ _ hb' (h₂' b' hb')) hτa',
        rwa this at hb' },
      { cases h₁' (mem_domain.2 ⟨_, hρN₂, rfl⟩) },
      { rw [(hρ.backward.one_to_one A).near_litter _ hρN₂ hN'],
        refine ⟨λ ha', (h₂' $ H' _ hτc _ hρc _ _ ha' hτa').1 ha', λ hb, _⟩,
        sorry } },
    { exact spec.atom_cond.small_out h (by rwa this) } },
  { refine spec.atom_cond.small_in N _ _ _,
    { exact mem_Sup.2 ⟨_, mem_image_of_mem _ hσ₂, hN⟩ },
    { rwa this },
    simp_rw mem_Sup,
    rintro a' b ⟨_, ⟨⟨τ, hτ⟩, hτc, rfl⟩, hτa'⟩,
    refine ⟨λ ha', (h₂ $ H' _ hτc _ hσ₂ a' b ha' hτa').1 ha', _⟩,
    sorry }
end

lemma near_litter_cond_Union (hc : is_chain (≤) c) (N₁ N₂ A) :
  (Sup (subtype.val '' c)).near_litter_cond N₁ N₂ A :=
begin
  rintro h,
  rw mem_Sup at h,
  obtain ⟨ρ, ⟨σ, hσ, rfl⟩, hρ⟩ := h,
  obtain ⟨M, hM, f, h1, h2⟩ := σ.prop.forward.near_litter_cond N₁ N₂ A hρ,
  exact ⟨M, mem_Sup.2 ⟨σ, mem_image_of_mem _ hσ, hM⟩, f, λ a, mem_Sup.2
    ⟨σ, mem_image_of_mem _ hσ, h1 a⟩, h2⟩,
end

lemma flexible_cond_Union (hc : is_chain (≤) c) (C : extended_index B) :
  (Sup (subtype.val '' c)).flexible_cond B C :=
begin
  obtain rfl | ⟨⟨σ, hσ₁⟩, hσ₂⟩ := c.eq_empty_or_nonempty,
  { refine spec.flexible_cond.co_large _ _;
    simp only [image_empty, Sup_empty, spec.domain_bot, spec.range_bot, mem_empty_eq,
      not_false_iff, and_true, coe_set_of, mk_flexible_litters] },
  by_cases h : ∃ (ρ : allowable_partial_perm B) (hρ : ρ ∈ c) (τ : allowable_partial_perm B)
    (hτ : τ ∈ c) L (hL : flexible L C),
    (((inr L.to_near_litter, C) ∉ ρ.val.domain ∧
      (inr L.to_near_litter, C) ∈ τ.val.domain) ∨
      ((inr L.to_near_litter, C) ∉ ρ.val.range ∧
      (inr L.to_near_litter, C) ∈ τ.val.range)) ∧ ρ ≤ τ,
  { obtain ⟨ρ, hρ, τ, hτ, L, hL, ⟨h, hρτ⟩⟩ := h,
    have H : ∀ L', flexible L' C →
        (⟨inr L'.to_near_litter, C⟩ : support_condition B) ∈ τ.val.domain ∧
        (⟨inr L'.to_near_litter, C⟩ : support_condition B) ∈ τ.val.range,
    { simp_rw [mem_domain, spec.mem_range] at h,
      obtain ⟨Hρ, ⟨⟨_ | ⟨N₁, N₂⟩, _⟩, hb₁, hb₂⟩⟩ | ⟨Hρ, ⟨⟨_ | ⟨N₁, N₂⟩, _⟩, hb₁, hb₂⟩⟩ := h;
      cases hb₂,
      { exact hρτ.all_flex_domain L N₂ C hL (λ Hρ', Hρ ⟨_, Hρ', rfl⟩) hb₁ },
      { exact hρτ.all_flex_range L N₁ C hL (λ Hρ', Hρ ⟨_, Hρ', rfl⟩) hb₁ } },
    refine spec.flexible_cond.all _ _;
    intros L' hL';
    obtain ⟨H₁, H₂⟩ := H L' hL';
    simp only [spec.domain_Sup, spec.range_Sup];
    exact mem_Union₂_of_mem (mem_image_of_mem _ hτ) ‹_› },
  push_neg at h,
  have := hσ₁.flexible_cond C,
  have H : ∀ (ρ : allowable_partial_perm B), ρ ∈ c → ∀ (τ : allowable_partial_perm B), τ ∈ c →
            ∀ (L : litter), flexible L C →
            ((inr L.to_near_litter, C) ∈ ρ.val.domain →
            (inr L.to_near_litter, C) ∈ τ.val.domain) ∧
            ((inr L.to_near_litter, C) ∈ ρ.val.range →
            (inr L.to_near_litter, C) ∈ τ.val.range),
  { intros ρ hρ τ hτ L hL,
    split;
    refine λ Hρ, of_not_not (λ Hτ, _),
    specialize h τ hτ ρ hρ L hL (or.inl ⟨Hτ, Hρ⟩), swap,
    specialize h τ hτ ρ hρ L hL (or.inr ⟨Hτ, Hρ⟩),
    all_goals
    { refine h ((hc hτ hρ _).elim id $ λ h₁, _),
      { rintro rfl,
        exact h le_rfl },
      { simp only [mem_domain, spec.mem_range] at Hρ Hτ,
        simp only [←image_domain, ←image_range] at Hρ Hτ,
        obtain ⟨b, hb₁, hb₂⟩ := Hρ,
        rw ←hb₂ at Hτ,
        cases Hτ (mem_image_of_mem _ $ h₁.1 hb₁) } } },
  obtain ⟨hdom, hrge⟩ | ⟨hdom, hrge⟩ := hσ₁.flexible_cond C,
  { refine spec.flexible_cond.co_large _ _,
    convert hdom using 3, swap, convert hrge using 3,
    all_goals
    { ext,
      rw [mem_set_of, mem_set_of, and.congr_right_iff],
      refine λ hx, ⟨λ hxc hxσ, hxc ⟨_, ⟨σ, Union_eq_true ⟨_, hσ₂, rfl⟩⟩, hxσ⟩, _⟩,
      rintro hxσ ⟨_, ⟨_, rfl⟩, ρ, ⟨⟨ρ, hρ₁, rfl⟩, rfl⟩, hρ₂⟩ },
    exact hxσ ((H ρ hρ₁ ⟨σ, hσ₁⟩ hσ₂ x hx).2 hρ₂),
    exact hxσ ((H ρ hρ₁ ⟨σ, hσ₁⟩ hσ₂ x hx).1 hρ₂), },
  { refine spec.flexible_cond.all (λ L hL, _) (λ L hL, _),
    { refine ⟨σ.domain, ⟨σ, Union_eq_true ⟨_, hσ₂, rfl⟩⟩, hdom L hL⟩, },
    { refine ⟨σ.range, ⟨σ, Union_eq_true ⟨_, hσ₂, rfl⟩⟩, hrge L hL⟩, } }
end

lemma non_flexible_cond_Union (hc : is_chain (≤) c) :
  (Sup $ subtype.val '' c).non_flexible_cond B :=
begin
  rintro β γ δ hγ hδ hγδ N A t hσ π hπ,
  rw mem_Sup at hσ,
  obtain ⟨_, ⟨σ, hσ₁, rfl⟩, hσ₂⟩ := hσ,
  exact σ.property.forward.non_flexible_cond hγ hδ hγδ N A t hσ₂ π (hπ.mono $ le_Sup ⟨σ, hσ₁, rfl⟩),
end

lemma domain_closed_Union (hc : is_chain (≤) c) :
  (Sup $ subtype.val '' c).domain.support_closed B :=
begin
  intros β γ δ hγ hδ hγδ A t h,
  simp_rw [spec.domain_Sup, mem_Union] at h,
  simp_rw [spec.domain_Sup, unary_spec.lower_Union],
  obtain ⟨_, ⟨σ, hσ₁, rfl⟩, hσ₂⟩ := h,
  refine (σ.prop.forward.support_closed hγ hδ hγδ A t hσ₂).mono _,
  convert @subset_bUnion_of_mem (unary_spec B) _ (spec.domain ∘ subtype.val '' c)
      (λ i, i.lower $ A.cons hγ) (spec.domain σ) _ using 1,
  { simp only [mem_image, Union_exists, bUnion_and', Union_Union_eq_right] },
  { exact ⟨σ, hσ₁, rfl⟩ }
end

variables (hc : is_chain (≤) c)

/-- The union of a chain of allowable partial permutations is allowable. -/
lemma allowable_Union : (Sup $ subtype.val '' c).allowable B :=
have c_inv_chain : is_chain (≤) (has_inv.inv '' c) := hc.image _ _ _ inv_mono,
have Union_rw : (Sup (subtype.val '' c))⁻¹ = Sup (subtype.val ''
  ((λ σ : allowable_partial_perm B, ⟨σ.val⁻¹, σ.2.inv⟩) '' c)) := begin
    rw Sup_inv, congr' 1, ext σ,
    simp only [allowable_inv, subtype.val_eq_coe, image_inv, set.mem_inv, mem_image, subtype.exists,
      subtype.coe_mk, exists_and_distrib_right, exists_eq_right, exists_prop,
      exists_eq_right_right],
    split,
    { rintro ⟨hσ, hσc⟩, exact ⟨hσ, ⟨σ⁻¹, allowable_inv.mpr hσ⟩, hσc, inv_inv σ⟩, },
    { rintro ⟨hσ, ρ, hρc, rfl⟩, simp_rw [inv_inv, subtype.coe_eta],
      exact ⟨allowable_inv.mpr ρ.property, hρc⟩, }
  end,
{ forward :=
  { one_to_one := one_to_one_Union hc,
    atom_cond := atom_cond_Union hc,
    near_litter_cond := near_litter_cond_Union hc,
    non_flexible_cond := non_flexible_cond_Union hc,
    support_closed := domain_closed_Union hc },
  backward :=
  { one_to_one := by { rw Union_rw, exact one_to_one_Union c_inv_chain },
    atom_cond := by { rw Union_rw, exact atom_cond_Union c_inv_chain },
    near_litter_cond := by { rw Union_rw, exact near_litter_cond_Union c_inv_chain },
    non_flexible_cond := by { rw Union_rw, exact non_flexible_cond_Union c_inv_chain },
    support_closed := by { rw Union_rw, exact domain_closed_Union c_inv_chain } },
  flexible_cond := flexible_cond_Union hc }

lemma le_Union₂ (σ τ : allowable_partial_perm B) (hτ : τ ∈ c) :
  τ ≤ ⟨Sup (subtype.val '' c), allowable_Union hc⟩ :=
begin
  have hsub : ∀ (t : allowable_partial_perm B) (ht : t ∈ c), t.val ≤ Sup (subtype.val '' c),
  { intros t ht b hb,
    exact ⟨t.val, ⟨t.val, Union_eq_true ⟨t, ht, rfl⟩⟩, hb⟩, },
  refine ⟨hsub τ hτ,
    λ L N A hLA hnin hin, _,
    λ L N A hLA hnin hin, _,
    λ a b L h A hnin hin p hp, _,
    λ a b L h A hnin hin p hp, _⟩,
  all_goals
  { obtain ⟨_, ⟨_, rfl⟩, _, ⟨⟨ρ, hρc, rfl⟩, rfl⟩, hLρ⟩ := hin,
    have hneq : ρ ≠ τ,
    { rintro rfl, exact hnin hLρ, },
    obtain ⟨hsub, -, -, -⟩ | hleq := hc hρc hτ hneq,
    { cases hnin (hsub hLρ) } },
  { intros l hla,
    have := hleq.2 L N A hLA hnin hLρ l hla,
    refine ⟨⟨_, ⟨ρ, set.ext $ λ x, ⟨_, _⟩⟩, this.1⟩, ⟨_, ⟨ρ, set.ext $ λ x, ⟨_, _⟩⟩, this.2⟩⟩,
    { rintro ⟨_, ⟨_, rfl⟩, hx⟩, exact hx },
    { rintro hx, exact ⟨_, ⟨⟨_, hρc, rfl⟩, rfl⟩, hx⟩ },
    { rintro ⟨_, ⟨_, rfl⟩, hx⟩, exact hx },
    { rintro hx, exact ⟨_, ⟨⟨_, hρc, rfl⟩, rfl⟩, hx⟩ } },
  { intros l hla,
    have := hleq.3 L N A hLA hnin hLρ l hla,
    refine ⟨⟨_, ⟨ρ, set.ext $ λ x, ⟨_, _⟩⟩, this.1⟩, ⟨_, ⟨ρ, set.ext $ λ x, ⟨_, _⟩⟩, this.2⟩⟩,
    { rintro ⟨_, ⟨_, rfl⟩, hx⟩, exact hx },
    { rintro hx, exact ⟨_, ⟨⟨_, hρc, rfl⟩, rfl⟩, hx⟩ },
    { rintro ⟨_, ⟨_, rfl⟩, hx⟩, exact hx },
    { rintro hx, exact ⟨_, ⟨⟨_, hρc, rfl⟩, rfl⟩, hx⟩ } },
  { obtain ⟨q, hq⟩ := hleq.4 a b L h A hnin hLρ p hp,
    exact ⟨q, (hsub ρ hρc) hq⟩ },
  { obtain ⟨q, hq⟩ := hleq.5 a b L h A hnin hLρ p hp,
    exact ⟨q, (hsub ρ hρc) hq⟩ }
end

lemma le_Union₁ (hcne : c.nonempty) (σ : allowable_partial_perm B)
  (hc₁ : c ⊆ {ρ : allowable_partial_perm B | σ ≤ ρ}) :
  σ ≤ ⟨Sup (subtype.val '' c), allowable_Union hc⟩ :=
let ⟨τ, h⟩ := hcne in (set_of_app_iff.1 $ mem_def.1 $ hc₁ h).trans (le_Union₂ hc σ τ h)

end zorn_setup

/-- There is a maximal allowable partial permutation extending any given allowable partial
permutation. This result is due to Zorn's lemma. -/
lemma maximal_perm (σ : allowable_partial_perm B) :
  ∃ (m : allowable_partial_perm B) (H : m ∈ {ρ : allowable_partial_perm B | σ ≤ ρ}), σ ≤ m ∧
    ∀ (z : allowable_partial_perm B), z ∈ {ρ : allowable_partial_perm B | σ ≤ ρ} →
    m ≤ z → z ≤ m :=
zorn_nonempty_preorder₀ {ρ | σ ≤ ρ}
  (λ c hc₁ hc₂ τ hτ,
    ⟨⟨Sup (subtype.val '' c), allowable_Union hc₂⟩,
      le_Union₁ hc₂ ⟨τ, hτ⟩ σ hc₁,
      λ τ, le_Union₂ hc₂ σ τ⟩)
  σ (le_refl σ)

end allowable_partial_perm
end con_nf
