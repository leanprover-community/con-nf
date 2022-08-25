import phase2.freedom_of_action.constrains
import phase2.freedom_of_action.values
import phase2.freedom_of_action.zorn

/-!
# Maximality proof: Flexible litter case

When we want to add an `A`-flexible litter to `σ`, we will just add all of them in an arbitrary
bijection. This will always exist because the sets are both of size `μ`. This will create a
*rough bijection*. This is not necessarily compatible with `σ`, because we may already have
specified where certain atoms in these litters are mapped to or from.

To remedy this, for each `A`-flexible litter we create a *precise atom bijection* mapping all of the
unassigned atoms in the domain of `σ` to all of the unassigned atoms in the range of `σ` in the
litter obtained under the rough bijection.

We extend `σ` by saying that each `A`-flexible litter is mapped to the image of the precise atom
bijection map, together with the image of all of the atoms that were already specified. This is a
near-litter, which is near to the litter obtained using the rough bijection. The same procedure is
done in the reverse direction with the same bijections, so that all of the `A`-flexible litters are
now defined in this new allowable partial permutation.
-/

open cardinal set sum
open_locale cardinal

universe u

namespace con_nf
namespace allowable_spec

variables [params.{u}]

open struct_perm spec

variables {α : Λ} [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [typed_positions.{}] [phase_2_assumptions α] {B : le_index α}

variables {B} (A : extended_index B) {σ : allowable_spec B} {dom rge : unary_spec B}

/-- A bijection of the remaining `A`-flexible litters in an allowable partial permutation `σ`.
This is a bijection of *rough images*; we have to then take into account all of the exceptions that
have already been established in `σ`. -/
abbreviation rough_bijection (dom rge : unary_spec B) :=
{L : litter // flex L A ∧ (inr L.to_near_litter, A) ∉ dom} ≃
{L : litter // flex L A ∧ (inr L.to_near_litter, A) ∉ rge}

variables {A}

/-- The inverse of a rough bijection, phrased as moving from `σ` to `σ⁻¹`. -/
def rough_bijection.inv (bij : rough_bijection A σ.val.domain σ.val.range) :
  rough_bijection A σ⁻¹.val.domain σ⁻¹.val.range :=
bij.symm

@[simp] lemma rough_bijection.inv_symm (bij : rough_bijection A σ.val.domain σ.val.range) :
  bij.inv.symm = bij := by ext; refl

@[simp] lemma rough_bijection.inv_inv (bij : rough_bijection A σ.val.domain σ.val.range) :
  bij.inv.inv = bij := by ext; refl

lemma rough_bijection.inv_coe (bij : rough_bijection A σ.val.domain σ.val.range)
  (L : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}) :
  bij.inv (bij L) = L :=
equiv.symm_apply_apply _ _

lemma rough_bijection.inv_to_fun (bij : rough_bijection A σ.val.domain σ.val.range)
  (L : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}) :
  bij.inv (bij.to_fun L) = L :=
equiv.symm_apply_apply _ _

lemma rough_bijection.inv_fun_inv_fun (bij : rough_bijection A σ.val.domain σ.val.range)
  (L : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}) :
  bij.inv_fun (bij.inv.inv_fun L) = L :=
equiv.symm_apply_apply _ _

lemma small_of_not_mem_spec
  (L : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}) :
  small {a ∈ litter_set L | (inl a, A) ∈ σ.val.domain} :=
begin
  obtain ⟨N, h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N, hN, h₁, h₂⟩ := σ.property.forward.atom_cond L A,
  { cases L.property.2 (inr_mem_domain h₁) },
  { exact h₂ },
  { exact h₁ },
end

lemma small_of_rough_bijection (bij : rough_bijection A σ.val.domain σ.val.range)
  (L : {L : litter // flex L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}) :
  small {a ∈ litter_set (bij L) | (inl a, A) ∈ σ.val.range} :=
begin
  obtain ⟨N, h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N, hN, h₁, h₂⟩ := σ.property.backward.atom_cond
    (bij L) A,
  { exfalso, rw spec.inr_mem_inv at h₁,
    obtain ⟨hC, hn⟩ := (bij L).property, exact hn (inr_mem_range h₁) },
  { rw spec.domain_inv at h₂, exact h₂ },
  { rw spec.domain_inv at h₁, exact h₁ }
end

namespace rough_bijection

/-- Suppose a flexible litter `L` is mapped to another flexible litter `L₁` under the rough
bijection defined above. We construct a bijection between the atoms not yet specified in `L` and
`L₁`. This yields a precise near-litter image of each flexible litter `L`.
`L₂` is supposed to be `(bij L₁)`. -/
def precise_atom_bijection
  (L₁ : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ dom})
  (L₂ : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ rge}) :=
↥{a ∈ litter_set L₁ | (inl a, A) ∉ dom} ≃
  ↥{a ∈ litter_set L₂ | (inl a, A) ∉ rge}

namespace precise_atom_bijection

def inv {σ : allowable_spec B} {bij : rough_bijection A σ.val.domain σ.val.range}
  {L : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ σ.val.range}}
  (abij : precise_atom_bijection (bij.inv_fun L) L) :
    precise_atom_bijection L (bij.inv_fun L) :=
equiv.symm abij

end precise_atom_bijection

/-- If the image of this atom has already been specified by `σ`, return the value that was already
given. Otherwise, return the image generated by `precise_image_bijection`. -/
noncomputable def precise_atom_image {dom rge} (bij : rough_bijection A dom rge)
  {L : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ dom}}
  {L' : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ rge}}
  (abij : precise_atom_bijection L L')
  (atom_value : {a : litter_set L // (inl a.val, A) ∈ dom} → atom)
  (a : atom) (ha : a ∈ litter_set L) : atom :=
@dite _ ((inl a, A) ∈ dom) (classical.dec _)
  (λ h, atom_value ⟨⟨a, ha⟩, h⟩)
  (λ h, abij.to_fun ⟨a, ha, h⟩)

lemma precise_atom_image_range {dom rge} (bij : rough_bijection A dom rge)
  {L : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ dom}}
  {L' : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ rge}}
  (abij : precise_atom_bijection L L')
  (atom_value : {a : litter_set L // (inl a.val, A) ∈ dom} → atom) :
  range (λ a : litter_set L, precise_atom_image bij abij atom_value a a.property) =
    (litter_set L' ∩ {a | (inl a, A) ∉ rge}) ∪ range atom_value :=
begin
  unfold precise_atom_image,
  ext a,
  split,
  { rintro ⟨b, hb⟩, dsimp only at hb,
    split_ifs at hb,
    { simp_rw subtype.coe_eta at hb, exact or.inr ⟨⟨b, h⟩, hb⟩ },
    { rw ← hb,
      exact or.inl (abij.to_fun ⟨b, _⟩).property } },
  rintro (⟨ha₁, ha₂⟩ | ⟨b, hb⟩),
  { rw mem_set_of at ha₂,
    set b := abij.inv_fun ⟨a, ha₁, ha₂⟩ with hb,
    refine ⟨⟨b, b.property.left⟩, _⟩,
    dsimp only,
    split_ifs,
    { cases b.property.right h },
    { simp only [hb, equiv.inv_fun_as_coe, subtype.coe_mk,
        subtype.coe_eta, equiv.to_fun_as_coe, equiv.apply_symm_apply] } },
  { refine ⟨b, _⟩,
    dsimp only,
    split_ifs,
    { simp_rw subtype.coe_eta, exact hb },
    { cases h b.property } }
end

/-- The precise image of a flexible litter under the new allowable permutation. -/
def precise_litter_image (bij : rough_bijection A σ.val.domain σ.val.range)
  (L : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain})
  (abij : precise_atom_bijection L (bij L)) : near_litter :=
⟨(bij L),
  range (λ (a : litter_set L),
    precise_atom_image bij abij (λ a, atom_value σ A a.1 a.2) a a.property),
  begin
    rw precise_atom_image_range,
    unfold is_near_litter is_near small symm_diff,
    refine (mk_union_le _ _).trans_lt (add_lt_of_lt κ_regular.aleph_0_le _ _),
    { rw [← sup_eq_union, sdiff_sup, ← inf_eq_inter, sdiff_inf_self_left],
      refine lt_of_le_of_lt (mk_le_mk_of_subset $ inter_subset_left _ _) _,
      convert small_of_rough_bijection bij L,
      ext a,
      split,
      { rintro ⟨ha₁, ha₂⟩, simp only [mem_set_of_eq, not_not_mem] at ha₂, exact ⟨ha₁, ha₂⟩ },
      { rintro ⟨ha₁, ha₂⟩, exact ⟨ha₁, function.eval ha₂⟩ } },
    { rw [← sup_eq_union, sup_sdiff, ← inf_eq_inter, inf_sdiff, sdiff_self, bot_inf_eq, bot_sup_eq],
      refine ((mk_le_mk_of_subset $ diff_subset _ _).trans mk_range_le).trans_lt _,
      convert small_of_not_mem_spec L using 1,
      rw mk_sep,
      refl }
end⟩

lemma precise_litter_image_not_mem (bij : rough_bijection A σ.val.domain σ.val.range)
  (L : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain})
  (abij : precise_atom_bijection L (bij L)) :
  (inr (precise_litter_image bij L abij), A) ∉ σ.val.range :=
begin
  intro h, rw spec.mem_range at h, obtain ⟨⟨_ | ⟨N, _⟩, C⟩, hc₁, hc₂⟩ := h; cases hc₂, clear hc₂,
  obtain ⟨M, hM₁, _⟩ :=
    σ.property.backward.near_litter_cond _ _ A hc₁,
  cases (bij L).prop.2 (inr_mem_domain hM₁),
end

lemma precise_litter_image_eq_symm
  {bij : rough_bijection A σ.val.domain σ.val.range}
  {abij : Π L, precise_atom_bijection L (bij L)}
  {abij' : Π L, precise_atom_bijection (bij.inv L) L}
  (habij : ∀ L a, (equiv.symm (abij' (bij L)) a).val = (equiv.symm (abij L) a).val)
  {L₁ : ↥{L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}}
  {L₂ : ↥{L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ σ.val.range}} :
  bij.precise_litter_image L₁ (abij L₁) = L₂.val.to_near_litter →
  L₁.val.to_near_litter = bij.inv.precise_litter_image L₂ (equiv.symm $ abij' L₂) :=
begin
  intro h,
  have : L₂ = bij L₁,
  { have := congr_arg sigma.fst h,
    unfold precise_litter_image at this,
    simp only [litter.to_near_litter, subtype.val_eq_coe, subtype.coe_inj] at this,
    exact this.symm, },
  subst this,
  rw ← near_litter.val_injective.eq_iff at h ⊢,
  rw [precise_litter_image] at h ⊢,
  dsimp only [litter.to_near_litter] at h ⊢,
  symmetry, rw range_eq_iff at h ⊢, obtain ⟨h₁, h₂⟩ := h, split,
  { intro a,
    obtain ⟨c, hc⟩ := h₂ a a.prop,
    simp_rw ← hc, convert c.prop using 1,
    unfold precise_atom_image,
    classical,
    by_cases (inl (c : atom), A) ∈ σ.val.domain,
    { simp_rw dif_pos h,
      rw dif_pos,
      { refine atom_value_eq_of_mem _,
        exact atom_value_spec _ _ _ _, },
      { exact atom_value_spec_range _ _ _ _, } },
    { simp_rw dif_neg h,
      rw dif_neg,
      { rw subtype.coe_eta,
        rw equiv.to_fun_as_coe,
        rw equiv.to_fun_as_coe,
        have := subtype.coe_inj.mpr (equiv.symm_apply_apply (abij L₁) ⟨c, c.2, h⟩),
        rw subtype.coe_mk at this, convert this using 1, exact habij _ _, },
      { exact ((abij L₁).to_fun ⟨c, c.2, h⟩).property.2, } } },
  { intros b hb,
    have := h₁ ⟨b, hb⟩,
    refine ⟨⟨_, this⟩, _⟩,
    unfold precise_atom_image,
    classical,
    by_cases (inl b, A) ∈ σ.val.domain,
    { simp_rw subtype.coe_mk, simp_rw dif_pos h,
      rw dif_pos,
      { refine atom_value_eq_of_mem _,
        exact atom_value_spec _ _ _ _, },
      { exact atom_value_spec_range _ _ _ _, } },
    { simp_rw subtype.coe_mk, simp_rw dif_neg h,
      rw dif_neg,
      { rw subtype.coe_eta,
        rw equiv.to_fun_as_coe,
        rw equiv.to_fun_as_coe,
        have := subtype.coe_inj.mpr (equiv.symm_apply_apply (abij L₁) ⟨b, hb, h⟩),
        rw subtype.coe_mk at this, convert this using 1, exact habij _ _, },
      { exact ((abij L₁).to_fun ⟨b, hb, h⟩).property.2, } } }
end

lemma precise_litter_image_inj {bij : rough_bijection A σ.val.domain σ.val.range}
  {L₁ L₂ : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}}
  (abij₁ : precise_atom_bijection L₁ (bij L₁))
  (abij₂ : precise_atom_bijection L₂ (bij L₂)) :
  precise_litter_image bij L₁ abij₁ = precise_litter_image bij L₂ abij₂ → L₁ = L₂ :=
begin
  intro h,
  unfold precise_litter_image at h,
  have := congr_arg sigma.fst h,
  rw [subtype.coe_inj, embedding_like.apply_eq_iff_eq] at this,
  exact this,
end

def new_flex_litters (bij : rough_bijection A σ.val.domain σ.val.range)
  (abij : ∀ L, precise_atom_bijection L (bij L)) : spec B := {
  carrier := {c | ∃ (L : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}),
    c = (inr (L.1.to_near_litter, precise_litter_image bij L (abij L)), A)},
  domain := {c | ∃ (L : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}),
    c = (inr L.1.to_near_litter, A)},
  range := {c | ∃ (L : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}),
    c = (inr (precise_litter_image bij L (abij L)), A)},
  image_domain' := begin
    ext c, simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and, mem_set_of_eq,
      set_coe.exists, subtype.coe_mk, mem_image, exists_prop],
    split,
    { rintro ⟨d, ⟨L, ⟨hL₁, hL₂⟩, rfl⟩, rfl⟩, exact ⟨L, ⟨hL₁, hL₂⟩, rfl⟩, },
    { rintro ⟨L, ⟨hL₁, hL₂⟩, rfl⟩, exact ⟨_, ⟨L, ⟨hL₁, hL₂⟩, rfl⟩, rfl⟩, },
  end,
  image_range' := begin
    ext c, simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and, mem_set_of_eq,
      set_coe.exists, subtype.coe_mk, mem_image],
    split,
    { rintro ⟨d, ⟨L, ⟨hL₁, hL₂⟩, rfl⟩, rfl⟩, exact ⟨L, ⟨hL₁, hL₂⟩, rfl⟩, },
    { rintro ⟨L, ⟨hL₁, hL₂⟩, rfl⟩, exact ⟨_, ⟨L, ⟨hL₁, hL₂⟩, rfl⟩, rfl⟩, },
  end,
}

def new_inverse_flex_litters (bij : rough_bijection A σ.val.domain σ.val.range)
  (abij' : ∀ L, precise_atom_bijection (bij.inv L) L) : spec B :=
(new_flex_litters bij.inv (λ L, equiv.symm (abij' L)))⁻¹

@[simp] lemma mem_new_flex_litters (bij : rough_bijection A σ.val.domain σ.val.range)
  (abij : ∀ L, precise_atom_bijection L (bij L)) (c : binary_condition B) :
  c ∈ new_flex_litters bij abij ↔
  ∃ (L : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}),
    c = (inr (L.1.to_near_litter, precise_litter_image bij L (abij L)), A) :=
iff.rfl

@[simp] lemma mem_new_inverse_flex_litters (bij : rough_bijection A σ.val.domain σ.val.range)
  (abij' : ∀ L, precise_atom_bijection (bij.inv L) L) (c : binary_condition B) :
  c ∈ new_inverse_flex_litters bij abij' ↔
  ∃ (L : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ σ.val.range}),
    c = (inr (precise_litter_image bij.inv L (equiv.symm $ abij' L), L.1.to_near_litter), A) :=
begin
  unfold new_inverse_flex_litters new_flex_litters,
  split,
  { rintro ⟨L, hL⟩, refine ⟨L, _⟩, rw inv_eq_iff_inv_eq at hL, rw ← hL, refl, },
  { rintro ⟨L, hL⟩, refine ⟨L, _⟩, rw hL, refl, },
end

lemma precise_litter_image_flex (bij : rough_bijection A σ.val.domain σ.val.range)
  (L : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain})
  (abij : precise_atom_bijection L (bij L)) :
  flex (precise_litter_image bij L abij).1 A :=
(bij L).property.1

end rough_bijection

open rough_bijection

variables (bij : rough_bijection A σ.val.domain σ.val.range)
  (abij : ∀ L, precise_atom_bijection L (bij L))
  (abij' : ∀ L, precise_atom_bijection (bij.inv L) L)

lemma flex_union_one_to_one
  (habij : ∀ L a, (equiv.symm (abij' (bij L)) a).val = (equiv.symm (abij L) a).val) :
  spec.one_to_one_forward
    (σ.val ⊔ bij.new_flex_litters abij ⊔ bij.new_inverse_flex_litters abij') :=
begin
  refine λ C, ⟨_, _⟩,
  { rintro b a₁ ((ha₁ | ha₁) | ha₁) a₂ ha₂,
    { obtain ((ha₂ | ha₂) | ha₂) := ha₂,
      { exact (σ.property.forward.one_to_one C).atom b ha₁ ha₂ },
      { simpa only [new_flex_litters, mem_set_of_eq, prod.mk.inj_iff, false_and,
          exists_false, and_false, coe_mk] using ha₂ },
      { simpa only [set_like.mem_coe, mem_new_inverse_flex_litters, prod.mk.inj_iff,
          false_and, exists_false] using ha₂ } },
    { simpa only [new_flex_litters, mem_set_of_eq, prod.mk.inj_iff, false_and,
        exists_false, and_false, coe_mk] using ha₁ },
    { simpa only [set_like.mem_coe, mem_new_inverse_flex_litters, prod.mk.inj_iff,
          false_and, exists_false] using ha₁ } },
  rintro N M₁ ((hM₁ | hM₁) | hM₁) M₂ ((hM₂ | hM₂) | hM₂),
  { exact (σ.property.forward.one_to_one C).near_litter N hM₁ hM₂ },
  { obtain ⟨N', hN'₁, hN'₂⟩ := σ.property.backward.near_litter_cond _ _ C hM₁,
    obtain ⟨L', hL'⟩ := hM₂, cases hL',
    cases (bij L').property.right (inr_mem_domain hN'₁), },
  { obtain ⟨L', hL'⟩ := hM₂, cases hL',
    cases L'.property.right (inr_mem_range hM₁), },
  { obtain ⟨L, hL⟩ := hM₁,cases hL,
    have := precise_litter_image_not_mem bij L (abij L), rw spec.mem_range at this,
    cases this ⟨_, hM₂, rfl⟩, },
  { obtain ⟨L₁, hL₁⟩ := hM₁, obtain ⟨L₂, hL₂⟩ := hM₂,
    cases precise_litter_image_inj _ _
      ((prod.ext_iff.1 $ inr_injective (prod.ext_iff.1 hL₁).1).2.symm.trans
        (prod.ext_iff.1 $ inr_injective (prod.ext_iff.1 hL₂).1).2),
    cases hL₁, cases hL₂, refl },
  { obtain ⟨L₁, hL₁⟩ := hM₁, obtain ⟨L₂, hL₂⟩ := hM₂,
    simp only [binary_condition.inv_def, map_inr, prod.swap_prod_mk, subtype.val_eq_coe,
      prod.mk.inj_iff] at hL₂,
    cases hL₁, cases hL₂.1.2,
    exact precise_litter_image_eq_symm habij hL₂.1.1, },
  { obtain ⟨L₁, hL₁⟩ := hM₁, cases hL₁,
    have := L₁.prop.2, simp_rw [allowable_spec.val_inv, domain_inv, spec.mem_range] at this,
    cases this ⟨_, hM₂, rfl⟩, },
  { obtain ⟨L₁, hL₁⟩ := hM₁, obtain ⟨L₂, hL₂⟩ := hM₂,
    rw [prod.mk.inj_iff, sum.inr.inj_iff, prod.mk.inj_iff] at hL₂, cases hL₁, cases hL₂.1.1,
    exact (precise_litter_image_eq_symm habij hL₂.1.2.symm).symm, },
  { obtain ⟨L₁, hL₁⟩ := hM₁, obtain ⟨L₂, hL₂⟩ := hM₂,
    unfold precise_litter_image at hL₁ hL₂,
    have := precise_litter_image_inj (abij' L₁).symm (abij' L₂).symm _,
    cases this, cases hL₁, cases hL₂, refl,
    have := litter.to_near_litter_injective
      ((prod.ext_iff.1 $ inr_injective (prod.ext_iff.1 hL₁).1).1.symm.trans
        (prod.ext_iff.1 $ inr_injective (prod.ext_iff.1 hL₂).1).1),
    rw subtype.val_inj at this,
    cases this, refl, }
end

lemma flex_union_atoms_eq (L : litter) (C : extended_index B) :
  {a ∈ litter_set L | (inl a, C) ∈
    (σ.val ⊔ bij.new_flex_litters abij ⊔ bij.new_inverse_flex_litters abij').domain} =
  {a ∈ litter_set L | (inl a, C) ∈ σ.val.domain} :=
begin
  ext a,
  simp only [spec.domain_sup, new_flex_litters, new_inverse_flex_litters,
    subtype.val_eq_coe, mem_set_of_eq, set_coe.exists, subtype.coe_mk, equiv.to_fun_as_coe,
    mem_union_eq, mem_sep_iff],
  refine and_congr_right (λ ha, ⟨_, λ h, or.inl $ or.inl h⟩),
  rintro ((h | ⟨L, hL, hc⟩) | ⟨L, hL, hc⟩),
  { exact h, },
  { cases hc, },
  { cases hc, },
end

lemma flex_union_atom_cond (L C) :
  spec.atom_cond
    (σ.val ⊔ bij.new_flex_litters abij ⊔ bij.new_inverse_flex_litters abij') L C :=
begin
  obtain ⟨N, h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N, hN, h₁, h₂⟩ := σ.prop.forward.atom_cond L C,
  { exact spec.atom_cond.all N
      (or.inl $ or.inl h₁) atom_map (λ a H, or.inl $ or.inl $ h₂ a H) h₃ },
  { obtain rfl | h := eq_or_ne A C,
    { by_cases flex L A,
      { refine spec.atom_cond.small_in _ (or.inl $ or.inr ⟨⟨L, h, h₁⟩, rfl⟩) _ _,
        { rwa flex_union_atoms_eq },
        rintro a b ((hab | ⟨L', ⟨⟩⟩) | ⟨L', ⟨⟩⟩),
        split,
        { intro ha, refine ⟨⟨a, ha⟩, _⟩,
          unfold precise_atom_image,
          rw dif_pos _,
          exact atom_value_eq_of_mem hab,
          exact inl_mem_domain hab, },
        { rintro ⟨c, hbc⟩, unfold precise_atom_image at hbc, dsimp only at hbc,
          split_ifs at hbc with hc,
          { have := atom_value_spec _ _ _ hc, simp_rw subtype.coe_mk at hbc, rw hbc at this,
            rw (σ.property.forward.one_to_one A).atom b hab this,
            exact c.property, },
          { have := ((abij ⟨L, h, h₁⟩).to_fun ⟨c, c.property, hc⟩).prop,
            rw hbc at this,
            cases this.2 (inl_mem_range hab), } } },
      refine spec.atom_cond.small_out _ (by rwa flex_union_atoms_eq),
      contrapose! h₁, rw [spec.domain_sup, spec.domain_sup] at h₁,
      obtain ((_ | _) | _) := h₁,
      { exact h₁ },
      { rw mem_domain at h₁, obtain ⟨_, ⟨L', rfl⟩, h₁⟩ := h₁, cases h₁, cases h L'.2.1 },
      rw mem_domain at h₁,
      obtain ⟨⟨as | ⟨_, N⟩, C⟩, ⟨L', hL'⟩, h'⟩ := h₁; cases hL',
      simp only [subtype.val_eq_coe, binary_condition.domain_mk, map_inr,
        prod.mk.inj_iff, eq_self_iff_true, and_true] at h',
      cases (congr_arg sigma.fst h').symm,
      cases h (bij.inv L').2.1, },
    { refine spec.atom_cond.small_out _ _,
      { contrapose! h₁, rw [spec.domain_sup, spec.domain_sup] at h₁,
        obtain ((_ | _) | _) := h₁,
        { exact h₁ },
        { obtain ⟨_, ⟨L', rfl⟩, ⟨⟩⟩ := h₁, cases h rfl },
        { rw mem_domain at h₁, obtain ⟨⟨as | ⟨_, N⟩, C⟩, ⟨L', hL'⟩, h'⟩ := h₁; cases hL',
          simp only [subtype.val_eq_coe, binary_condition.domain_mk, map_inr,
            prod.mk.inj_iff] at h', cases h'.2, cases h rfl } },
      rw flex_union_atoms_eq, exact h₂, } },
  { refine spec.atom_cond.small_in N (or.inl $ or.inl hN) _ _,
    { rw flex_union_atoms_eq, exact h₁ },
    rintro a b ((hab | ⟨L', ⟨⟩⟩) | ⟨L', ⟨⟩⟩),
    exact h₂ hab }
end

lemma mem_domain_of_mem_symm_diff
  (L : {L : litter | flex L A ∧ (inr L.to_near_litter, A) ∉ σ.val.range})
  (a : atom)
  (ha : a ∈ litter_set (bij.inv L) ∆ (bij.inv.precise_litter_image L (equiv.symm (abij' L))).snd) :
  (inl a, A) ∈ σ.val.domain :=
begin
  rw precise_litter_image at ha,
  simp only at ha,
  rw subtype.coe_mk at ha,
  simp_rw precise_atom_image at ha,
  by_contradiction,
  obtain ⟨ha₁, ha₂⟩ | ⟨ha₁, ha₂⟩ := ha,
  { rw set.mem_range at ha₂, push_neg at ha₂,
    have := ha₂ ⟨((abij' L).to_fun ⟨a, ha₁, h⟩).val, ((abij' L).to_fun ⟨a, ha₁, h⟩).property.1⟩,
    classical,
    rw dif_neg at this,
    { refine this _,
      generalize_proofs,
      simp only [subtype.coe_mk, equiv.to_fun_as_coe, subtype.val_eq_coe, subtype.coe_eta,
        equiv.symm_apply_apply], },
    exact ((abij' L).to_fun ⟨a, ha₁, h⟩).property.2, },
  { obtain ⟨b, hb⟩ := ha₁,
    dsimp only at hb,
    split_ifs at hb with h' h',
    { have := atom_value_spec σ⁻¹ A b h',
      simp_rw subtype.coe_mk at hb, rw hb at this,
      rw mem_domain at h,
      exact h ⟨_, this, rfl⟩, },
    { rw ← hb at ha₂,
      cases ha₂ ((abij' L).symm ⟨b, b.2, h'⟩).property.1, } },
end

lemma flex_union_near_litter_cond :
  ∀ N₁ N₂ C, spec.near_litter_cond
    (σ.val ⊔ bij.new_flex_litters abij ⊔ bij.new_inverse_flex_litters abij') N₁ N₂ C :=
begin
  rintros N₁ N₂ C ((h | h) | h),
  { obtain ⟨M, hM, s, hs₁, hs₂⟩ := σ.property.forward.near_litter_cond N₁ N₂ C h,
    exact ⟨M, (or.inl (or.inl hM)), s, λ h, or.inl (or.inl $ hs₁ h), hs₂⟩, },
  { rw [set_like.mem_coe, mem_new_flex_litters] at h,
    obtain ⟨L, hL⟩ := h,
    refine ⟨N₂, or.inl (or.inr _), _⟩,
    { rw [set_like.mem_coe, mem_new_flex_litters],
      cases hL, exact ⟨_, rfl⟩, },
    refine ⟨λ a, arbitrary atom, _, _⟩,
    { rintro ⟨a, ha⟩, cases hL,
      simpa only [subtype.coe_mk, symm_diff_self, bot_eq_empty, mem_empty_eq] using ha, },
    { symmetry, rw symm_diff_eq_left, rw bot_eq_empty, rw set.range_eq_empty_iff,
      split, rintro ⟨a, ha⟩, cases hL,
      simpa only [subtype.coe_mk, symm_diff_self, bot_eq_empty, mem_empty_eq] using ha, } },
  { rw [set_like.mem_coe, mem_new_inverse_flex_litters] at h,
    obtain ⟨L, hL⟩ := h,
    refine ⟨bij.precise_litter_image (bij.inv L) (abij (bij.inv L)), _, _⟩,
    { refine or.inl (or.inr _),
      rw [set_like.mem_coe, mem_new_flex_litters],
      refine ⟨bij.inv L, _⟩, cases hL, refl, },
    refine ⟨λ a, atom_value σ A a _, _, _⟩,
    { cases hL, exact mem_domain_of_mem_symm_diff bij abij' L a a.2, },
    { intro a, cases hL, refine or.inl (or.inl $ atom_value_spec σ A a _), },
    { simp only [subtype.val_eq_coe, prod.mk.inj_iff] at hL,
      sorry } }
end

-- lemma unpack_coh_cond ⦃β : Λ⦄
--   ⦃γ : type_index⦄
--   ⦃δ : Λ⦄
--   (hγβ : γ < ↑β)
--   (hδβ : δ < β)
--   (hδγ : γ ≠ ↑δ)
--   (p : path ↑B ↑β)
--   (t : tangle_path ↑(lt_index.mk' hγβ (B.path.comp p)))
--   (π : allowable_path B) :
--   derivative ((p.cons $ coe_lt_coe.mpr hδβ).cons (bot_lt_coe _)) π.to_struct_perm •
--       (f_map_path hγβ hδβ t).to_near_litter =
--     (f_map_path hγβ hδβ $ (π.derivative_comp B p).derivative hγβ
--       {index := ↑β, path := B.path.comp p} • t).to_near_litter :=
-- begin
--   sorry,
-- end

lemma flex_union_non_flex_cond :
  spec.non_flex_cond B
    (σ.val ⊔ bij.new_flex_litters abij ⊔ bij.new_inverse_flex_litters abij') :=
begin
  unfold spec.non_flex_cond,
  intros β γ δ hγ hδ hγδ N C t hf π hπ,
  unfold struct_perm.satisfies struct_perm.satisfies_cond at hπ,
  have h := hπ hf,
  dsimp only [sum.elim_inr] at h,
  rw ← h,
  rw ← smul_f_map_path (B.path.comp C) hγ hδ hγδ _ t,
  convert near_litter_perm.smul_to_near_litter_eq _ _ using 1,
  unfold to_near_litter_perm,
  simp only [lower_self, monoid_hom.comp_id, allowable_path.to_struct_perm_derivative_comp,
    mul_equiv.coe_to_monoid_hom, coe_to_bot_iso_symm, of_bot_smul],
  rw [← allowable_path.to_struct_perm_derivative_comp, allowable_path.smul_to_struct_perm,
    allowable_path.derivative_comp, allowable_path.derivative_comp,
    allowable_path.smul_derivative_bot],
end

lemma flex_union_support_closed :
  (σ.val ⊔ bij.new_flex_litters abij ⊔ bij.new_inverse_flex_litters abij')
    .domain.support_closed B :=
begin
  unfold unary_spec.support_closed,
  rintros β γ δ hγ hδ hγδ C t ht π hsupp,
  rw [domain_sup, domain_sup] at ht hsupp,
  obtain ((ht | ht) | ht) := ht,
  { refine σ.property.forward.support_closed hγ hδ hγδ C t ht _ _,
    intros a ha, exact hsupp (or.inl (or.inl ha)), },
  { exfalso,
    simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and, mem_set_of_eq,
      mem_new_flex_litters, set_coe.exists, subtype.coe_mk] at ht,
    obtain ⟨c, ⟨L, ⟨hL₁, hL₂⟩, rfl⟩, hc⟩ := ht,
    simp only [binary_condition.domain_mk, map_inr, prod.mk.inj_iff,
      litter.to_near_litter_injective.eq_iff] at hc,
    refine hL₁ hγ hδ hγδ C hc.2 t hc.1, },
  { exfalso,
    simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and, mem_set_of_eq,
      mem_new_inverse_flex_litters, set_coe.exists, subtype.coe_mk] at ht,
    obtain ⟨c, ⟨L, ⟨hL₁, hL₂⟩, rfl⟩, hc⟩ := ht,
    simp only [binary_condition.domain_mk, map_inr, prod.mk.inj_iff] at hc,
    have h := precise_litter_image_flex bij.inv ⟨L, hL₁, hL₂⟩ (abij' ⟨L, hL₁, hL₂⟩).symm,
    refine h hγ hδ hγδ C hc.2 t (congr_arg sigma.fst hc.1), },
end

lemma flex_union_flex_cond (C) :
  spec.flex_cond B
    (σ.val ⊔ bij.new_flex_litters abij ⊔ bij.new_inverse_flex_litters abij') C :=
begin
  obtain rfl | h := eq_or_ne C A,
  { refine spec.flex_cond.all (λ L hL, _) (λ L hL, _),
    { by_cases h : ((inr L.to_near_litter, C) ∈ σ.val.domain);
        rw [spec.domain_sup, spec.domain_sup, mem_union, mem_union]; left,
      { left, exact h },
      exact or.inr ⟨⟨L, hL, h⟩, rfl⟩, },
    { -- might want to switch naming around if it doesn't shorten code
      by_cases h : ((inr L.to_near_litter, C) ∈ σ.val.range);
      rw [spec.range_sup, spec.range_sup, mem_union, mem_union],
      { left, left, exact h },
      { right,
        refine ⟨⟨L, hL, h⟩, _⟩,
        simp only [equiv.inv_fun_as_coe, equiv.apply_symm_apply], } } },
  { obtain ⟨hdom, hrge⟩ := σ.prop.flex_cond C,
    { refine spec.flex_cond.co_large _ _,
      { convert hdom, ext,
        rw and.congr_right_iff,
        intro hx,
        rw not_iff_not,
        rw [spec.domain_sup, spec.domain_sup, mem_union, mem_union],
        split,
        { rintro ((h | ⟨L, hL⟩) | ⟨L, hL⟩),
          { exact h },
          { cases hL, cases h rfl },
          { cases congr_arg prod.snd hL, cases h rfl } },
        { sorry } },
      { sorry } },
    { sorry } }
end

lemma new_flex_litters_inv :
  (bij.new_flex_litters abij)⁻¹ =
  bij.inv.new_inverse_flex_litters (λ L, equiv.symm $ abij L) :=
begin
  ext ⟨_ | ⟨N₁, N₂⟩, C⟩,
  { simp only [binary_condition.inv_def, new_flex_litters, new_inverse_flex_litters,
      mem_set_of_eq, prod.mk.inj_iff, exists_false, false_and, map_inl, and_false, mem_mk,
      spec.mem_inv], },
  rw [inr_mem_inv, prod.swap, mem_new_flex_litters, mem_new_inverse_flex_litters],
  split; rintro ⟨L, hL⟩; refine ⟨L, _⟩;
  simp only [prod.mk.inj_iff, sum.inr.inj_iff] at hL ⊢;
  have := hL.1.1; subst this; have := hL.1.2; subst this; have := hL.2; subst this,
  { refine ⟨⟨_, rfl⟩, rfl⟩,
    rw equiv.symm_symm, congr' 1, rw _root_.inv_inv, rw rough_bijection.inv_inv, },
  { refine ⟨⟨rfl, _⟩, rfl⟩,
    rw equiv.symm_symm, congr' 1, rw _root_.inv_inv, rw rough_bijection.inv_inv, },
end

lemma new_inverse_flex_litters_inv :
  (bij.new_inverse_flex_litters abij')⁻¹ =
  bij.inv.new_flex_litters (λ L, equiv.symm $ abij' L) :=
begin
  rw inv_eq_iff_inv_eq,
  congr,
end

lemma forward_eq_backward :
  (σ.val ⊔ bij.new_flex_litters abij ⊔ bij.new_inverse_flex_litters abij')⁻¹ =
  σ⁻¹.val ⊔ bij.inv.new_flex_litters (λ L, equiv.symm $ abij' L) ⊔
    bij.inv.new_inverse_flex_litters (λ L, equiv.symm $ abij L) :=
begin
  rw [sup_inv, sup_inv, sup_assoc, sup_assoc, new_flex_litters_inv,
    new_inverse_flex_litters_inv],
  congr' 1,
  rw sup_comm,
end

lemma flex_union_allowable
  (habij : ∀ L a, (equiv.symm (abij' (bij L)) a).val = (equiv.symm (abij L) a).val)
  (habij' : ∀ L a, ((abij (bij.inv L)).to_fun a).val = ((abij' L).to_fun a).val) :
  spec.allowable B
    (σ.val ⊔ bij.new_flex_litters abij ⊔ bij.new_inverse_flex_litters abij') :=
{ forward :=
  { one_to_one := flex_union_one_to_one bij abij abij' habij,
    atom_cond := flex_union_atom_cond bij abij abij',
    near_litter_cond := flex_union_near_litter_cond bij abij abij',
    non_flex_cond := flex_union_non_flex_cond bij abij abij',
    support_closed := flex_union_support_closed bij abij abij' },
  backward :=
  { one_to_one :=
      by { convert flex_union_one_to_one bij.inv _ _ _,
        rw forward_eq_backward bij abij abij',
        exact habij', },
    atom_cond :=
      by { convert flex_union_atom_cond bij.inv _ _,
        rw forward_eq_backward bij abij abij' },
    near_litter_cond :=
      by { convert flex_union_near_litter_cond bij.inv _ _,
        rw forward_eq_backward bij abij abij' },
    non_flex_cond :=
      by { convert flex_union_non_flex_cond bij.inv _ _,
        rw forward_eq_backward bij abij abij' },
    support_closed :=
      by { convert flex_union_support_closed bij.inv _ _,
        rw forward_eq_backward bij abij abij' },
  },
  flex_cond := flex_union_flex_cond bij abij abij',
}

lemma le_flex_union
  (habij : ∀ L a, (equiv.symm (abij' (bij L)) a).val = (equiv.symm (abij L) a).val)
  (habij' : ∀ L a, ((abij (bij.inv L)).to_fun a).val = ((abij' L).to_fun a).val) :
  σ ≤ ⟨σ.val ⊔ bij.new_flex_litters abij ⊔ bij.new_inverse_flex_litters abij',
    flex_union_allowable bij abij abij' habij habij'⟩ :=
{ le := by { simp_rw sup_assoc, exact le_sup_left },
  all_flex_domain := λ L N' C hN' hσ₁ hσ₂ L' hL', begin
    split,
    { rw [spec.domain_sup, spec.domain_sup],
      by_cases (inr L'.to_near_litter, C) ∈ σ.val.domain,
      { exact or.inl (or.inl h) },
      { have : A = C,
        { obtain ((_ | ⟨L₁, hL₁⟩) | ⟨L₁, hL₁⟩) := hσ₂,
          { cases hσ₁ hσ₂ },
          { exact (congr_arg prod.snd hL₁).symm },
          { exact (congr_arg prod.snd hL₁).symm } },
        subst this,
        exact or.inl (or.inr ⟨⟨L', hL', h⟩, rfl⟩), } },
    { rw [spec.range_sup, spec.range_sup],
      by_cases (inr L'.to_near_litter, C) ∈ σ.val.range,
      { exact or.inl (or.inl h) },
      { have : A = C,
        { obtain ((_ | ⟨L₁, hL₁⟩) | ⟨L₁, hL₁⟩) := hσ₂,
          { cases hσ₁ hσ₂ },
          { exact (congr_arg prod.snd hL₁).symm },
          { exact (congr_arg prod.snd hL₁).symm } },
        subst this,
        refine or.inr ⟨⟨L', hL', h⟩, _⟩,
        simp only [equiv.inv_fun_as_coe, equiv.apply_symm_apply], } }
  end,
  all_flex_range := λ L N' C hN' hσ₁ hσ₂ L' hL', begin
    split,
    { rw [spec.domain_sup, spec.domain_sup],
      by_cases (inr L'.to_near_litter, C) ∈ σ.val.domain,
      { exact or.inl (or.inl h) },
      { have : A = C,
        { obtain ((_ | ⟨L₁, hL₁⟩) | ⟨L₁, hL₁⟩) := hσ₂,
          { cases hσ₁ hσ₂ },
          { exact (congr_arg prod.snd hL₁).symm },
          { exact (congr_arg prod.snd hL₁).symm } },
        subst this,
        exact or.inl (or.inr ⟨⟨L', hL', h⟩, rfl⟩) } },
    { rw [spec.range_sup, spec.range_sup],
      by_cases (inr L'.to_near_litter, C) ∈ σ.val.range,
      { exact or.inl (or.inl h) },
      { have : A = C,
        { obtain ((_ | ⟨L₁, hL₁⟩) | ⟨L₁, hL₁⟩) := hσ₂,
          { cases hσ₁ hσ₂ },
          { exact (congr_arg prod.snd hL₁).symm },
          { exact (congr_arg prod.snd hL₁).symm } },
        subst this,
        refine or.inr ⟨⟨L', hL', h⟩, _⟩,
        simp only [equiv.inv_fun_as_coe, equiv.apply_symm_apply], } }
  end,
  all_atoms_domain := begin
    rintro a b L ha C hσ₁ ((hσ₂ | hσ₂) | hσ₂),
    { cases hσ₁ hσ₂ },
    { simpa only [new_flex_litters, mem_set_of_eq, prod.mk.inj_iff, false_and,
        exists_false, and_false, coe_mk] using hσ₂ },
    { simpa only [set_like.mem_coe, mem_new_inverse_flex_litters, prod.mk.inj_iff,
        false_and, exists_false] using hσ₂ }
  end,
  all_atoms_range := begin
    rintro a b L ha C hσ₁ ((hσ₂ | hσ₂) | hσ₂),
    { cases hσ₁ hσ₂ },
    { simpa only [new_flex_litters, mem_set_of_eq, prod.mk.inj_iff, false_and,
        exists_false, and_false, coe_mk] using hσ₂ },
    { simpa only [set_like.mem_coe, mem_new_inverse_flex_litters, prod.mk.inj_iff,
        false_and, exists_false] using hσ₂ }
  end }

/-- Nothing constrains a flexible litter, so we don't have any hypothesis about the fact that all
things that constrain it lie in `σ` already. -/
lemma exists_ge_flex (σ : allowable_spec B) {L : litter} (hL : flex L A) :
  ∃ ρ, σ ≤ ρ ∧ (⟨inr L.to_near_litter, A⟩ : support_condition B) ∈ ρ.val.domain :=
begin
  by_cases (inr L.to_near_litter, A) ∈ σ.val.domain,
  { exact ⟨σ, le_rfl, h⟩ },
  obtain ⟨hdom, hrge⟩ | ⟨hdom, hrge⟩ := σ.property.flex_cond A,
  swap, { cases h (hdom L hL) },
  obtain ⟨bij⟩ :nonempty (rough_bijection A σ.val.domain σ.val.range) :=
    cardinal.eq.1 (hdom.symm.trans hrge),
  have abij : ∀ L, precise_atom_bijection L (bij L),
  { refine λ L, (cardinal.eq.1 _).some,
    rw [mk_sep, mk_sep],
    transitivity #κ,
    { have := mk_sum_compl {a : litter_set L | (inl a.val, A) ∈ σ.val.domain},
      rw mk_litter_set at this,
      refine eq_of_add_eq_of_aleph_0_le this _ κ_regular.aleph_0_le,
      convert (small_of_not_mem_spec L) using 1, rw mk_sep },
    { have := mk_sum_compl
        {a : litter_set (bij L) | (inl a.val, A) ∈ σ.val.range},
      rw mk_litter_set at this, symmetry,
      refine eq_of_add_eq_of_aleph_0_le this _ κ_regular.aleph_0_le,
      convert (small_of_rough_bijection bij L) using 1, rw mk_sep } },
  set abij' : ∀ L, precise_atom_bijection (bij.inv L) L := λ L, (abij (bij.inv L)).trans {
    to_fun := λ a, ⟨a,
      by simpa only [rough_bijection.inv, subtype.val_eq_coe, equiv.apply_symm_apply] using a.2.1,
      a.2.2⟩,
    inv_fun := λ a, ⟨a,
      by simpa only [rough_bijection.inv, subtype.val_eq_coe, equiv.apply_symm_apply] using a.2.1,
      a.2.2⟩,
    left_inv := by intro a; rw [← subtype.coe_inj, subtype.coe_mk]; refl,
    right_inv := by intro a; rw [← subtype.coe_inj, subtype.coe_mk]; refl,
  } with abij'_def,
  have habij₁ : ∀ L, (abij' (bij L)).trans (abij L).symm = equiv.subtype_equiv_prop _,
  { intro L, ext1 a, rw equiv.trans_apply, rw abij'_def,
    simp only [equiv.coe_trans, equiv.coe_fn_mk, function.comp_app],
    have := (abij (bij.inv (bij L))).left_inv a, convert this using 1,
    { rw rough_bijection.inv_coe, },
    { unfold equiv.symm, dsimp only [equiv.coe_fn_mk], congr' 1,
      { rw rough_bijection.inv_coe, },
      { rw rough_bijection.inv_coe, },
      { rw rough_bijection.inv_coe, },
      { rw subtype.heq_iff_coe_eq _, refl,
        intro, rw rough_bijection.inv_coe, refl, }, },
    { rw subtype.heq_iff_coe_eq _, refl,
      intro, rw rough_bijection.inv_coe, refl, } },
  have habij₂ : ∀ L a, ((equiv.symm (abij' (bij L))).trans
    ((abij' (bij L)).trans (abij L).symm) a).val = (equiv.symm (abij L) a).val,
  { intros L a, rw ← equiv.trans_assoc, rw equiv.symm_trans_self, refl, },
  have habij : ∀ L a, (equiv.symm (abij' (bij L)) a).val = (equiv.symm (abij L) a).val,
  { intros L a, rw [← habij₂, habij₁], refl, },
  have habij' : ∀ L a, ((abij (bij.inv L)).to_fun a).val = ((abij' L).to_fun a).val,
  { intros L a, refl, },
  refine ⟨_, le_flex_union bij abij abij' habij habij', _⟩,
  rw [spec.domain_sup, spec.domain_sup],
  left, right,
  exact ⟨⟨L, hL, ‹_›⟩, rfl⟩,
  { ext, rw rough_bijection.inv_coe, refl },
end

end allowable_spec
end con_nf
