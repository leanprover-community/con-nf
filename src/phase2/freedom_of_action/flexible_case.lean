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

open set sum
open_locale cardinal

universe u

namespace con_nf
namespace allowable_partial_perm

variables [params.{u}]

open struct_perm spec

variables {α : Λ} [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [typed_positions.{}] [phase_2_assumptions α] {B : le_index α}

variables {B} (A : extended_index B) {σ : allowable_partial_perm B} {dom rge : unary_spec B}

/-- A bijection of the remaining `A`-flexible litters in an allowable partial permutation `σ`.
This is a bijection of *rough images*; we have to then take into account all of the exceptions that
have already been established in `σ`. -/
abbreviation rough_bijection (dom rge : unary_spec B) :=
{L : litter // flexible L A ∧ (inr L.to_near_litter, A) ∉ dom} ≃
{L : litter // flexible L A ∧ (inr L.to_near_litter, A) ∉ rge}

variables {A}

/-- The inverse of a rough bijection, phrased as moving from `σ` to `σ⁻¹`. -/
def rough_bijection.inv (bij : rough_bijection A σ.val.domain σ.val.range) :
  rough_bijection A σ⁻¹.val.domain σ⁻¹.val.range :=
bij.symm

@[simp] lemma rough_bijection.inv_symm (bij : rough_bijection A σ.val.domain σ.val.range) :
  bij.inv.symm = bij := by ext; refl

@[simp] lemma rough_bijection.inv_inv (bij : rough_bijection A σ.val.domain σ.val.range) :
  bij.inv.inv = bij := by ext; refl

lemma rough_bijection.inv_to_fun (bij : rough_bijection A σ.val.domain σ.val.range)
  (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}) :
  bij.inv (bij.to_fun L) = L :=
equiv.symm_apply_apply _ _

lemma rough_bijection.inv_fun_inv_fun (bij : rough_bijection A σ.val.domain σ.val.range)
  (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}) :
  bij.inv_fun (bij.inv.inv_fun L) = L :=
equiv.symm_apply_apply _ _

lemma small_of_not_mem_spec
  (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}) :
  small {a ∈ litter_set L | (inl a, A) ∈ σ.val.domain} :=
begin
  obtain ⟨N, h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N, hN, h₁, h₂⟩ := σ.property.forward.atom_cond L A,
  { cases L.property.2 (inr_mem_domain h₁) },
  { exact h₂ },
  { exact h₁ },
end

lemma small_of_rough_bijection (bij : rough_bijection A σ.val.domain σ.val.range)
  (L : {L : litter // flexible L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}) :
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
`L₁`. This yields a precise near-litter image of each flexible litter `L`. -/
def precise_atom_bijection (bij : rough_bijection A dom rge)
  (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ dom}) :=
↥{a ∈ litter_set L | (inl a, A) ∉ dom} ≃
  ↥{a ∈ litter_set (bij L) | (inl a, A) ∉ rge}

namespace precise_atom_bijection

/-- The inverse of a rough bijection is a rough bijection for the inverse permutation. -/
def symm {bij : rough_bijection A dom rge} {L} (abij : bij.precise_atom_bijection L) :
  precise_atom_bijection bij.symm (bij L) :=
{ to_fun := λ a, ⟨abij.inv_fun a,
    (by simpa only [equiv.symm_apply_apply] using (abij.inv_fun a).2.1), (abij.inv_fun a).2.2⟩,
  inv_fun := λ a, abij.to_fun ⟨a, (by simpa only [equiv.symm_apply_apply] using a.2.1), a.2.2⟩,
  left_inv := begin
    rintro ⟨a, ha₁, ha₂⟩,
    simp only [equiv.inv_fun_as_coe, subtype.coe_mk, subtype.coe_eta, equiv.to_fun_as_coe,
      equiv.apply_symm_apply],
  end,
  right_inv := begin
    rintro ⟨a, ha₁, ha₂⟩,
    simp only [subtype.coe_mk, equiv.to_fun_as_coe, equiv.inv_fun_as_coe, equiv.symm_apply_apply,
      subtype.mk_eq_mk],
  end }

def inv {σ : allowable_partial_perm B} {bij : rough_bijection A σ.val.domain σ.val.range}
  {L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ.val.range}} {hL}
  (abij : bij.precise_atom_bijection (bij.inv_fun ⟨L.val, hL⟩)) :
    precise_atom_bijection bij.inv L := {
  to_fun := λ a, ⟨abij.inv_fun
    ⟨a, by simpa only [equiv.inv_fun_as_coe, equiv.apply_symm_apply] using a.2.1, a.2.2⟩,
    begin
      simp only [equiv.inv_fun_as_coe, subtype.coe_eta],
      convert (abij.inv_fun ⟨a, _, _⟩).2,
      rw subtype.eta, refl,
    end⟩,
  inv_fun := λ a, ⟨abij.to_fun ⟨a, by simpa only [subtype.eta] using a.2.1, a.2.2⟩,
    begin
      convert (abij.to_fun ⟨a, _, _⟩).2 using 2,
      simp only [subtype.coe_mk, equiv.inv_fun_as_coe, equiv.apply_symm_apply, subtype.val_eq_coe],
    end⟩,
  left_inv := begin
    rintro ⟨a, ha₁, ha₂⟩,
    simp only [subtype.coe_eta, subtype.coe_mk, equiv.inv_fun_as_coe, equiv.to_fun_as_coe,
      equiv.apply_symm_apply, subtype.mk_eq_mk],
  end,
  right_inv := begin
    rintro ⟨a, ha₁, ha₂⟩,
    simp only [equiv.inv_fun_as_coe, equiv.to_fun_as_coe, subtype.coe_eta, subtype.coe_mk,
      equiv.symm_apply_apply, subtype.mk_eq_mk],
  end }

end precise_atom_bijection

/-- If the image of this atom has already been specified by `σ`, return the value that was already
given. Otherwise, return the image generated by `precise_image_bijection`. -/
private noncomputable def precise_atom_image {dom rge} (bij : rough_bijection A dom rge)
  (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ dom})
  (abij : bij.precise_atom_bijection L)
  (atom_value : {a : litter_set L // (inl a.val, A) ∈ dom} → atom)
  (a : atom) (ha : a ∈ litter_set L) : atom :=
@dite _ ((inl a, A) ∈ dom) (classical.dec _)
  (λ h, atom_value ⟨⟨a, ha⟩, h⟩)
  (λ h, abij.to_fun ⟨a, ha, h⟩)

lemma precise_atom_image_range {dom rge} (bij : rough_bijection A dom rge)
  (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ dom})
  (abij : bij.precise_atom_bijection L)
  (atom_value : {a : litter_set L // (inl a.val, A) ∈ dom} → atom) :
  range (λ a : litter_set L, precise_atom_image bij L abij atom_value a a.property) =
    (litter_set (bij L) ∩ {a | (inl a, A) ∉ rge}) ∪ range atom_value :=
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
def precise_litter_image_aux {dom rge} (bij : rough_bijection A dom rge)
  (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ dom})
  (abij : bij.precise_atom_bijection L)
  (atom_value : {a : litter_set L // (inl a.val, A) ∈ dom} → atom)
  (h₁ : # ↥(litter_set ↑(bij L) \ {a : atom | (inl a, A) ∉ rge}) < # κ)
  (h₂ : # {a : litter_set L // (inl a.val, A) ∈ dom} < # κ) : near_litter :=
⟨(bij L),
  range (λ (a : litter_set L), precise_atom_image bij L abij atom_value a a.property),
  begin
    rw precise_atom_image_range,
    unfold is_near_litter is_near small symm_diff,
    refine (cardinal.mk_union_le _ _).trans_lt (cardinal.add_lt_of_lt κ_regular.aleph_0_le _ _),
    { rw [← sup_eq_union, sdiff_sup, ← inf_eq_inter, sdiff_inf_self_left],
      exact lt_of_le_of_lt (cardinal.mk_le_mk_of_subset $ inter_subset_left _ _) h₁ },
    { rw [← sup_eq_union, sup_sdiff, ← inf_eq_inter, inf_sdiff, sdiff_self, bot_inf_eq,
        bot_sup_eq],
      refine lt_of_le_of_lt (cardinal.mk_le_mk_of_subset $ @sdiff_le _ _ (litter_set _) _) _,
      exact lt_of_le_of_lt cardinal.mk_range_le h₂ },
end⟩

private lemma precise_litter_image_aux_inj (bij : rough_bijection A σ.val.domain σ.val.range)
  {L₁ L₂ : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}}
  {abij₁ : bij.precise_atom_bijection L₁} {abij₂ : bij.precise_atom_bijection L₂}
  {atom_value₁ : {a : litter_set L₁ // (inl a.val, A) ∈ σ.val.domain} → atom}
  {atom_value₂ : {a : litter_set L₂ // (inl a.val, A) ∈ σ.val.domain} → atom}
  {h₁ h₂ h₃ h₄} :
  precise_litter_image_aux bij L₁ abij₁ atom_value₁ h₁ h₂ =
  precise_litter_image_aux bij L₂ abij₂ atom_value₂ h₃ h₄ →
    L₁ = L₂ :=
begin
  intro h,
  have := congr_arg sigma.fst h,
  simpa only [precise_litter_image_aux, subtype.coe_inj, equiv.to_fun_as_coe,
    embedding_like.apply_eq_iff_eq] using this,
end

noncomputable def precise_litter_image (bij : rough_bijection A σ.val.domain σ.val.range)
  (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain})
  (abij : bij.precise_atom_bijection L) : near_litter :=
precise_litter_image_aux bij L abij (λ a, atom_value σ A a.1 a.2)
  (begin
    convert small_of_rough_bijection bij L,
    ext a,
    split,
    { rintro ⟨ha₁, ha₂⟩, simp only [mem_set_of_eq, not_not_mem] at ha₂, exact ⟨ha₁, ha₂⟩ },
    { rintro ⟨ha₁, ha₂⟩, exact ⟨ha₁, function.eval ha₂⟩ }
  end)
  (by { convert small_of_not_mem_spec L using 1, rw cardinal.mk_sep, refl })

noncomputable def precise_litter_inverse_image (bij : rough_bijection A σ.val.domain σ.val.range)
  (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ.val.range})
  (abij : precise_atom_bijection bij.symm L) :
  near_litter :=
precise_litter_image_aux bij.symm L abij
  (λ a, atom_value σ⁻¹ A a.1 (by simpa only [val_inv, spec.domain_inv] using a.2))
  (begin
    convert small_of_rough_bijection bij.inv
      ⟨L.1, L.2.1, by simpa only [val_inv, spec.domain_inv] using L.2.2⟩,
    ext a, split,
    { rintro ⟨ha₁, ha₂⟩, simp only [mem_set_of_eq, not_not_mem] at ha₂,
      refine ⟨_, by rwa [val_inv, spec.range_inv]⟩,
      rw subtype.eta, exact ha₁, },
    { rintro ⟨ha₁, ha₂⟩,
      rw subtype.eta at ha₁,
      exact ⟨ha₁, function.eval ha₂⟩, }
  end)
  (begin
    convert small_of_not_mem_spec ⟨L.1, L.2.1, _⟩ using 1,
    swap, exact σ⁻¹,
    { rw cardinal.mk_sep, refl, },
    exact L.2.2,
  end)

lemma precise_litter_image_inj {bij : rough_bijection A σ.val.domain σ.val.range}
  {L₁ L₂ : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}}
  (abij₁ : bij.precise_atom_bijection L₁) (abij₂ : bij.precise_atom_bijection L₂) :
  precise_litter_image bij L₁ abij₁ = precise_litter_image bij L₂ abij₂ → L₁ = L₂ :=
precise_litter_image_aux_inj bij

lemma precise_litter_inverse_image_inj {bij : rough_bijection A σ.val.domain σ.val.range}
  {L₁ L₂ : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ.val.range}}
  (abij₁ : precise_atom_bijection bij.symm L₁) (abij₂ : precise_atom_bijection bij.symm L₂) :
  precise_litter_inverse_image bij L₁ abij₁ = precise_litter_inverse_image bij L₂ abij₂ → L₁ = L₂ :=
precise_litter_image_aux_inj bij.inv

def new_flexible_litters (bij : rough_bijection A σ.val.domain σ.val.range)
  (abij : ∀ L, bij.precise_atom_bijection L) : spec B := {
  carrier := {c | ∃ (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}),
    c = (inr (L.1.to_near_litter, precise_litter_image bij L (abij L)), A)},
  domain := {c | ∃ (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}),
    c = (inr L.1.to_near_litter, A)},
  range := {c | ∃ (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}),
    c = (inr (precise_litter_image bij L (abij L)), A)},
  image_domain' := sorry,
  image_range' := sorry,
}

def new_inverse_flexible_litters (bij : rough_bijection A σ.val.domain σ.val.range)
  (abij : ∀ L, bij.precise_atom_bijection L) : spec B := {
  carrier := {c | ∃ (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}),
    c = (inr (precise_litter_inverse_image bij _ (abij L).symm, (bij L).1.to_near_litter), A)},
  domain := {c | ∃ L, c = (inr (precise_litter_inverse_image bij _ (abij L).symm), A)},
  range := {c | ∃ L, c = (inr (bij L).1.to_near_litter, A)},
  image_domain' := sorry,
  image_range' := sorry,
}

@[simp] lemma mem_new_flexible_litters (bij : rough_bijection A σ.val.domain σ.val.range)
  (abij : ∀ L, bij.precise_atom_bijection L) (c : binary_condition B) :
  c ∈ new_flexible_litters bij abij ↔
  ∃ (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}),
    c = (inr (L.1.to_near_litter, precise_litter_image bij L (abij L)), A) :=
iff.rfl

@[simp] lemma mem_new_inverse_flexible_litters (bij : rough_bijection A σ.val.domain σ.val.range)
  (abij : ∀ L, bij.precise_atom_bijection L) (c : binary_condition B) :
  c ∈ new_inverse_flexible_litters bij abij ↔
  ∃ (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}),
    c = (inr (precise_litter_inverse_image bij _ (abij L).symm, (bij L).1.to_near_litter), A) :=
iff.rfl

end rough_bijection

open rough_bijection

variables (bij : rough_bijection A σ.val.domain σ.val.range)
  (abij : ∀ L, bij.precise_atom_bijection L)

lemma flexible_union_one_to_one :
  spec.one_to_one_forward
    (σ.val ⊔ bij.new_flexible_litters abij ⊔ bij.new_inverse_flexible_litters abij) :=
begin
  refine λ C, ⟨_, _⟩,
  { rintro b a₁ ((ha₁ | ha₁) | ha₁) a₂ ha₂,
    { obtain ((ha₂ | ha₂) | ha₂) := ha₂,
      { exact (σ.property.forward.one_to_one C).atom b ha₁ ha₂ },
      { simpa only [new_flexible_litters, mem_set_of_eq, prod.mk.inj_iff, false_and,
          exists_false, and_false, coe_mk] using ha₂ },
      { simpa only [new_inverse_flexible_litters, mem_set_of_eq, prod.mk.inj_iff, false_and,
          exists_false, and_false, coe_mk] using ha₂ } },
    { simpa only [new_flexible_litters, mem_set_of_eq, prod.mk.inj_iff, false_and,
        exists_false, and_false, coe_mk] using ha₁ },
    { simpa only [new_inverse_flexible_litters, mem_set_of_eq, prod.mk.inj_iff, false_and,
          exists_false, and_false, coe_mk] using ha₁ } },
  rintro N M₁ ((hM₁ | hM₁) | hM₁) M₂ ((hM₂ | hM₂) | hM₂),
  { exact (σ.property.forward.one_to_one C).near_litter N hM₁ hM₂ },
  { obtain ⟨N', hN'₁, hN'₂⟩ := σ.property.backward.near_litter_cond _ _ C hM₁,
    obtain ⟨L', hL'⟩ := hM₂, cases hL',
    cases (bij L').property.right (inr_mem_domain hN'₁), },
  { obtain ⟨L', hL'⟩ := hM₂, cases hL',
    cases (bij L').property.right (inr_mem_range hM₁), },
  { exfalso,
    sorry },
  { obtain ⟨L₁, hL₁⟩ := hM₁, obtain ⟨L₂, hL₂⟩ := hM₂,
    cases precise_litter_image_inj _ _
      ((prod.ext_iff.1 $ inr_injective (prod.ext_iff.1 hL₁).1).2.symm.trans
        (prod.ext_iff.1 $ inr_injective (prod.ext_iff.1 hL₂).1).2),
    cases hL₁, cases hL₂, refl },
  { obtain ⟨L₁, hL₁⟩ := hM₁, obtain ⟨L₂, hL₂⟩ := hM₂,
    sorry },
  { obtain ⟨L₁, hL₁⟩ := hM₁,
    obtain ⟨N', hN'₁, hN'₂⟩ := σ.property.backward.near_litter_cond _ _ C hM₂,
    sorry },
  { sorry },
  obtain ⟨L₁, hL₁⟩ := hM₁, obtain ⟨L₂, hL₂⟩ := hM₂,
  unfold precise_litter_inverse_image at hL₁ hL₂,
  have := precise_litter_inverse_image_inj (abij L₁).symm (abij L₂).symm _,
  rw embedding_like.apply_eq_iff_eq at this,
  cases this, cases hL₁, cases hL₂, refl,
  have := litter.to_near_litter_injective
    ((prod.ext_iff.1 $ inr_injective (prod.ext_iff.1 hL₁).1).2.symm.trans
      (prod.ext_iff.1 $ inr_injective (prod.ext_iff.1 hL₂).1).2),
  rw [subtype.val_inj, embedding_like.apply_eq_iff_eq] at this,
  cases this,
  refl,
end

lemma flexible_union_atoms_eq (L : litter) (C : extended_index B) :
  {a ∈ litter_set L | (inl a, C) ∈
    (σ.val ⊔ bij.new_flexible_litters abij ⊔ bij.new_inverse_flexible_litters abij).domain} =
  {a ∈ litter_set L | (inl a, C) ∈ σ.val.domain} :=
begin
  ext a,
  simp only [spec.domain_sup, new_flexible_litters, new_inverse_flexible_litters,
    subtype.val_eq_coe, mem_set_of_eq, set_coe.exists, subtype.coe_mk, equiv.to_fun_as_coe,
    mem_union_eq, mem_sep_iff],
  refine and_congr_right (λ ha, ⟨_, λ h, or.inl $ or.inl h⟩),
  rintro ((h | ⟨L, hL, hc⟩) | ⟨L, hL, hc⟩),
  { exact h, },
  { cases hc, },
  { cases hc, },
end

lemma flexible_union_atom_cond (L C) :
  spec.atom_cond
    (σ.val ⊔ bij.new_flexible_litters abij ⊔ bij.new_inverse_flexible_litters abij) L C :=
begin
  obtain ⟨N, h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N, hN, h₁, h₂⟩ := σ.prop.forward.atom_cond L C,
  { exact spec.atom_cond.all N
      (or.inl $ or.inl h₁) atom_map (λ a H, or.inl $ or.inl $ h₂ a H) h₃ },
  { obtain rfl | h := eq_or_ne A C,
    { by_cases flexible L A,
      { refine spec.atom_cond.small_in _ (or.inl $ or.inr ⟨⟨L, h, h₁⟩, rfl⟩) _ _,
        { rwa flexible_union_atoms_eq },
        rintro a b ((hab | ⟨L', ⟨⟩⟩) | ⟨L', ⟨⟩⟩),
        sorry
        -- refine ⟨⟨a, ha⟩, _⟩,
        -- unfold precise_atom_image,
        -- rw dif_pos _,
        -- exact atom_value_eq_of_mem _ _ _ _ _ hab
         },
      refine spec.atom_cond.small_out _ (by rwa flexible_union_atoms_eq),
      contrapose! h₁, rw [spec.domain_sup, spec.domain_sup] at h₁,
      obtain ((_ | _) | _) := h₁,
      { exact h₁ },
      { rw mem_domain at h₁, obtain ⟨_, ⟨L', rfl⟩, h₁⟩ := h₁, cases h₁, cases h L'.2.1 },
      rw mem_domain at h₁,
      obtain ⟨_, ⟨L', rfl⟩, h₁⟩ := h₁,
      simp only [binary_condition.domain_mk, sum.map_inr, prod.mk.inj_iff, eq_self_iff_true,
        and_true] at h₁,
      suffices : L = L',
      { subst this, cases h L'.2.1 },
      convert (congr_arg sigma.fst h₁).symm,
      simp only [equiv.symm_apply_apply] },
    { refine spec.atom_cond.small_out _ _,
      { contrapose! h₁, rw [spec.domain_sup, spec.domain_sup] at h₁,
        obtain ((_ | _) | _) := h₁,
        { exact h₁ },
        { obtain ⟨_, ⟨L', rfl⟩, ⟨⟩⟩ := h₁, cases h rfl },
        { rw mem_domain at h₁, obtain ⟨_, ⟨L', rfl⟩, h₁⟩ := h₁,
          cases congr_arg prod.snd h₁, cases h rfl } },
      rw flexible_union_atoms_eq, exact h₂, } },
  { refine spec.atom_cond.small_in N (or.inl $ or.inl hN) _ _,
    { rw flexible_union_atoms_eq, exact h₁ },
    rintro a b ((hab | ⟨L', ⟨⟩⟩) | ⟨L', ⟨⟩⟩),
    exact h₂ hab }
end

lemma flexible_union_near_litter_cond :
  ∀ N₁ N₂ C, spec.near_litter_cond
    (σ.val ⊔ bij.new_flexible_litters abij ⊔ bij.new_inverse_flexible_litters abij) N₁ N₂ C :=
sorry

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

lemma flexible_union_non_flexible_cond :
  spec.non_flexible_cond B
    (σ.val ⊔ bij.new_flexible_litters abij ⊔ bij.new_inverse_flexible_litters abij) :=
begin
  unfold spec.non_flexible_cond,
  intros hb hg hd hgb hdb hdg hNl hp ht hf π h1,
  unfold struct_perm.satisfies struct_perm.satisfies_cond at h1,
  have h := h1 hf,
  dsimp at h,
  rw ← h,
  sorry
  -- exact unpack_coh_cond hgb hdb hdg hp ht π,
end

lemma flexible_union_support_closed :
  (σ.val ⊔ bij.new_flexible_litters abij ⊔ bij.new_inverse_flexible_litters abij)
    .domain.support_closed B :=
sorry

lemma flexible_union_flexible_cond (C) :
  spec.flexible_cond B
    (σ.val ⊔ bij.new_flexible_litters abij ⊔ bij.new_inverse_flexible_litters abij) C :=
begin
  obtain rfl | h := eq_or_ne C A,
  { refine spec.flexible_cond.all (λ L hL, _) (λ L hL, _),
    { by_cases h : ((inr L.to_near_litter, C) ∈ σ.val.domain);
        rw [spec.domain_sup, spec.domain_sup, mem_union, mem_union]; left,
      { left, exact h },
      exact or.inr ⟨⟨L, hL, h⟩, rfl⟩, },
    { -- might want to switch naming around if it doesn't shorten code
      by_cases h : ((inr L.to_near_litter, C) ∈ σ.val.range);
      rw [spec.range_sup, spec.range_sup, mem_union, mem_union],
      { left, left, exact h },
      { right,
        refine ⟨bij.inv_fun ⟨L, hL, h⟩, _⟩,
        simp only [equiv.inv_fun_as_coe, equiv.apply_symm_apply], } } },
  { obtain ⟨hdom, hrge⟩ := σ.prop.flexible_cond C,
    { refine spec.flexible_cond.co_large _ _,
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

def abij_inv :
  Π (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ⁻¹.val.domain}),
    bij.inv.precise_atom_bijection L :=
λ L, (abij (bij.inv_fun ⟨L, by simpa only [val_inv, spec.domain_inv] using L.property⟩)).inv

lemma abij_inv_symm
  (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}) :
  (abij_inv bij abij (bij.to_fun L)).symm == abij L :=
sorry

lemma abij_inv_inv :
  abij_inv bij.inv (abij_inv bij abij) = abij :=
begin
  ext1 L, ext1 a,
  simp only [abij_inv, precise_atom_bijection.inv, subtype.coe_mk, equiv.to_fun_as_coe,
    equiv.coe_fn_mk],
  have := rough_bijection.inv_fun_inv_fun bij ⟨L, L.2⟩,
  rw [← subtype.coe_inj, subtype.coe_mk],
  sorry
end

lemma atom_value_heq
  (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}) :
  (λ (a : {a : litter_set (bij.inv (bij.to_fun L)) // (inl a.val, A) ∈ σ⁻¹.val.range}),
    σ⁻¹⁻¹.atom_value A ↑(a.val) a.2) ==
  λ (a : {a : litter_set L // (inl a.val, A) ∈ σ.val.domain}),
    σ.atom_value A ↑(a.val) a.2 :=
sorry

lemma precise_litter_image_eq
  (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ.val.domain}) :
  bij.precise_litter_image L (abij L) =
  bij.inv.precise_litter_inverse_image ((bij.inv) (bij.to_fun L))
    (abij_inv bij abij (bij.to_fun L)).symm :=
begin
  refine near_litter.val_injective _,
  rw [precise_litter_image, precise_litter_inverse_image,
    precise_litter_image_aux, precise_litter_image_aux],
  dsimp only,
  rw set.range_eq_iff, split,
  { intro a, refine ⟨⟨a, _⟩, _⟩,
    { rw inv_to_fun, exact a.2, },
    { dsimp only,
      congr' 1,
      { exact rough_bijection.inv_symm _, },
      { exact inv_to_fun _ _, },
      { exact abij_inv_symm _ _ _, },
      { exact atom_value_heq bij L, } } },
  { rintros b ⟨c, hbc⟩, dsimp only at hbc,
    refine ⟨⟨c, _⟩, _⟩,
    { have := c.2, simp_rw inv_to_fun at this, exact this, },
    { convert hbc using 2,
      { exact (rough_bijection.inv_symm _).symm, },
      { exact (inv_to_fun _ _).symm, },
      { exact (abij_inv_symm _ _ _).symm, },
      { exact (atom_value_heq bij L).symm, } } }
end

lemma precise_litter_inverse_image_eq
  (L : {L : litter | flexible L A ∧ (inr L.to_near_litter, A) ∉ σ⁻¹.val.domain}) :
  bij.inv.precise_litter_inverse_image ((bij.inv) L) (abij_inv bij abij L).symm =
  bij.precise_litter_image (bij.inv_fun L) (abij (bij.inv_fun L)) :=
by rw [precise_litter_image_eq bij abij (bij.inv_fun L), equiv.right_inv bij L]

lemma new_flexible_litters_inv :
  (bij.new_flexible_litters abij)⁻¹ = bij.inv.new_inverse_flexible_litters (abij_inv bij abij) :=
begin
  ext ⟨_ | ⟨N₁, N₂⟩, C⟩,
  { simp only [binary_condition.inv_mk, new_flexible_litters, new_inverse_flexible_litters,
      mem_set_of_eq, prod.mk.inj_iff, exists_false, false_and, map_inl, and_false, mem_mk,
      spec.mem_inv], },
  rw [inr_mem_inv, prod.swap, mem_new_flexible_litters, mem_new_inverse_flexible_litters],
  dsimp only,
  split,
  { rintro ⟨L, hL⟩, simp only [subtype.val_eq_coe, prod.mk.inj_iff] at hL,
    have := hL.1.1, subst this,
    have := hL.1.2, subst this,
    have := hL.2, subst this,
    clear hL,
    refine ⟨bij.to_fun L, _⟩,
    rw precise_litter_image_eq bij abij L,
    simp_rw rough_bijection.inv_to_fun,
    refl, },
  { rintro ⟨L, hL⟩, simp only [subtype.val_eq_coe, prod.mk.inj_iff] at hL,
    have := hL.1.1, subst this,
    have := hL.1.2, subst this,
    have := hL.2, subst this,
    clear hL,
    rw precise_litter_inverse_image_eq,
    exact ⟨bij.inv_fun L, rfl⟩, },
end

lemma new_inverse_flexible_litters_inv :
  (bij.new_inverse_flexible_litters abij)⁻¹ = bij.inv.new_flexible_litters (abij_inv bij abij) :=
begin
  rw inv_eq_iff_inv_eq,
  rw new_flexible_litters_inv bij.inv (abij_inv bij abij),
  congr' 1,
  { rw has_involutive_inv.inv_inv, },
  { rw rough_bijection.inv_inv, },
  { rw abij_inv_inv, },
end

lemma forward_eq_backward :
  (σ.val ⊔ bij.new_flexible_litters abij ⊔ bij.new_inverse_flexible_litters abij)⁻¹ =
  σ⁻¹.val ⊔ bij.inv.new_flexible_litters (abij_inv bij abij) ⊔
    bij.inv.new_inverse_flexible_litters (abij_inv bij abij) :=
begin
  rw [sup_inv, sup_inv, val_inv, sup_assoc, sup_assoc, new_flexible_litters_inv,
    new_inverse_flexible_litters_inv],
  congr' 1,
  rw sup_comm,
end

lemma flexible_union_allowable :
  spec.allowable B
    (σ.val ⊔ bij.new_flexible_litters abij ⊔ bij.new_inverse_flexible_litters abij) :=
{ forward :=
  { one_to_one := flexible_union_one_to_one bij abij,
    atom_cond := flexible_union_atom_cond bij abij,
    near_litter_cond := flexible_union_near_litter_cond bij abij,
    non_flexible_cond := flexible_union_non_flexible_cond bij abij,
    support_closed := flexible_union_support_closed bij abij },
  backward :=
  { one_to_one :=
      by { convert flexible_union_one_to_one bij.inv (abij_inv bij abij),
        rw forward_eq_backward bij abij },
    atom_cond :=
      by { convert flexible_union_atom_cond bij.inv (abij_inv bij abij),
        rw forward_eq_backward bij abij },
    near_litter_cond :=
      by { convert flexible_union_near_litter_cond bij.inv (abij_inv bij abij),
        rw forward_eq_backward bij abij },
    non_flexible_cond :=
      by { convert flexible_union_non_flexible_cond bij.inv (abij_inv bij abij),
        rw forward_eq_backward bij abij },
    support_closed :=
      by { convert flexible_union_support_closed bij.inv (abij_inv bij abij),
        rw forward_eq_backward bij abij },
  },
  flexible_cond := flexible_union_flexible_cond bij abij,
}

lemma le_flexible_union :
  σ ≤ ⟨σ.val ⊔ bij.new_flexible_litters abij ⊔ bij.new_inverse_flexible_litters abij,
    flexible_union_allowable bij abij⟩ :=
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
        refine or.inr ⟨bij.inv_fun ⟨L', hL', h⟩, _⟩,
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
        refine or.inr ⟨bij.inv_fun ⟨L', hL', h⟩, _⟩,
        simp only [equiv.inv_fun_as_coe, equiv.apply_symm_apply], } }
  end,
  all_atoms_domain := begin
    rintro a b L ha C hσ₁ ((hσ₂ | hσ₂) | hσ₂),
    { cases hσ₁ hσ₂ },
    { simpa only [new_flexible_litters, mem_set_of_eq, prod.mk.inj_iff, false_and,
        exists_false, and_false, coe_mk] using hσ₂ },
    { simpa only [new_inverse_flexible_litters, mem_set_of_eq, prod.mk.inj_iff, false_and,
        exists_false, and_false, coe_mk] using hσ₂ }
  end,
  all_atoms_range := begin
    rintro a b L ha C hσ₁ ((hσ₂ | hσ₂) | hσ₂),
    { cases hσ₁ hσ₂ },
    { simpa only [new_flexible_litters, mem_set_of_eq, prod.mk.inj_iff, false_and,
        exists_false, and_false, coe_mk] using hσ₂ },
    { simpa only [new_inverse_flexible_litters, mem_set_of_eq, prod.mk.inj_iff, false_and,
        exists_false, and_false, coe_mk] using hσ₂ }
  end }

/-- Nothing constrains a flexible litter, so we don't have any hypothesis about the fact that all
things that constrain it lie in `σ` already. -/
lemma exists_ge_flexible (σ : allowable_partial_perm B) {L : litter} (hL : flexible L A) :
  ∃ ρ, σ ≤ ρ ∧ (⟨inr L.to_near_litter, A⟩ : support_condition B) ∈ ρ.val.domain :=
begin
  by_cases (inr L.to_near_litter, A) ∈ σ.val.domain,
  { exact ⟨σ, le_rfl, h⟩ },
  obtain ⟨hdom, hrge⟩ | ⟨hdom, hrge⟩ := σ.property.flexible_cond A,
  swap, { cases h (hdom L hL) },
  have bij : rough_bijection A σ.val.domain σ.val.range :=
    (cardinal.eq.mp $ eq.trans hdom.symm hrge).some,
  have abij : ∀ L, bij.precise_atom_bijection L,
  { refine λ L, (cardinal.eq.mp _).some,
    rw [cardinal.mk_sep, cardinal.mk_sep],
    transitivity #κ,
    { have := cardinal.mk_sum_compl {a : litter_set L | (inl a.val, A) ∈ σ.val.domain},
      rw mk_litter_set at this,
      refine cardinal.eq_of_add_eq_of_aleph_0_le this _ κ_regular.aleph_0_le,
      convert (small_of_not_mem_spec L) using 1, rw cardinal.mk_sep },
    { have := cardinal.mk_sum_compl
        {a : litter_set (bij L) | (inl a.val, A) ∈ σ.val.range},
      rw mk_litter_set at this, symmetry,
      refine cardinal.eq_of_add_eq_of_aleph_0_le this _ κ_regular.aleph_0_le,
      convert (small_of_rough_bijection bij L) using 1, rw cardinal.mk_sep } },
  refine ⟨_, le_flexible_union bij abij, _⟩,
  rw [spec.domain_sup, spec.domain_sup],
  left, right,
  exact ⟨⟨L, hL, ‹_›⟩, rfl⟩,
end

end allowable_partial_perm
end con_nf
