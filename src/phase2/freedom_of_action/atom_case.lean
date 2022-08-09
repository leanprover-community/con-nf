import phase2.freedom_of_action.constrains
import phase2.freedom_of_action.values
import phase2.freedom_of_action.zorn

/-!
# Maximality proof: Atom case

Suppose that we have an atom whose litter is specified in `σ`. We want to extend `σ` such that all
of the atoms in this litter are now specified. To do this, we construct an arbitrary bijection of
the unassigned atoms in the litter in the domain with the unassigned atoms in the litter's image.
-/

open function set sum
open_locale cardinal

universe u

namespace con_nf
namespace allowable_partial_perm

variables [params.{u}]

open struct_perm spec

variables {α : Λ} [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [typed_positions.{}] [phase_2_assumptions α] {B : le_index α}

variables (σ : allowable_partial_perm B) (a : atom) (A : extended_index B) (N : near_litter)

lemma atom_value_inj_range (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  range (λ b : {b : atom | b ∈ litter_set a.fst ∧ (inl b, A) ∈ σ.val.domain},
    (atom_value_inj σ A) ⟨b.val, b.property.right⟩) =
  {b : atom | b ∈ N.snd.val ∧ (inl b, A) ∈ σ.val.range} :=
begin
  rw range_eq_iff,
  refine ⟨λ c, ⟨_, _⟩, λ c hc, _⟩,
  { dsimp only [atom_value_inj, subtype.coe_mk, embedding.coe_fn_mk],
    have := atom_value_spec σ A c c.property.right,
    obtain ⟨N', h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N', hN, h₁, h₂⟩ :=
      σ.property.forward.atom_cond a.fst A,
    { cases (σ.property.backward.one_to_one A).near_litter _ ha h₁,
      rw [h₃, set.mem_range],
      refine ⟨⟨c, c.2.1⟩, _⟩,
      rw (σ.property.backward.one_to_one A).atom _ (h₂ c c.2.1) this,
      refl },
    { rw mem_domain at h₁, cases h₁ ⟨_, ha, rfl⟩ },
    { cases (σ.property.backward.one_to_one A).near_litter _ ha hN,
      exact (h₂ this).mp c.property.left } },
  { exact atom_value_spec_range σ A c c.property.right, },
  obtain ⟨hc, hc'⟩ := hc,
  rw spec.mem_range at hc',
  obtain ⟨⟨⟨a₁, a₂⟩ | Ns, C⟩, hd₁, hd₂⟩ := hc'; cases hd₂,
  refine ⟨⟨a₁, _, inl_mem_domain hd₁⟩, (σ.property.backward.one_to_one A).atom a₁
    (atom_value_spec σ A a₁ (inl_mem_domain hd₁)) hd₁⟩,
  obtain ⟨M, hM, s, hs₁, hs₂⟩ := σ.property.backward.near_litter_cond _ _ _ ha,
  dsimp only at hs₂,
  by_cases c ∈ litter_set N.fst,
  { obtain ⟨N', h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N', hN, h₁, h₂⟩ :=
      σ.property.backward.atom_cond N.fst A,
    { cases (σ.property.forward.one_to_one A).near_litter _ h₁ hM,
      cases (σ.property.forward.one_to_one A).atom _ (h₂ c h) hd₁,
      rw [hs₂, h₃],
      refine or.inl ⟨⟨_, rfl⟩, _⟩,
      rintro ⟨d, hd⟩,
      have := hs₁ d,
      rw hd at this,
      cases (σ.property.backward.one_to_one A).atom _ this hd₁,
      obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := d.property,
      { exact h₂ hc },
      { exact h₂ h } },
    { rw mem_domain at h₁, cases h₁ ⟨_, hM, rfl⟩ },
    { cases (σ.property.forward.one_to_one A).near_litter _ hM hN,
      rw hs₂,
      refine or.inl ⟨(h₂ hd₁).mp h, _⟩,
      rintro ⟨d, hd⟩,
      have := hs₁ d,
      rw hd at this,
      cases (σ.property.backward.one_to_one A).atom _ this hd₁,
      obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := d.property,
      { exact h₂ hc },
      { exact h₂ h } } },
  have : a₁ = _ := (σ.property.forward.one_to_one A).atom _ hd₁ (hs₁ ⟨c, or.inr ⟨hc, h⟩⟩),
  subst this,
  rw hs₂,
  refine or.inr ⟨⟨_, rfl⟩, _⟩,
  obtain ⟨N', h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N', hN, h₁, h₂⟩ := σ.2.backward.atom_cond N.fst A,
  { cases (σ.property.forward.one_to_one A).near_litter _ h₁ hM,
    rw h₃,
    rintro ⟨d, hd⟩,
    have := h₂ d d.property,
    rw [subtype.coe_eta, hd] at this,
    cases (σ.property.backward.one_to_one A).atom _ hd₁ this,
    exact h d.property },
  { rw mem_domain at h₁, cases h₁ ⟨_, hM, rfl⟩ },
  { cases (σ.property.forward.one_to_one A).near_litter _ hM hN,
    rw ← h₂ hd₁,
    exact h }
end

/-- The domain and range of an allowable partial permutation, restricted to a given litter, are
equivalent. The equivalence produced by this function is induced by the allowable partial
permutation itself, so if this function maps an atom `a` to `b`, we have `π_A(a) = b` for all
allowable `π` satisfying `σ`. -/
noncomputable def cond_domain_range_equiv (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  {b | b ∈ litter_set a.fst ∧ (inl b, A) ∈ σ.val.domain} ≃
  {b | b ∈ N.snd.val ∧ (inl b, A) ∈ σ.val.range} :=
begin
  convert equiv.of_injective (λ (b : {b | b ∈ litter_set a.fst ∧ (inl b, A) ∈ σ.val.domain}),
    atom_value_inj σ A ⟨b.val, b.property.right⟩) _ using 2,
  { symmetry, exact atom_value_inj_range σ a A N ha },
  { intros b₁ b₂ hb,
    simpa only [subtype.mk_eq_mk, subtype.val_inj] using
      @function.embedding.injective _ _ (atom_value_inj σ A)
        ⟨b₁.val, b₁.property.right⟩ ⟨b₂.val, b₂.property.right⟩ hb },
end

/-- If we are in the "small" case (although this holds in both cases), the amount of atoms in a
given litter whose positions we have not defined so far is the same as the amount of atoms in the
resulting near-litter which are not the image of anything under `σ`. This means we can construct an
arbitrary bijection of these remaining atoms, "filling out" the specification to define the
permutation of all atoms in the litter to the atoms in the resulting near-litter. -/
lemma equiv_not_mem_atom (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  #↥{a' ∈ litter_set a.fst | (⟨inl a', A⟩ : support_condition B) ∉ σ.val.domain} =
    #↥{a' ∈ N.snd.val | (⟨inl a', A⟩ : support_condition B) ∉ σ.val.range} :=
begin
  have h₁ : #↥{a' ∈ litter_set a.fst | (⟨inl a', A⟩ : support_condition B) ∉ σ.val.domain} = #κ,
  { cases le_iff_eq_or_lt.mp (cardinal.mk_le_mk_of_subset (show
      {a' ∈ litter_set a.fst | (⟨inl a', A⟩ : support_condition B) ∉ σ.val.domain}
        ⊆ litter_set a.fst, by simp only [sep_subset])),
    { rw [h, mk_litter_set] },
    { rw mk_litter_set at h,
      cases (cardinal.add_lt_of_lt κ_regular.aleph_0_le hsmall h).ne _,
      rw [cardinal.mk_sep, cardinal.mk_sep],
      convert cardinal.mk_sum_compl _ using 1,
      rw mk_litter_set } },
  have h₂' : #↥{a' ∈ N.snd.val | (⟨inl a', A⟩ : support_condition B) ∈ σ.val.range} < #κ,
  { convert hsmall using 1,
    rw cardinal.eq,
    exact ⟨(cond_domain_range_equiv σ a A N ha).symm⟩ },
  rw h₁,
  cases le_iff_eq_or_lt.mp (cardinal.mk_le_mk_of_subset (show
    {a' ∈ N.snd.val | (⟨inl a', A⟩ : support_condition B) ∉ σ.val.range}
      ⊆ N.snd.val, by simp only [sep_subset])),
  { rw [h, N.snd.property.mk_eq_κ] },
  rw N.snd.property.mk_eq_κ at h,
  cases (cardinal.add_lt_of_lt κ_regular.aleph_0_le h₂' h).ne _,
  rw [cardinal.mk_sep, cardinal.mk_sep],
  convert cardinal.mk_sum_compl _ using 1,
  rw N.snd.property.mk_eq_κ,
end

private noncomputable def atom_map
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  ↥{a' ∈ litter_set a.fst | (⟨inl a', A⟩ : support_condition B) ∉ σ.val.domain} ≃
    ↥{a' ∈ N.snd.val | (⟨inl a', A⟩ : support_condition B) ∉ σ.val.range} :=
(cardinal.eq.mp $ equiv_not_mem_atom σ a A N hsmall ha).some

/-- The binary condition associated with this atom. -/
private noncomputable def atom_to_cond
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  {a' ∈ litter_set a.fst | (⟨inl a', A⟩ : support_condition B) ∉ σ.val.domain} →
    binary_condition B :=
λ b, (inl ⟨b, atom_map σ a A N hsmall ha b⟩, A)

lemma atom_to_cond_spec (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (b) : ∃ c, atom_to_cond σ a A N hsmall ha b = (inl (b, c), A) ∧
    (c ∈ N.snd.val ∧ (inl c, A) ∉ σ.val.range) :=
⟨atom_map σ a A N hsmall ha b, rfl, (atom_map σ a A N hsmall ha b).property⟩

lemma atom_to_cond_eq (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  {b c d e f C D} (hb : atom_to_cond σ a A N hsmall ha b = (inl (d, e), C))
  (hc : atom_to_cond σ a A N hsmall ha c = (inl (d, f), D)) :
  e = f ∧ C = D :=
begin
  simp only [atom_to_cond, prod.mk.inj_iff] at hb hc,
  obtain ⟨⟨h1, h2⟩, h3⟩ := hb,
  obtain ⟨⟨h1', h2'⟩, h3'⟩ := hc,
  rw [subtype.coe_inj.1 (h1.trans h1'.symm), h2'] at h2,
  exact ⟨h2.symm, h3.symm.trans h3'⟩,
end

lemma atom_to_cond_eq' (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  {b c d e f C D} (hb : atom_to_cond σ a A N hsmall ha b = (inl (e, d), C))
  (hc : atom_to_cond σ a A N hsmall ha c = (inl (f, d), D)) :
  e = f ∧ C = D :=
begin
  simp only [atom_to_cond, prod.mk.inj_iff] at hb hc,
  obtain ⟨⟨h1, h2⟩, h3⟩ := hb,
  obtain ⟨⟨h1', h2'⟩, h3'⟩ := hc,
  rw [← h2', subtype.coe_inj, embedding_like.apply_eq_iff_eq] at h2,
  exact ⟨h1.symm.trans ((subtype.coe_inj.2 h2).trans h1'), h3.symm.trans h3'⟩,
end

lemma exists_atom_to_cond (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  {c : atom} (hc₁ : c ∈ N.snd.val) (hc₂ : (inl c, A) ∉ σ.val.range) :
  ∃ d, atom_to_cond σ a A N hsmall ha d = (inl (d, c), A) :=
begin
  obtain ⟨d, hd⟩ : (⟨c, hc₁, hc₂⟩ : ↥{a' ∈ N.snd.val | _}) ∈ range (atom_map σ a A N hsmall ha),
  { rw equiv.range_eq_univ, exact mem_univ _ },
  refine ⟨d, _⟩,
  unfold atom_to_cond,
  rw hd,
  refl,
end

def new_atom_conds
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) : spec B := {
  carrier := set.range (atom_to_cond σ a A N hsmall ha),
  domain := set.range
    (λ b : {a' ∈ litter_set a.fst | (⟨inl a', A⟩ : support_condition B) ∉ σ.val.domain},
      (sum.inl b.val, A)),
  range := set.range
    (λ b : {a' ∈ litter_set a.fst | (⟨inl a', A⟩ : support_condition B) ∉ σ.val.domain},
      (sum.inl (atom_map σ a A N hsmall ha b), A)),
image_domain' := begin ext, simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and, mem_sep_eq, mem_image, set.mem_range, set_coe.exists,
  subtype.coe_mk, exists_prop], split, intro h, obtain ⟨x_1, ⟨⟨x,⟨h, h2⟩⟩, h3⟩⟩ := h, use x, split,
  exact h,rw ← h3, cases x_1,simp only [binary_condition.domain_mk, prod.mk.inj_iff],
  obtain ⟨c, hc⟩ := atom_to_cond_spec σ a A N hsmall ha ⟨x, _⟩, rw hc.left at h2,
  simp only [subtype.coe_mk, prod.mk.inj_iff] at h2, rw ← h2.1, rw h2.2, simp only [map_inl, eq_self_iff_true, and_self],
  intro h, obtain ⟨x_1, hx⟩ := h, have : x_1 ∈ ({a' ∈ litter_set a.fst | (inl a', A) ∉ σ.val.domain} : set atom),
  {simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and, mem_sep_eq], exact hx.left,},
  use (atom_to_cond σ a A N hsmall ha ⟨x_1, this⟩), use x_1, use hx.left,
  obtain ⟨c, hc⟩ := atom_to_cond_spec σ a A N hsmall ha ⟨x_1, this⟩, rw hc.left, rw ← hx.2,
  simp only [subtype.coe_mk, binary_condition.domain_mk, map_inl],  end,
  image_range' := begin ext, simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and, mem_sep_eq, mem_image, set.mem_range, set_coe.exists],
  split, intro h, obtain ⟨x_1, ⟨⟨a,⟨h, h2⟩⟩, h3⟩⟩ := h, use a, split,
  dsimp [(atom_to_cond)] at h2, cases x_1, simp only [binary_condition.range_mk] at h3, rw ← h3,
  simp only [prod.mk.inj_iff] at h2 ⊢,split, cases x_1_fst, simp only [map_inl] at h2 ⊢, rw ← h2.left,
  simp only, refl,simp only [map_inl] at h2, exfalso, exact h2.left, exact h2.right,
  exact h,
  intro h, obtain ⟨a, h, h2⟩ := h, cases x, simp only [prod.mk.inj_iff] at h2, cases x_fst,
  swap, exfalso, simp only at h2, exact h2.left, use (inl (a, x_fst), A), use a, use h,
  dsimp [(atom_to_cond)], simp only [(map_inl)] at h2,rw ← h2.left, refl,
  simp only [binary_condition.range_mk, map_inl, prod.mk.inj_iff, eq_self_iff_true, true_and],
  exact h2.right,
 end,
}

@[simp] lemma inl_mem_new_atom_conds
  {hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain}}
  {ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val}
  (b c : atom) (C : extended_index B) :
  (sum.inl (b, c), C) ∈ new_atom_conds σ a A N hsmall ha ↔
    C = A ∧ ∃ (hb₁ : b ∈ litter_set a.fst) (hb₂ : (inl b, A) ∉ σ.val.domain),
      c = atom_map σ a A N hsmall ha ⟨b, hb₁, hb₂⟩ :=
begin
  split,
  { rintro ⟨h₁, h₂⟩, cases h₂, refine ⟨rfl, h₁.prop.1, h₁.prop.2, _⟩, rw subtype.eta, refl, },
  { rintro ⟨rfl, hb₁, hb₂, rfl⟩, exact ⟨⟨b, hb₁, hb₂⟩, rfl⟩, },
end

lemma atom_union_one_to_one_forward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  spec.one_to_one_forward (σ.val ⊔ new_atom_conds σ a A N hsmall ha) :=
begin
  refine λ C, ⟨λ b p hp q hq, _, λ N' M hM M' hM', _⟩,
  { simp only [subtype.val_eq_coe, mem_sep_eq, mem_set_of_eq,
               mem_sup, set.mem_range, set_coe.exists, inl_mem_new_atom_conds] at hp hq,
    obtain hp | ⟨rfl, hxa, hxσ, rfl⟩ := hp; obtain hq | ⟨C_eq_A, hya, hyσ, hy⟩ := hq,
    { exact (σ.prop.forward.one_to_one C).atom b hp hq },
    { obtain ⟨c, hcond, hc, hcnin⟩ := atom_to_cond_spec σ a A N hsmall ha ⟨q, hya, hyσ⟩,
      cases C_eq_A, cases hy, cases hcond,
      rw spec.mem_range at hcnin,
      cases hcnin ⟨_, hp, rfl⟩ },
    { obtain ⟨c, hcond, hc, hcnin⟩ := atom_to_cond_spec σ a C N hsmall ha ⟨p, hxa, hxσ⟩,
      cases hcond,
      rw spec.mem_range at hcnin,
      cases hcnin ⟨_, hq, rfl⟩ },
    { rw [subtype.coe_inj, embedding_like.apply_eq_iff_eq] at hy,
      cases hy, refl, } },
  simp only [subtype.val_eq_coe, mem_sep_eq, mem_set_of_eq, mem_union_eq, spec.mem_range,
    set_coe.exists] at hM hM',
  obtain hM | ⟨x, ⟨hxa, hxσ⟩, hx⟩ := hM,
  obtain hM' | ⟨y, ⟨hya, hyσ⟩, hy⟩ := hM',
  { exact (σ.prop.forward.one_to_one C).near_litter N' hM hM' },
end

lemma atom_union_one_to_one_backward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  spec.one_to_one_forward (σ.val ⊔ new_atom_conds σ a A N hsmall ha)⁻¹ :=
begin
  refine λ C, ⟨λ b p hp q hq, _, λ N' M hM M' hM', _⟩,
  { simp only [subtype.val_eq_coe, mem_sep_eq, mem_set_of_eq, mem_sup, spec.mem_range,
      set_coe.exists, spec.mem_inv, inl_mem_new_atom_conds] at hp hq,
    dsimp only [has_inv.inv, has_involutive_inv.inv, sum.map_inl, prod.swap] at hp hq,
    obtain hp | ⟨p', hp⟩ := hp; obtain hq | ⟨q', hq⟩ := hq,
    { exact (σ.prop.backward.one_to_one C).atom b hp hq },
    { cases hq, cases q'.prop.2 (inl_mem_domain hp), },
    { cases hp, cases p'.prop.2 (inl_mem_domain hq), },
    { have : p' = q',
      { cases hp, unfold atom_to_cond at hq,
        simp only [subtype.val_eq_coe, prod.mk.inj_iff, eq_self_iff_true, and_true] at hq,
        exact subtype.coe_inj.mp hq.left.symm, },
      subst this, rw hp at hq, cases hq, refl, } },
  obtain hM | ⟨x, ⟨hxa, hxσ⟩, hx⟩ := hM,
  obtain hM' | ⟨y, ⟨hya, hyσ⟩, hy⟩ := hM',
  exact (σ.prop.backward.one_to_one C).near_litter N' hM hM',
end

lemma atom_union_atom_cond_forward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  ∀ L C, spec.atom_cond (σ.val ⊔ new_atom_conds σ a A N hsmall ha) L C :=
begin
  intros L C,
  obtain ⟨L', hL, atom_map, hin, himg⟩ | ⟨hL, hLsmall⟩ | ⟨L', hL, hLsmall, hmaps⟩ := σ.prop.forward.atom_cond L C,
  { exact spec.atom_cond.all L' (or.inl hL) atom_map (λ a ha, or.inl (hin a ha)) himg },
  { by_cases a.fst ≠ L ∨ A ≠ C,
    { refine spec.atom_cond.small_out _ _,
      { rw mem_domain,
        rintro ⟨⟨_ | ⟨N, M⟩, D⟩, hin | hin, hdom⟩; cases hdom,
        { exact hL (inr_mem_domain hin) },
        { unfold new_atom_conds atom_to_cond at hin,
          cases hin with _ hin, cases hin } },
      unfold small,
      have : {a_1 ∈ litter_set L | (inl a_1, C) ∈
        (σ.val ⊔ σ.new_atom_conds a A N hsmall ha).domain} =
        {a_1 ∈ litter_set L | (inl a_1, C) ∈ σ.val.domain} ∪ {a_1 ∈ litter_set L | (inl a_1, C) ∈
          binary_condition.domain '' (new_atom_conds σ a A N hsmall ha).carrier},
      { rw (new_atom_conds σ a A N hsmall ha).image_domain',
       ext,
        simp only [subtype.val_eq_coe, mem_sep_eq, mem_union_eq, mem_image, set.mem_range,
          set_coe.exists, mem_domain],
        split,
        { rintro ⟨hL, cond, h | h, h2⟩,
          { exact or.inl ⟨hL, ⟨cond, h, h2⟩⟩ },
          { exact or.inr ⟨hL, cond, h, h2⟩ } },
        { simp_rw mem_sup,
         rintro (⟨hL, cond, h, h2⟩ | ⟨hL, cond, h, h2⟩),
          { exact ⟨hL, cond, or.inl h, h2⟩ },
          { exact ⟨hL, cond, or.inr h, h2⟩ },
        },
      },
      have h2 : (new_atom_conds σ a A N hsmall ha).carrier = range (atom_to_cond σ a A N hsmall ha) := rfl,
      rw h2 at this,
      rw this,
      convert (cardinal.mk_union_le _ _).trans_lt (cardinal.add_lt_of_lt κ_regular.aleph_0_le
        hLsmall $ (cardinal.mk_emptyc _).trans_lt κ_regular.pos),
      simp only [binary_condition.domain, subtype.val_eq_coe, mem_sep_eq, mem_image, set.mem_range,
        set_coe.exists, prod.mk.inj_iff],
      cases h,
      { refine eq_empty_of_forall_not_mem _,
        rintro x ⟨hx, ⟨⟨x', y⟩ | _, b⟩, ⟨_, ⟨ha, _⟩, hb⟩, ⟨⟩⟩,
        simp only [atom_to_cond, sum.elim_inl, subtype.coe_mk, prod.mk.inj_iff] at hb,
        obtain ⟨⟨rfl, -⟩, -⟩ := hb,
        exact pairwise_disjoint_litter_set a.fst L h ⟨ha, hx⟩ },
      { refine eq_empty_of_forall_not_mem _,
        rintro x ⟨hL, ⟨b1, b2⟩, ⟨_, _, h1⟩, h2⟩,
        exact h ((congr_arg prod.snd h1).trans $ congr_arg prod.snd h2) } },
    { obtain ⟨rfl, rfl⟩ := and_iff_not_or_not.2 h,
      cases hL (inr_mem_domain ha), } },
  { by_cases a.fst ≠ L ∨ A ≠ C,
    { refine spec.atom_cond.small_in L' (or.inl hL) _ _,
      { unfold small,
        have : {a_1 ∈ litter_set L | (inl a_1, C) ∈
          (σ.val ⊔ σ.new_atom_conds a A N hsmall ha).domain} = {a_1 ∈ litter_set L | (inl a_1, C) ∈
              σ.val.domain} ∪ {a_1 ∈ litter_set L | (inl a_1, C) ∈
                binary_condition.domain '' (new_atom_conds σ a A N hsmall ha).carrier},
       { rw (new_atom_conds σ a A N hsmall ha).image_domain', ext,
          simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and, mem_sep_eq, domain_sup, mem_union_eq, mem_image, set.mem_range,
  set_coe.exists],
          split,
          { rintro ⟨hL, h | h⟩,
            { exact or.inl ⟨hL, h⟩ },
            { exact or.inr ⟨hL, h⟩ } },
          { rintro (⟨hL, h⟩ | ⟨hL, h⟩),
            { exact ⟨hL, or.inl h⟩ },
            { exact ⟨hL, or.inr h⟩ } } },
        have h2 : (new_atom_conds σ a A N hsmall ha).carrier = range (atom_to_cond σ a A N hsmall ha) := rfl,
        rw h2 at this,
        rw this,
        convert (cardinal.mk_union_le _ _).trans_lt (cardinal.add_lt_of_lt κ_regular.aleph_0_le
          hLsmall $ (cardinal.mk_emptyc _).trans_lt κ_regular.pos),
        simp only [binary_condition.domain, subtype.val_eq_coe, mem_sep_eq, mem_image,
          set.mem_range, set_coe.exists, prod.mk.inj_iff],
        cases h,
        { refine eq_empty_of_forall_not_mem _,
          rintro x ⟨hx, ⟨⟨x', y⟩ | _, b⟩, ⟨_, ⟨ha, _⟩, hb⟩, ⟨⟩⟩,
          { simp only [atom_to_cond, sum.elim_inl, subtype.coe_mk, prod.mk.inj_iff] at hb,
            obtain ⟨⟨rfl, -⟩, -⟩ := hb,
            exact pairwise_disjoint_litter_set a.fst L h ⟨ha, hx⟩ } },
        { refine eq_empty_of_forall_not_mem _,
          rintro x ⟨hL, ⟨b1, b2⟩, ⟨_, _, h1⟩, h2⟩,
        exact h ((congr_arg prod.snd h1).trans $ congr_arg prod.snd h2) } },
      { refine λ c d hcdu, or.rec (@hmaps c d) _ hcdu,
        rintro ⟨c, hcond⟩,
        cases hcond,
        simp only [ne.def, eq_self_iff_true, not_true, or_false] at h,
        refine ⟨λ hc, by cases pairwise_disjoint_litter_set _ _ h ⟨c.prop.1, hc⟩, _⟩,
        intro hL',
        cases litter_image_disjoint σ A ha hL h ⟨(atom_map σ a A N hsmall ha c).prop.1, hL'⟩ } },
    { classical,
      obtain ⟨rfl, rfl⟩ := and_iff_not_or_not.2 h,
      obtain rfl := (σ.prop.backward.one_to_one A).near_litter _ ha hL,
      refine spec.atom_cond.all N (or.inl ha)
        (λ x, dite ((inl x.val, A) ∈ σ.val.domain)
          (λ hx, atom_value σ A x hx)
          (λ hx, (atom_map σ a A N hsmall ha ⟨x.val, x.prop, hx⟩).val))
        (λ y hy, _) (ext $ λ x, ⟨λ hx, _, λ hx, _⟩),
      { by_cases (inl y, A) ∈ σ.val.domain,
        { rw dif_pos h,
          exact or.inl (atom_value_spec σ A y h) },
        { rw dif_neg h,
          exact or.inr ⟨⟨y, hy, h⟩, rfl⟩ } },
      { by_cases (inl x, A) ∈ σ.val.range,
        { rw spec.mem_range at h, obtain ⟨⟨⟨y, _⟩ | _, _⟩, hin, hxy⟩ := h; cases hxy,
          have hya : y ∈ litter_set a.fst := (hmaps hin).2 hx,
          use ⟨y, hya⟩,
          dsimp only,
          have : (inl y, A) ∈ σ.val.domain := inl_mem_domain hin,
          rw dif_pos this,
          exact (σ.prop.backward.one_to_one A).atom y
            (atom_value_spec σ A y $ inl_mem_domain hin) hin },
        { obtain ⟨d, hd⟩ := exists_atom_to_cond σ a A N hsmall ha hx h,
          use ⟨coe d, d.prop.1⟩,
          dsimp only,
          rw dif_neg d.prop.2,
          simpa only [atom_to_cond, subtype.coe_eta, prod.mk.inj_iff,
                      eq_self_iff_true, true_and, and_true] using hd } },
      { obtain ⟨y, rfl⟩ := hx,
        by_cases (inl y.val, A) ∈ σ.val.domain,
        { simp_rw dif_pos h,
          exact (hmaps $ atom_value_spec σ A y.val h).1 y.prop },
        { simp_rw dif_neg h,
          obtain ⟨c, hcy, hcN, hcnin⟩ := atom_to_cond_spec σ a A N hsmall ha ⟨y.val, y.prop, h⟩,
          simp only [atom_to_cond, prod.mk.inj_iff, eq_self_iff_true, true_and, and_true] at hcy,
          rw ← hcy at hcN,
          exact hcN } } } },
end

lemma atom_union_atom_cond_backward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) (L C) :
  spec.atom_cond (σ.val ⊔ new_atom_conds σ a A N hsmall ha)⁻¹ L C :=
begin
  obtain ⟨L', hL, atom_map, hin, himg⟩ | ⟨hL, hLsmall⟩ | ⟨L', hL, hLsmall, hmaps⟩ :=
    σ.prop.backward.atom_cond L C,
  { exact spec.atom_cond.all L' (or.inl hL) atom_map (λ a H, or.inl $ hin a H) himg },
  { by_cases N.fst = L,
    { subst h,
      by_cases A = C,
      { subst h,
        obtain ⟨_, hin, -⟩ := (σ.prop.backward.near_litter_cond N a.fst.to_near_litter A ha),
        cases hL (mem_domain.2 ⟨_, hin, rfl⟩) },
      { have : σ.new_atom_conds a A N hsmall ha =
            { carrier := range (atom_to_cond σ a A N hsmall ha),
              domain := _ , range := _,
              image_domain' := _, image_range' := _ } := rfl,
        rw this,
        clear this,
        refine spec.atom_cond.small_out (λ h, or.rec hL (λ hb, by cases hb.some_spec) h) _,
        rw spec.domain_inv at hLsmall ⊢,
        rw spec.range_sup,
        convert (cardinal.mk_union_le _ _).trans_lt (cardinal.add_lt_of_lt κ_regular.aleph_0_le
            hLsmall $ (cardinal.mk_emptyc _).trans_lt κ_regular.pos),
        ext,
        split,
        { rintro ⟨hxL, hxrge | hxrge⟩,
          { exact or.inl ⟨hxL, hxrge⟩ },
          exact or.inr (h (prod.eq_iff_fst_eq_snd_eq.1 hxrge.some_spec).2) },
        { rintro (⟨hxL, hxrge⟩ | h),
          { exact ⟨hxL, or.inl hxrge⟩ },
          cases h, } } },
    { by_cases A = C,
      { subst h,
        sorry },
      { refine spec.atom_cond.small_out _ _,
        { rintro (hnin | hnin),
          { exact hL hnin },
          exact h (prod.eq_iff_fst_eq_snd_eq.1 hnin.some_spec).2 },
        simp only [subtype.val_eq_coe, domain_inv, range_sup, mem_union_eq],
        convert (cardinal.mk_union_le _ _).trans_lt (cardinal.add_lt_of_lt κ_regular.aleph_0_le
            hLsmall $ (cardinal.mk_emptyc _).trans_lt κ_regular.pos),
        ext,
        split,
        { rintro ⟨hxL, hxrge | hxrge⟩,
          { exact or.inl ⟨hxL, hxrge⟩ },
          exact or.inr (h (prod.eq_iff_fst_eq_snd_eq.1 hxrge.some_spec).2) },
        { rintro (⟨hxL, hxrge⟩ | h),
          { exact ⟨hxL, or.inl hxrge⟩ },
          cases h, } } } },
  { by_cases A = C,
    { subst h,
      sorry},
    { refine spec.atom_cond.small_in L' (or.inl hL) _ _,
      { convert hLsmall using 2,
        refine funext (λ x, eq_iff_iff.2 ⟨λ hx, or.rec id _ hx, or.inl⟩),
        rintro ⟨_, ⟨⟩⟩,
        cases h rfl },
      { rintros a b (hab | ⟨_, ⟨⟩⟩),
        { exact hmaps hab },
        cases h rfl } } }
end

lemma atom_union_near_litter_cond_forward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  ∀ N₁ N₂ C,
    spec.near_litter_cond (σ.val ⊔ new_atom_conds σ a A N hsmall ha) N₁ N₂ C :=
begin
  rintro N₁ N₂ C (h | h),
  { obtain ⟨M, hM₁, sd, hsd₁, hsd₂⟩ := σ.property.forward.near_litter_cond N₁ N₂ C h,
    exact ⟨M, or.inl hM₁, sd, λ a, or.inl (hsd₁ a), hsd₂⟩ },
  obtain ⟨d, hd⟩ := h,
  cases hd,
end

lemma atom_union_near_litter_cond_backward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  ∀ N₁ N₂ C,
    spec.near_litter_cond (σ.val ⊔ new_atom_conds σ a A N hsmall ha)⁻¹ N₁ N₂ C :=
begin
  rintro N₁ N₂ C (h | h),
  { obtain ⟨M, hM₁, sd, hsd₁, hsd₂⟩ := σ.property.backward.near_litter_cond N₁ N₂ C h,
    exact ⟨M, or.inl hM₁, sd, λ a, or.inl (hsd₁ a), hsd₂⟩ },
  obtain ⟨d, hd⟩ := h,
  cases hd,
end

lemma atom_union_non_flexible_cond_forward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  spec.non_flexible_cond B (σ.val ⊔ new_atom_conds σ a A N hsmall ha) :=
begin
  rintro β δ γ hγ hδ hγδ N₁ C t (ht | ht) ρ hρ,
  { exact σ.property.forward.non_flexible_cond hγ hδ hγδ N₁ C t ht ρ
      (hρ.mono $ subset_union_left _ _) },
  obtain ⟨d, hd⟩ := ht,
  cases hd,
end

lemma atom_union_non_flexible_cond_backward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  spec.non_flexible_cond B (σ.val ⊔ new_atom_conds σ a A N hsmall ha)⁻¹ :=
begin
  rintro β δ γ hγ hδ hγδ N₁ C t (ht | ⟨d, ⟨⟩⟩) ρ hρ,
  exact σ.property.backward.non_flexible_cond hγ hδ hγδ N₁ C t ht ρ
      (hρ.mono $ subset_union_left _ _),
end

lemma atom_union_support_closed_forward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  (σ.val ⊔ new_atom_conds σ a A N hsmall ha).domain.support_closed B :=
begin
  intros β δ γ hγ hδ hγδ C t ht,
  rw spec.domain_sup at ht ⊢,
  rw unary_spec.lower_union,
  obtain (ht | ⟨_, ⟨_, ⟨⟩⟩, ⟨⟩⟩) := ht,
  exact (σ.property.forward.support_closed hγ hδ hγδ C t ht).mono (subset_union_left _ _),
end

lemma atom_union_support_closed_backward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  (σ.val ⊔ new_atom_conds σ a A N hsmall ha).range.support_closed B :=
begin
  intros β δ γ hγ hδ hγδ C t ht,
  rw spec.range_sup at ht ⊢,
  rw unary_spec.lower_union,
  obtain (ht | ⟨_, ⟨_, ⟨⟩⟩, ⟨⟩⟩) := ht,
  convert (σ.property.backward.support_closed hγ hδ hγδ C t $ by rwa spec.domain_inv).mono
    (subset_union_left _ _),
end

lemma atom_union_flexible_cond
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) (C) :
  spec.flexible_cond B (σ.val ⊔ new_atom_conds σ a A N hsmall ha) C :=
begin
  obtain (⟨hdom, hrge⟩ | ⟨hdom, hrge⟩) := σ.property.flexible_cond C,
  { refine spec.flexible_cond.co_large _ _,
    { convert hdom,
      ext L,
      rw spec.domain_sup,
      refine and_congr_right' ⟨λ hC h, hC $ mem_union_left _ h, λ hC, _⟩,
      rintro (h | ⟨_, ⟨_, ⟨⟩⟩, ⟨⟩⟩),
      exact hC h },
    { convert hrge,
      ext L,
      rw spec.range_sup,
      refine and_congr_right' ⟨λ hC h, hC $ mem_union_left _ h, λ hC, _⟩,
      rintro (h | ⟨_, ⟨_, ⟨⟩⟩, ⟨⟩⟩),
      exact hC h } },
  { refine spec.flexible_cond.all (λ L hL, _) (λ L hL, _),
    { rw spec.domain_sup,
      exact or.inl (hdom L hL) },
    { rw spec.range_sup,
      exact or.inl (hrge L hL) } }
end

/-- When we add the provided atoms from the atom map, we preserve allowability.

This lemma is going to be work, and we have three others just like it later.
Is there a way to unify all of the cases somehow, or at least avoid duplicating code?
At the moment, I can't see a way to use any less than eleven lemmas here, since the symmetry is
broken. -/
lemma atom_union_allowable
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  spec.allowable B (σ.val ⊔ new_atom_conds σ a A N hsmall ha) :=
{ forward :=
  { one_to_one := atom_union_one_to_one_forward σ a A N hsmall ha,
    atom_cond := atom_union_atom_cond_forward σ a A N hsmall ha,
    near_litter_cond := atom_union_near_litter_cond_forward σ a A N hsmall ha,
    non_flexible_cond := atom_union_non_flexible_cond_forward σ a A N hsmall ha,
    support_closed := atom_union_support_closed_forward σ a A N hsmall ha },
  backward :=
  { one_to_one := atom_union_one_to_one_backward σ a A N hsmall ha,
    atom_cond := atom_union_atom_cond_backward σ a A N hsmall ha,
    near_litter_cond := atom_union_near_litter_cond_backward σ a A N hsmall ha,
    non_flexible_cond := atom_union_non_flexible_cond_backward σ a A N hsmall ha,
    support_closed := by { rw spec.domain_inv,
      exact atom_union_support_closed_backward σ a A N hsmall ha } },
  flexible_cond := atom_union_flexible_cond σ a A N hsmall ha }

lemma atom_union_all_atoms_domain
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) (b₁ b₂ : atom)
  (L : litter) (hb₁ : b₁ ∈ litter_set L) (C : extended_index B)
  (hσ : (⟨inl ⟨b₁, b₂⟩, C⟩ : binary_condition B) ∈
    range (atom_to_cond σ a A N hsmall ha)) :
  ∀ c ∈ litter_set L, ∃ d, (⟨inl ⟨c, d⟩, C⟩ : binary_condition B) ∈
    σ.val ⊔ new_atom_conds σ a A N hsmall ha :=
begin
  intros c hc,
  by_cases (⟨inl c, C⟩ : support_condition B) ∈ σ.val.domain,
  { exact ⟨atom_value σ C c h, or.inl (atom_value_spec σ C c h)⟩ },
  obtain ⟨d, hd⟩ := hσ,
  have hd : b₁ = d,
  { unfold atom_to_cond at hd,
    have hd' := congr_arg prod.fst hd, have := congr_arg prod.fst (inl.inj hd'),
    cases this, refl },
  subst hd,
  have hL : L = a.fst := by { cases hb₁, obtain ⟨d, hd₁, hd₂⟩ := d, exact hd₁ },
  subst hL,
  have hC : A = C := by { cases hd, refl },
  subst hC,
  generalize he : atom_to_cond σ a A N hsmall ha ⟨c, hc, h⟩ = e,
  obtain ⟨⟨e₁, e₂⟩ | Ns, E⟩ := e,
  { refine ⟨e₂, or.inr ⟨⟨c, hc, h⟩, _⟩⟩,
    cases he, exact he },
  { unfold atom_to_cond at he, simpa only [prod.mk.inj_iff, false_and] using he }
end

/-- The image of an element of a near-litter lies in the resulting near-litter. -/
lemma atom_union_mem
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (b₁ b₂ : atom) (C : extended_index B)
  (hσ : (⟨inl ⟨b₁, b₂⟩, C⟩ : binary_condition B) ∈
    range (atom_to_cond σ a A N hsmall ha)) :
  b₂ ∈ (N.snd : set atom) :=
begin
  obtain ⟨d, hd⟩ := hσ,
  have : b₁ = d,
  { unfold atom_to_cond at hd,
    have hd' := congr_arg prod.fst hd, have := congr_arg prod.fst (inl.inj hd'),
    cases this, refl },
  subst this,
  obtain ⟨N', h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N', h₁, h₂, h₃⟩ :=
    atom_union_atom_cond_forward σ a A N hsmall ha a.fst A,
  { obtain this | ⟨e, he⟩ := h₂ d d.property.left,
    { cases d.property.right (inl_mem_domain this) },
    rw (atom_to_cond_eq σ a A N hsmall ha hd he).left,
    rw (atom_union_one_to_one_backward σ a A N hsmall ha A).near_litter
      a.fst.to_near_litter (or.inl ha) h₁,
    exact ((range_eq_iff _ _).mp h₃.symm).left _ },
  { cases h₁ _,
    rw spec.domain_sup,
    exact or.inl (inr_mem_domain ha) },
  { have : A = C,
    { cases hd, refl },
    subst this,
    have := (h₃ (or.inr ⟨d, hd⟩)).1 d.property.left,
    rwa (atom_union_one_to_one_backward σ a A N hsmall ha A).near_litter
       a.fst.to_near_litter (or.inl ha) h₁
  }
end

/-- The atom map only ever maps to the intersection of `N` with its corresponding litter, `N.fst`.
In particular, we prove that if some atom `c` lies in the litter we're mapping to, it lies in the
precise near-litter we are mapping to as well. -/
lemma atom_union_mem'
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val)
  (b₁ b₂ : atom) (C : extended_index B)
  (hσ : (⟨inl ⟨b₁, b₂⟩, C⟩ : binary_condition B) ∈ range (atom_to_cond σ a A N hsmall ha))
  (c : atom) (hc₁ : c ∈ litter_set b₂.fst) (hc₂ : (inl c, A) ∉ σ.val.range) :
  c ∈ (N.snd : set atom) :=
begin
  contrapose hc₂,
  rw not_not_mem,

  suffices hb₂ : b₂.fst = N.fst,
  { rw hb₂ at hc₁,
    obtain ⟨M, hM, symm_diff, hS₁, hS₂⟩ :=
      σ.property.backward.near_litter_cond N a.fst.to_near_litter A ha,
    exact inl_mem_domain (hS₁ ⟨c, or.inl ⟨hc₁, hc₂⟩⟩), },

  obtain ⟨d, hd⟩ := hσ,
  have : b₁ = d,
  { unfold atom_to_cond at hd,
    have hd' := congr_arg prod.fst hd, have := congr_arg prod.fst (inl.inj hd'),
    cases this, refl },
  subst this,

  obtain ⟨M, hM, symm_diff, hS₁, hS₂⟩ :=
    σ.property.backward.near_litter_cond N a.fst.to_near_litter A ha,
  by_contradiction hb₂,
  have := hS₁ ⟨b₂, or.inr ⟨atom_union_mem σ a A N hsmall ha d b₂ C ⟨d, hd⟩, hb₂⟩⟩,
  obtain ⟨e, he₁, he₂, he₃⟩ := atom_to_cond_spec σ a A N hsmall ha d,
  rw hd at he₁,
  cases he₁,
  exact he₃ (inl_mem_domain this),
end

lemma atom_union_all_atoms_range
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) (b₁ b₂ : atom)
  (L : litter) (hb₂ : b₂ ∈ litter_set L) (C : extended_index B)
  (hσ : (⟨inl ⟨b₁, b₂⟩, C⟩ : binary_condition B) ∈
    range (atom_to_cond σ a A N hsmall ha)) :
  ∀ c ∈ litter_set L, ∃ d, (⟨inl ⟨d, c⟩, C⟩ : binary_condition B) ∈
    σ.val ⊔ new_atom_conds σ a A N hsmall ha :=
begin
  have b₂_mem := atom_union_mem σ a A N hsmall ha _ _ _ hσ,
  obtain ⟨d, hd⟩ := hσ,
  have : b₁ = d,
  { unfold atom_to_cond at hd,
    have hd' := congr_arg prod.fst hd, have := congr_arg prod.fst (inl.inj hd'),
    cases this, refl },
  subst this,
  have : A = C,
  { cases hd, refl },
  subst this,
  have : N.fst = L,
  { cases hb₂,
    by_contradiction,
    obtain ⟨M, hM, symm_diff, hS₁, hS₂⟩ :=
      σ.property.backward.near_litter_cond N a.fst.to_near_litter A ‹_›,
    rw spec.inr_mem_inv at hM,
    have mem_symm_diff : b₂ ∈ litter_set N.fst ∆ N.snd := or.inr ⟨b₂_mem, ne.symm h⟩,
    have hS₁' := hS₁ ⟨b₂, mem_symm_diff⟩,
    rw spec.inl_mem_inv at hS₁',
    have : symm_diff ⟨b₂, mem_symm_diff⟩ = d :=
      (atom_union_one_to_one_forward σ a A N hsmall ha A).atom b₂
        (or.inl hS₁') (or.inr ⟨_, hd⟩),
    refine d.property.right _,
    rw [subtype.val_eq_coe, ← this],
    exact inl_mem_domain hS₁', },
  subst this,

  intros c hc,
  by_cases (⟨inl c, A⟩ : support_condition B) ∈ σ.val.range,
  { rw spec.mem_range at h, obtain ⟨⟨⟨d₁, d₂⟩ | Ns, D⟩, hc₁, hc₂⟩ := h; cases hc₂,
    exact ⟨d₁, or.inl hc₁⟩ },
  have : c ∈ N.snd.val,
  { convert atom_union_mem' σ a A N hsmall ha d b₂ A ⟨d, hd⟩ _ _ h, convert hc },
  refine ⟨(atom_map σ a A N hsmall ha).inv_fun ⟨c, this, h⟩,
    or.inr ⟨(atom_map σ a A N hsmall ha).inv_fun ⟨c, this, h⟩, _⟩⟩,
  unfold atom_to_cond,
  rw ← equiv.to_fun_as_coe,
  rw equiv.right_inv _,
  refl,
end

/-- When we add the atoms from the atom map, the resulting permutation "carefully extends" `σ`.
The atom conditions hold because `σ` is allowable and the `near_litter_cond` is satisfied - in
particular, the atoms in the symmetric difference between `N` and `N.fst.to_near_litter` are already
given in `σ`, so do not appear in the `atom_to_cond` map. -/
lemma le_atom_union
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ σ.val.domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ σ.val) :
  σ ≤ ⟨σ.val ⊔ new_atom_conds σ a A N hsmall ha, atom_union_allowable σ a A N hsmall ha⟩ := {
  le := subset_union_left _ _,
  all_flex_domain := begin
    intros L N' C hN' hσ₁ hσ₂,
    cases mem_or_mem_of_mem_union hσ₂,
    { cases hσ₁ h },
    simpa only [new_atom_conds, atom_to_cond, spec.coe_mk, prod.mk.inj_iff, exists_false,
      set.mem_range, false_and] using h,
  end,
  all_flex_range := begin
    intros L N' C hN' hσ₁ hσ₂,
    cases mem_or_mem_of_mem_union hσ₂,
    { cases hσ₁ h },
    simpa only [new_atom_conds, atom_to_cond, spec.coe_mk, prod.mk.inj_iff, exists_false,
      set.mem_range, false_and] using h,
  end,
  all_atoms_domain := begin
    intros b₁ b₂ L hb₁ C hC₁ hC₂ c hc',
    cases hC₂,
    { cases hC₁ hC₂ },
    exact atom_union_all_atoms_domain σ a A N hsmall ha b₁ b₂ L hb₁ C hC₂ c hc',
  end,
  all_atoms_range := begin
    intros b₁ b₂ L hb₁ C hC₁ hC₂ c hc',
    cases hC₂,
    { cases hC₁ hC₂ },
    exact atom_union_all_atoms_range σ a A N hsmall ha b₁ b₂ L hb₁ C hC₂ c hc',
  end,
}

/-- If everything that constrains an atom lies in `σ`, we can add the atom to `σ`, giving a new
allowable partial permutation `ρ ≥ σ`. -/
lemma exists_ge_atom (hσ : ∀ c, c ≺ (⟨inl a, A⟩ : support_condition B) → c ∈ σ.val.domain) :
  ∃ ρ, σ ≤ ρ ∧ (⟨inl a, A⟩ : support_condition B) ∈ ρ.val.domain :=
begin
  by_cases haσ : (⟨inl a, A⟩ : support_condition B) ∈ σ.val.domain,
  { exact ⟨σ, le_rfl, haσ⟩ },
  have h := hσ (⟨inr a.fst.to_near_litter, A⟩ : support_condition B)
    (constrains.mem_litter a.fst a rfl _),
  rw mem_domain at h,
  obtain ⟨⟨_ | ⟨_, N⟩, A⟩, hc₁, hc₂⟩ := h; cases hc₂,
  sorry
  -- obtain hsmall | ⟨N', atom_map, hσ₁, hσ₂, hN'⟩ := σ.property.forward.atom_cond a.fst A,
  -- swap, { cases haσ ⟨_, hσ₂ a rfl, rfl⟩ },
  -- have := equiv_not_mem_atom σ a A N hsmall hc₁,
  -- exact ⟨_, le_atom_union σ a A N hc₁ hsmall hc₁, _, mem_union_right _ ⟨⟨a, rfl, haσ⟩, rfl⟩, rfl⟩,
end

end allowable_partial_perm
end con_nf
