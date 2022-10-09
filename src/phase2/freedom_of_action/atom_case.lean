import phase2.freedom_of_action.constrains
import phase2.freedom_of_action.values
import phase2.freedom_of_action.zorn

/-!
# Maximality proof: Atom case

Suppose that we have an atom whose litter is specified in `σ`. We want to extend `σ` such that all
of the atoms in this litter are now specified. To do this, we construct an arbitrary bijection of
the unassigned atoms in the litter in the domain with the unassigned atoms in the litter's image.
-/

open cardinal function set sum
open_locale cardinal

universe u

namespace con_nf
namespace allowable_spec

variables [params.{u}]

open struct_perm spec

variables {α : Λ} [phase_2_core_assumptions α] [phase_2_positioned_assumptions α]
  [typed_positions.{}] [phase_2_assumptions α] {B : le_index α}

variables (σ : allowable_spec B) (a : atom) (A : extended_index B) (N : near_litter)

lemma atom_value_inj_range (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) :
  range (λ b : {b : atom | b ∈ litter_set a.fst ∧ (inl b, A) ∈ (σ : spec B).domain},
    (atom_value_inj σ A) ⟨b.val, b.prop.right⟩) =
  {b : atom | b ∈ (N.2 : set atom) ∧ (inl b, A) ∈ (σ : spec B).range} :=
begin
  rw range_eq_iff,
  refine ⟨λ c, ⟨_, _⟩, λ c hc, _⟩,
  { dsimp only [atom_value_inj, subtype.coe_mk, embedding.coe_fn_mk],
    have := atom_value_spec σ A c c.prop.right,
    obtain ⟨N', h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N', hN, h₁, h₂⟩ :=
      σ.prop.forward.atom_cond a.fst A,
    { cases (σ.prop.backward.one_to_one A).near_litter _ ha h₁,
      rw [h₃, set.mem_range],
      refine ⟨⟨c, c.2.1⟩, _⟩,
      rw (σ.prop.backward.one_to_one A).atom _ (h₂ c c.2.1) this,
      refl },
    { rw mem_domain at h₁, cases h₁ ⟨_, ha, rfl⟩ },
    { cases (σ.prop.backward.one_to_one A).near_litter _ ha hN,
      exact (h₂ this).mp c.prop.left } },
  { exact atom_value_spec_range σ A c c.prop.right },
  obtain ⟨hc, hc'⟩ := hc,
  rw spec.mem_range at hc',
  obtain ⟨⟨⟨a₁, a₂⟩ | Ns, C⟩, hd₁, hd₂⟩ := hc'; cases hd₂,
  refine ⟨⟨a₁, _, inl_mem_domain hd₁⟩, (σ.prop.backward.one_to_one A).atom a₁
    (atom_value_spec σ A a₁ (inl_mem_domain hd₁)) hd₁⟩,
  obtain ⟨M, hM, s, hs₁, hs₂⟩ := σ.prop.backward.near_litter_cond _ _ _ ha,
  dsimp only at hs₂,
  by_cases c ∈ litter_set N.fst,
  { obtain ⟨N', h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N', hN, h₁, h₂⟩ :=
      σ.prop.backward.atom_cond N.fst A,
    { cases (σ.prop.forward.one_to_one A).near_litter _ h₁ hM,
      cases (σ.prop.forward.one_to_one A).atom _ (h₂ c h) hd₁,
      rw [hs₂, h₃],
      refine or.inl ⟨⟨_, rfl⟩, _⟩,
      rintro ⟨d, hd⟩,
      have := hs₁ d,
      rw hd at this,
      cases (σ.prop.backward.one_to_one A).atom _ this hd₁,
      obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := d.prop,
      { exact h₂ hc },
      { exact h₂ h } },
    { rw mem_domain at h₁, cases h₁ ⟨_, hM, rfl⟩ },
    { cases (σ.prop.forward.one_to_one A).near_litter _ hM hN,
      rw hs₂,
      refine or.inl ⟨(h₂ hd₁).mp h, _⟩,
      rintro ⟨d, hd⟩,
      have := hs₁ d,
      rw hd at this,
      cases (σ.prop.backward.one_to_one A).atom _ this hd₁,
      obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := d.prop,
      { exact h₂ hc },
      { exact h₂ h } } },
  have : a₁ = _ := (σ.prop.forward.one_to_one A).atom _ hd₁ (hs₁ ⟨c, or.inr ⟨hc, h⟩⟩),
  subst this,
  rw hs₂,
  refine or.inr ⟨⟨_, rfl⟩, _⟩,
  obtain ⟨N', h₁, atom_map, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨N', hN, h₁, h₂⟩ := σ.2.backward.atom_cond N.fst A,
  { cases (σ.prop.forward.one_to_one A).near_litter _ h₁ hM,
    rw h₃,
    rintro ⟨d, hd⟩,
    have := h₂ d d.prop,
    rw [subtype.coe_eta, hd] at this,
    cases (σ.prop.backward.one_to_one A).atom _ hd₁ this,
    exact h d.prop },
  { rw mem_domain at h₁, cases h₁ ⟨_, hM, rfl⟩ },
  { cases (σ.prop.forward.one_to_one A).near_litter _ hM hN,
    rw ← h₂ hd₁,
    exact h }
end

/-- The domain and range of an allowable partial permutation, restricted to a given litter, are
equivalent. The equivalence produced by this function is induced by the allowable partial
permutation itself, so if this function maps an atom `a` to `b`, we have `π_A(a) = b` for all
allowable `π` satisfying `σ`. -/
noncomputable def cond_domain_range_equiv (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) :
  {b | b ∈ litter_set a.fst ∧ (inl b, A) ∈ (σ : spec B).domain} ≃
  {b | b ∈ (N.2 : set atom) ∧ (inl b, A) ∈ (σ : spec B).range} :=
begin
  convert equiv.of_injective (λ (b : {b | b ∈ litter_set a.fst ∧ (inl b, A) ∈ (σ : spec B).domain}),
    atom_value_inj σ A ⟨b.val, b.prop.right⟩) _ using 2,
  { symmetry, exact atom_value_inj_range σ a A N ha },
  { intros b₁ b₂ hb,
    simpa only [subtype.mk_eq_mk, subtype.val_inj] using
      @function.embedding.injective _ _ (atom_value_inj σ A)
        ⟨b₁.val, b₁.prop.right⟩ ⟨b₂.val, b₂.prop.right⟩ hb },
end

/-- If we are in the "small" case (although this holds in both cases), the amount of atoms in a
given litter whose positions we have not defined so far is the same as the amount of atoms in the
resulting near-litter which are not the image of anything under `σ`. This means we can construct an
arbitrary bijection of these remaining atoms, "filling out" the specification to define the
permutation of all atoms in the litter to the atoms in the resulting near-litter. -/
lemma equiv_not_mem_atom (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) :
  #↥{a' ∈ litter_set a.fst | (⟨inl a', A⟩ : support_condition B) ∉ (σ : spec B).domain} =
    #↥{a' ∈ (N.2 : set atom) | (⟨inl a', A⟩ : support_condition B) ∉ (σ : spec B).range} :=
begin
  have h₁ : #↥{a' ∈ litter_set a.fst | (⟨inl a', A⟩ : support_condition B) ∉ (σ : spec B).domain} = #κ,
  { cases le_iff_eq_or_lt.mp (mk_le_mk_of_subset (show
      {a' ∈ litter_set a.fst | (⟨inl a', A⟩ : support_condition B) ∉ (σ : spec B).domain}
        ⊆ litter_set a.fst, by simp only [sep_subset])),
    { rw [h, mk_litter_set] },
    { rw mk_litter_set at h,
      cases (add_lt_of_lt κ_regular.aleph_0_le hsmall h).ne _,
      rw [mk_sep, mk_sep],
      convert mk_sum_compl _ using 1,
      rw mk_litter_set } },
  have h₂' : #↥{a' ∈ (N.2 : set atom) | (⟨inl a', A⟩ : support_condition B) ∈ (σ : spec B).range} < #κ,
  { convert hsmall using 1,
    exact cardinal.eq.2 ⟨(cond_domain_range_equiv σ a A N ha).symm⟩ },
  rw h₁,
  cases (mk_le_mk_of_subset (show
    {a' ∈ (N.2 : set atom) | (⟨inl a', A⟩ : support_condition B) ∉ (σ : spec B).range}
      ⊆ (N.2 : set atom), by simp only [sep_subset])).eq_or_lt,
  { rw [h, N.snd.prop.mk_eq_κ] },
  rw N.snd.prop.mk_eq_κ at h,
  cases (add_lt_of_lt κ_regular.aleph_0_le h₂' h).ne _,
  rw [mk_sep, mk_sep],
  convert mk_sum_compl _ using 1,
  rw N.snd.prop.mk_eq_κ,
end

private noncomputable def atom_map
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) :
  ↥{a' ∈ litter_set a.fst | (⟨inl a', A⟩ : support_condition B) ∉ (σ : spec B).domain} ≃
    ↥{a' ∈ (N.2 : set atom) | (⟨inl a', A⟩ : support_condition B) ∉ (σ : spec B).range} :=
(cardinal.eq.mp $ equiv_not_mem_atom σ a A N hsmall ha).some

/-- The binary condition associated with this atom. -/
private noncomputable def atom_to_cond
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) :
  {a' ∈ litter_set a.fst | (⟨inl a', A⟩ : support_condition B) ∉ (σ : spec B).domain} →
    binary_condition B :=
λ b, (inl ⟨b, atom_map σ a A N hsmall ha b⟩, A)


lemma atom_to_cond_spec (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B))
  (b) : ∃ c, atom_to_cond σ a A N hsmall ha b = (inl (b, c), A) ∧
    (c ∈ (N.2 : set atom) ∧ (inl c, A) ∉ (σ : spec B).range) :=
⟨atom_map σ a A N hsmall ha b, rfl, (atom_map σ a A N hsmall ha b).prop⟩

lemma atom_to_cond_eq (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B))
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

lemma atom_to_cond_eq' (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B))
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

lemma exists_atom_to_cond (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B))
  {c : atom} (hc₁ : c ∈ (N.2 : set atom)) (hc₂ : (inl c, A) ∉ (σ : spec B).range) :
  ∃ d, atom_to_cond σ a A N hsmall ha d = (inl (d, c), A) :=
begin
  obtain ⟨d, hd⟩ : (⟨c, hc₁, hc₂⟩ : ↥{a' ∈ (N.2 : set atom) | _}) ∈ range (atom_map σ a A N hsmall ha),
  { rw equiv.range_eq_univ, exact mem_univ _ },
  refine ⟨d, _⟩,
  unfold atom_to_cond,
  rw hd,
  refl,
end

def new_atom_conds (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) : spec B :=
{ carrier := set.range (atom_to_cond σ a A N hsmall ha),
  domain := set.range
    (λ b : {a' ∈ litter_set a.fst | (⟨inl a', A⟩ : support_condition B) ∉ (σ : spec B).domain},
      (sum.inl b.val, A)),
  range := set.range
    (λ b : {a' ∈ litter_set a.fst | (⟨inl a', A⟩ : support_condition B) ∉ (σ : spec B).domain},
      (sum.inl (atom_map σ a A N hsmall ha b), A)),
  image_domain' := begin
    ext,
    simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and, mem_sep_iff, mem_image,
      set.mem_range, set_coe.exists, subtype.coe_mk, exists_prop],
    split,
    { rintro ⟨x_1, ⟨x, h, h2⟩, h3⟩,
      refine ⟨x, h, _⟩,
      rw ← h3,
      cases x_1,
      simp only [binary_condition.domain_mk, prod.mk.inj_iff],
      obtain ⟨c, hc⟩ := atom_to_cond_spec σ a A N hsmall ha ⟨x, _⟩,
      rw hc.left at h2,
      simp only [subtype.coe_mk, prod.mk.inj_iff] at h2,
      rw [←h2.1, h2.2],
      simp only [map_inl, eq_self_iff_true, and_self] },
    rintro ⟨x_1, hx⟩,
    have : x_1 ∈ ({a' ∈ litter_set a.fst | (inl a', A) ∉ (σ : spec B).domain} : set atom),
    { simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and, mem_sep_iff], exact hx.left },
    refine ⟨atom_to_cond σ a A N hsmall ha ⟨x_1, this⟩, ⟨x_1, hx.left, _⟩, _⟩,
    obtain ⟨c, hc⟩ := atom_to_cond_spec σ a A N hsmall ha ⟨x_1, this⟩,
    rw hc.left,
    rw ← hx.2,
    simp only [subtype.coe_mk, binary_condition.domain_mk, map_inl],
  end,
  image_range' := begin ext, simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and, mem_sep_iff, mem_image, set.mem_range, set_coe.exists],
  split, intro h, obtain ⟨x_1, ⟨⟨a,⟨h, h2⟩⟩, h3⟩⟩ := h, use a, split,
  dsimp [atom_to_cond] at h2,
  cases x_1,
  simp only [binary_condition.range_mk] at h3,
  rw ← h3,
  simp only [prod.mk.inj_iff] at h2 ⊢,
  split,
  cases x_1_fst,
  simp only [map_inl] at h2 ⊢,
  rw ← h2.left,
  simp only,
  refl,
  simp only [map_inl] at h2,
  { cases h2.left} ,
  exact h2.right,
  exact h,
  intro h,
  obtain ⟨a, h, h2⟩ := h, cases x, simp only [prod.mk.inj_iff] at h2, cases x_fst,
  swap, simp only at h2, cases h2.left, refine ⟨(inl (a, x_fst), A), a, h, _⟩,
  dsimp [atom_to_cond],
  simp only [map_inl] at h2,
  rw ← h2.left,
  refl,
  simp only [binary_condition.range_mk, map_inl, prod.mk.inj_iff, eq_self_iff_true, true_and],
  exact h2.right,
 end }

@[simp] lemma inl_mem_new_atom_conds
  {hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain}}
  {ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)}
  (b c : atom) (C : extended_index B) :
  (sum.inl (b, c), C) ∈ new_atom_conds σ a A N hsmall ha ↔
    C = A ∧ ∃ (hb₁ : b ∈ litter_set a.fst) (hb₂ : (inl b, A) ∉ (σ : spec B).domain),
      c = atom_map σ a A N hsmall ha ⟨b, hb₁, hb₂⟩ :=
begin
  split,
  { rintro ⟨h₁, h₂⟩, cases h₂, refine ⟨rfl, h₁.prop.1, h₁.prop.2, _⟩, rw subtype.eta, refl },
  { rintro ⟨rfl, hb₁, hb₂, rfl⟩, exact ⟨⟨b, hb₁, hb₂⟩, rfl⟩ },
end

@[simp] lemma inr_mem_new_atom_conds
  {hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain}}
  {ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)}
  (l1 l2 : near_litter) (C : extended_index B) :
  (sum.inr (l1, l2), C) ∈ new_atom_conds σ a A N hsmall ha ↔ false :=
begin
  split,
  { rintro ⟨h₁, h₂⟩, cases h₂},
  { rintro ⟨rfl, hb₁, hb₂, rfl⟩},
end


lemma atom_union_one_to_one_forward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) :
  spec.one_to_one_forward ((σ : spec B) ⊔ new_atom_conds σ a A N hsmall ha) :=
begin
  refine λ C, ⟨λ b p hp q hq, _, λ N' M hM M' hM', _⟩,
  { simp only [subtype.val_eq_coe, mem_sep_iff, mem_set_of_eq,
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
      cases hy,
      refl } },
  simp only [subtype.val_eq_coe, mem_sep_iff, mem_set_of_eq, mem_union, spec.mem_range,
    set_coe.exists] at hM hM',
  obtain hM | ⟨x, ⟨hxa, hxσ⟩, hx⟩ := hM,
  obtain hM' | ⟨y, ⟨hya, hyσ⟩, hy⟩ := hM',
  { exact (σ.prop.forward.one_to_one C).near_litter N' hM hM' },
end

lemma atom_union_one_to_one_backward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) :
  spec.one_to_one_forward ((σ : spec B) ⊔ new_atom_conds σ a A N hsmall ha)⁻¹ :=
begin
  refine λ C, ⟨λ b p hp q hq, _, λ N' M hM M' hM', _⟩,
  { simp only [subtype.val_eq_coe, mem_sep_iff, mem_set_of_eq, mem_sup, spec.mem_range,
      set_coe.exists, spec.mem_inv, inl_mem_new_atom_conds] at hp hq,
    dsimp only [has_inv.inv, has_involutive_inv.inv, sum.map_inl, prod.swap] at hp hq,
    obtain hp | ⟨p', hp⟩ := hp; obtain hq | ⟨q', hq⟩ := hq,
    { exact (σ.prop.backward.one_to_one C).atom b hp hq },
    { cases hq, cases q'.prop.2 (inl_mem_domain hp) },
    { cases hp, cases p'.prop.2 (inl_mem_domain hq) },
    { have : p' = q',
      { cases hp, unfold atom_to_cond at hq,
        simp only [subtype.val_eq_coe, prod.mk.inj_iff, eq_self_iff_true, and_true] at hq,
        exact subtype.coe_inj.mp hq.left.symm },
      subst this, rw hp at hq, cases hq, refl } },
  obtain hM | ⟨x, ⟨hxa, hxσ⟩, hx⟩ := hM,
  obtain hM' | ⟨y, ⟨hya, hyσ⟩, hy⟩ := hM',
  exact (σ.prop.backward.one_to_one C).near_litter N' hM hM',
end

lemma atom_union_atom_cond_forward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) :
  ∀ L C, spec.atom_cond ((σ : spec B) ⊔ new_atom_conds σ a A N hsmall ha) L C :=
begin  {
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
        ((σ : spec B) ⊔ σ.new_atom_conds a A N hsmall ha).domain} =
        {a_1 ∈ litter_set L | (inl a_1, C) ∈ (σ : spec B).domain} ∪ {a_1 ∈ litter_set L | (inl a_1, C) ∈
          binary_condition.domain '' (new_atom_conds σ a A N hsmall ha).carrier},
      { rw (new_atom_conds σ a A N hsmall ha).image_domain',
       ext,
        simp only [subtype.val_eq_coe, mem_sep_iff, mem_union, mem_image, set.mem_range,
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
      convert (mk_union_le _ _).trans_lt (add_lt_of_lt κ_regular.aleph_0_le
        hLsmall $ (mk_emptyc _).trans_lt κ_regular.pos),
      simp only [binary_condition.domain, subtype.val_eq_coe, mem_sep_iff, mem_image, set.mem_range,
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
      cases hL (inr_mem_domain ha) } },
  { by_cases a.fst ≠ L ∨ A ≠ C,
    { refine spec.atom_cond.small_in L' (or.inl hL) _ _,
      { unfold small,
        have : {a_1 ∈ litter_set L | (inl a_1, C) ∈
          ((σ : spec B) ⊔ σ.new_atom_conds a A N hsmall ha).domain} = {a_1 ∈ litter_set L | (inl a_1, C) ∈
              (σ : spec B).domain} ∪ {a_1 ∈ litter_set L | (inl a_1, C) ∈
                binary_condition.domain '' (new_atom_conds σ a A N hsmall ha).carrier},
       { rw (new_atom_conds σ a A N hsmall ha).image_domain', ext,
          simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and, mem_sep_iff, domain_sup, mem_union, mem_image, set.mem_range,
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
        convert (mk_union_le _ _).trans_lt (add_lt_of_lt κ_regular.aleph_0_le
          hLsmall $ (mk_emptyc _).trans_lt κ_regular.pos),
        simp only [binary_condition.domain, subtype.val_eq_coe, mem_sep_iff, mem_image,
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
        (λ x, dite ((inl x.val, A) ∈ (σ : spec B).domain)
          (λ hx, atom_value σ A x hx)
          (λ hx, (atom_map σ a A N hsmall ha ⟨x.val, x.prop, hx⟩).val))
        (λ y hy, _) (ext $ λ x, ⟨λ hx, _, λ hx, _⟩),
      { by_cases (inl y, A) ∈ (σ : spec B).domain,
        { rw dif_pos h,
          exact or.inl (atom_value_spec σ A y h) },
        { rw dif_neg h,
          exact or.inr ⟨⟨y, hy, h⟩, rfl⟩ } },
      { by_cases (inl x, A) ∈ (σ : spec B).range,
        { rw spec.mem_range at h, obtain ⟨⟨⟨y, _⟩ | _, _⟩, hin, hxy⟩ := h; cases hxy,
          have hya : y ∈ litter_set a.fst := (hmaps hin).2 hx,
          use ⟨y, hya⟩,
          dsimp only,
          have : (inl y, A) ∈ (σ : spec B).domain := inl_mem_domain hin,
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
        by_cases (inl y.val, A) ∈ (σ : spec B).domain,
        { simp_rw dif_pos h,
          exact (hmaps $ atom_value_spec σ A y.val h).1 y.prop },
        { simp_rw dif_neg h,
          obtain ⟨c, hcy, hcN, hcnin⟩ := atom_to_cond_spec σ a A N hsmall ha ⟨y.val, y.prop, h⟩,
          simp only [atom_to_cond, prod.mk.inj_iff, eq_self_iff_true, true_and, and_true] at hcy,
          rw ← hcy at hcN,
          exact hcN } } } },
}end

private lemma technical_lemma  (x: ↥(litter_set N.fst)) (hx: (inl x.val, A) ∉ (σ : spec B).range) (hM_sd: ↥(litter_set N.fst ∆ ↑(N.snd)) → atom)
(hM3: ∀ (a : ↥(litter_set N.fst ∆ ↑(N.snd))), (inl (↑a, hM_sd a), A) ∈ ((σ : spec B))⁻¹) : x.val ∈ (N.2 : set atom) := begin
          suffices : x.val ∉ litter_set N.fst ∆ (N.2 : set atom),
          dsimp [∆)] at this, rw [← subtype.val_eq_coe, (eq_true_intro x.prop] at this,
          simp only [subtype.val_eq_coe, true_and, not_true, and_false, or_false, not_not_mem] at this,
          exact this,
          by_contra,
          apply hx, -- x hx h
          simp only [subtype.val_eq_coe, spec.mem_range],
          use (⟨inl (⟨ hM_sd ⟨x.val, h⟩, x.val⟩ : atom × atom ), A⟩ : binary_condition B),
          split,
          have := (hM3 ⟨x, h⟩), simp only [subtype.coe_mk, subtype.val_eq_coe, inl_mem_inv, prod.swap_prod_mk] at this,
          exact this,
          simp only [subtype.val_eq_coe, binary_condition.range_mk, map_inl],
end

lemma cond_atom_of_range_atom (y : atom) (h : (inl y, A) ∈ (σ : spec B).range) :
  ∃ a : atom, (⟨sum.inl (a,y), A⟩ : binary_condition B) ∈ (σ : spec B) :=
begin
  simp only [subtype.val_eq_coe, spec.mem_range] at h, obtain ⟨cond, hcond1, hcond2⟩ := h,
  cases cond, cases cond_fst,
  simp only [binary_condition.range_mk, map_inl, prod.mk.inj_iff] at hcond2, obtain ⟨rfl, rfl⟩ :=hcond2,
  cases cond_fst, exact ⟨_, hcond1⟩,
  simp only [binary_condition.range_mk, map_inr, prod.mk.inj_iff, false_and] at hcond2,
  cases hcond2,
end

private lemma useful {a : atom} {L' : near_litter} {N : near_litter}
  (hM_sd : ↥(litter_set N.fst ∆ ↑(N.snd)) → atom)
  (hM4 : litter_set a.fst = ↑(L'.snd) ∆ range hM_sd) : a.fst = L'.fst :=
begin
  have := L'.2.prop,
  rw [← (symm_diff_bot (↑L'.snd)), ← symm_diff_self (litter_set L'.fst), symm_diff_left_comm,
  ← (symm_diff_bot (litter_set a.fst)), ← symm_diff_self (litter_set L'.fst),
  symm_diff_left_comm, symm_diff_assoc, symm_diff_assoc] at hM4,
  have hM4 := symm_diff_right_injective (litter_set L'.fst) hM4,
  have : is_near (litter_set a.fst) (litter_set L'.fst),
  dsimp [is_near],
  rw [hM4, ←symm_diff_assoc],
  refine ((mk_le_mk_of_subset symm_diff_subset_union).trans $ mk_union_le _ _).trans_lt _,
  rw symm_diff_comm,
  apply add_lt_of_lt κ_regular.aleph_0_le L'.snd.prop,
  exact lt_of_le_of_lt mk_range_le N.snd.prop,
  exact is_near_litter_litter_set_iff.mp this,
end


lemma atom_union_atom_cond_backward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) (L C) :
  spec.atom_cond ((σ : spec B) ⊔ new_atom_conds σ a A N hsmall ha)⁻¹ L C :=
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
        convert (mk_union_le _ _).trans_lt (add_lt_of_lt κ_regular.aleph_0_le
            hLsmall $ (mk_emptyc _).trans_lt κ_regular.pos),
        ext,
        split,
        { rintro ⟨hxL, hxrge | hxrge⟩,
          { exact or.inl ⟨hxL, hxrge⟩ },
          exact or.inr (h (prod.eq_iff_fst_eq_snd_eq.1 hxrge.some_spec).2) },
        { rintro (⟨hxL, hxrge⟩ | h),
          { exact ⟨hxL, or.inl hxrge⟩ },
          cases h } } },
    { by_cases A = C,
      { subst h,

       refine spec.atom_cond.small_out _ _,
        rintro (hnin | hnin),
          { exact hL hnin },
        simp only [spec.mem_range] at hnin,
        obtain ⟨⟨⟨a1,a2⟩ | ⟨l1, l2⟩ , ei⟩, h1, h2 ⟩ := hnin,
        simp only [binary_condition.range_mk, map_inl, prod.mk.inj_iff, false_and] at h2, exact h2,
        simp only [inr_mem_new_atom_conds] at h1, exact h1,
        simp only [subtype.val_eq_coe, domain_inv, range_sup, mem_union],
        convert (mk_union_le _ _).trans_lt (add_lt_of_lt κ_regular.aleph_0_le
            hLsmall $ (_ : cardinal.mk (coe_sort{a_1 ∈ litter_set L |(inl a_1, A) ∈ (σ.new_atom_conds a A N hsmall ha).range}) < #κ)),
        ext,
        split,
        { rintro ⟨hxL, hxrge | hxrge⟩,
          { exact or.inl ⟨hxL, hxrge⟩ },
          exact or.inr ⟨hxL, hxrge⟩ },
        { rintro (⟨hxL, hxrge⟩ | h),
          { exact ⟨hxL, or.inl hxrge⟩ },
          cases h, simp only [mem_sep_iff], exact ⟨h_left, or.inr h_right⟩ },
          suffices : {a_1 ∈ litter_set L | (inl a_1, A) ∈ (σ.new_atom_conds a A N hsmall ha).range} ⊆ N.2 ∩ litter_set L,
          apply lt_of_le_of_lt, apply mk_le_mk_of_subset this,
          {
            suffices : (↑(N.snd) ∩ litter_set L) ⊆ (litter_set N.fst ∆ ((N.2 : set atom))),
            apply lt_of_le_of_lt, apply mk_le_mk_of_subset this,
            exact N.2.2,
            dsimp [∆], rw set.subset_def, intros x hx, refine or.inr ⟨hx.1, _ ⟩, by_contra h3,
            apply pairwise_disjoint_litter_set N.fst L h ⟨h3, hx.2 ⟩,
          },
          simp only [spec.mem_range, subset_inter_iff, sep_subset, and_true],
          intros a2 ha2, simp only [mem_sep_iff] at ha2, obtain ⟨_, cond, hcond, hcond2 ⟩ := ha2,
          obtain ⟨ ⟨ a3, a2_2⟩, A_2⟩ := cond, simp only [mem_domain, subtype.val_eq_coe, not_exists, not_and, inl_mem_new_atom_conds] at hcond,
          obtain ⟨_, h, _, h2⟩ := hcond,
          simp only [binary_condition.range_mk, map_inl, prod.mk.inj_iff] at hcond2,
          rw [← hcond2.left, h2], exact ((atom_map σ a A N hsmall ha _).prop).1,
          simp only [binary_condition.range_mk, map_inr, prod.mk.inj_iff, false_and] at hcond2,
          exfalso, exact hcond2,
         },
      { refine spec.atom_cond.small_out _ _,
        { rintro (hnin | hnin),
          { exact hL hnin },
          exact h (prod.eq_iff_fst_eq_snd_eq.1 hnin.some_spec).2 },
        simp only [subtype.val_eq_coe, domain_inv, range_sup, mem_union],
        convert (mk_union_le _ _).trans_lt (add_lt_of_lt κ_regular.aleph_0_le
            hLsmall $ (mk_emptyc _).trans_lt κ_regular.pos),
        ext,
        split,
        { rintro ⟨hxL, hxrge | hxrge⟩,
          { exact or.inl ⟨hxL, hxrge⟩ },
          exact or.inr (h (prod.eq_iff_fst_eq_snd_eq.1 hxrge.some_spec).2) },
        { rintro (⟨hxL, hxrge⟩ | h),
          { exact ⟨hxL, or.inl hxrge⟩ },
          cases h } } } },
  { by_cases A = C, subst h,
  rw sup_inv,

   {classical,
    have := σ.prop.backward.near_litter_cond _ _ A ha,
    obtain ⟨M, hM1, hM_sd, hM3, hM4 ⟩ := this,
    by_cases h2: L = N.fst,
    {
      subst h2,
        have := (σ.prop.forward.one_to_one A).near_litter _ hL hM1, dsimp only at this,
        subst this,
      refine spec.atom_cond.all L' (or.inl hL) (λ x : litter_set N.fst, dite ((inl x.val, A) ∈ (σ : spec B).range)
          (λ hx, atom_value σ⁻¹ A x hx)
          (λ hx, ((atom_map σ a A N hsmall ha).inv_fun ⟨x.val, _, hx⟩).val))
        (λ y hy, _) (ext $ λ x, ⟨λ hx, _, λ hx, _⟩),
      exact technical_lemma σ A N x hx hM_sd hM3,
        by_cases h3: (inl y, A) ∈ (σ : spec B).range,
     {
           simp only [subtype.coe_mk, subtype.val_eq_coe, coe_inv, set.mem_inv, binary_condition.inv_def, map_inl, prod.swap_prod_mk,
           set_like.mem_coe],
           rw dif_pos, apply or.inl,
           have := cond_atom_of_range_atom σ A y h3, obtain ⟨b, hb⟩ := this,
           suffices : (inl ( y, σ⁻¹.atom_value A y _), A) ∈ (@coe {σ // spec.allowable B σ} (spec ↑B) coe_to_lift σ)⁻¹,
           simp only [inl_mem_inv, prod.swap_prod_mk] at this, exact this,
           apply atom_value_spec, exact h3,
        },
        {
          rw dif_neg, apply or.inr, simp only [subtype.val_eq_coe, true_and, subtype.coe_mk, prod.swap_prod_mk, map_inl, equiv.inv_fun_as_coe, coe_inv, set.mem_inv,
          binary_condition.inv_def, set_like.mem_coe, inl_mem_new_atom_conds, eq_self_iff_true, mem_domain, not_exists, not_and,
          subtype.coe_eta, equiv.apply_symm_apply, exists_prop, and_true],
          have := (((atom_map σ a A N hsmall ha).symm) ⟨y, _⟩).prop, simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and, mem_sep_iff] at this,
          exact this,
          simp only, exact h3,
        },
        by_cases h4 : (inl x, A) ∈ (σ : spec B).domain,
        {
          simp only [spec.mem_range, subtype.val_eq_coe, subtype.coe_mk, equiv.inv_fun_as_coe, set.mem_range, set_coe.exists],
          simp only [subtype.val_eq_coe, mem_domain] at h4, obtain ⟨cond, hcond1, hcond2⟩ := h4,
          cases cond, cases cond_fst, cases cond_fst, simp_rw inl_mem_inv at hmaps, dsimp [prod.swap] at hmaps,
          simp only [binary_condition.domain_mk, map_inl, prod.mk.inj_iff] at hcond2, obtain ⟨rfl, rfl⟩ := hcond2,
          use cond_fst_snd, use (hmaps hcond1).mpr hx,
          rw dif_pos,
          apply (σ⁻¹.prop.backward.one_to_one cond_snd).atom, simp only [subtype.val_eq_coe, mem_set_of_eq],
          apply atom_value_spec,
          simp only [val_inv], simp only [subtype.val_eq_coe], simp only [inv_inv], simp only [mem_set_of_eq],
          exact hcond1,
          refine ⟨⟨sum.inl (cond_fst_fst, cond_fst_snd), cond_snd⟩ , hcond1, _⟩, simp only [binary_condition.range_mk, map_inl],
          simp only [binary_condition.domain_mk, map_inr, prod.mk.inj_iff, false_and] at hcond2,
          exfalso, exact hcond2,
        },
        refine ⟨⟨(atom_map σ a A N hsmall ha) ⟨x, _, h4⟩, _⟩, _ ⟩,
        simp only [subtype.val_eq_coe] at hM4,
        have useful:= useful hM_sd hM4,
        rw useful,
        by_contra hx_2,
        rw useful at hM4,
        rw hM4 at hx_2, rw symm_diff_def at hx_2, simp only [sup_eq_union, mem_union, mem_diff, set.mem_range, set_coe.exists, not_exists] at hx_2, push_neg at hx_2,
        obtain ⟨x2, hx2, hx2_2 ⟩ := hx_2.left hx, subst hx2_2,
        have := hM3 ⟨x2, hx2⟩, simp only [subtype.coe_mk, subtype.val_eq_coe, inl_mem_inv, prod.swap_prod_mk] at this,
        simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and] at h4,
        have := h4 ⟨inl (hM_sd ⟨x2, hx2⟩, x2), A⟩ this, simp only [binary_condition.domain_mk, map_inl, eq_self_iff_true, not_true] at this, exfalso, exact this,
        have := ((atom_map σ a A N hsmall ha) ⟨x, _, h4⟩).prop,
        {simp only [subtype.val_eq_coe, spec.mem_range, not_exists, not_and, mem_sep_iff] at this,
        suffices h5: ↑((atom_map σ a A N hsmall ha) ⟨x, _⟩) ∉ (litter_set N.fst) ∆ N.snd,
        rw symm_diff_def at h5, simp only [sup_eq_union, mem_union, mem_diff] at h5, push_neg at h5,
        exact h5.right this.left,
        by_contra h6,
        have h7:= hM3 ⟨_, h6⟩, simp only [subtype.val_eq_coe, subtype.coe_mk, inl_mem_inv, prod.swap_prod_mk] at h7,
        have := this.right _ h7, simp only [map_inl, eq_self_iff_true, not_true, binary_condition.range_mk] at this,
        exact this,
        },
        dsimp only, rw dif_neg, simp only [subtype.coe_eta, equiv.inv_fun_as_coe, equiv.symm_apply_apply],
        apply ((atom_map σ a A N hsmall ha) ⟨x, _⟩).prop.2,-- ⋆
        obtain ⟨x_2_fst, hx_2⟩ := hx,
        dsimp at hx_2,
        by_cases h4 : @has_mem.mem ((atom ⊕ near_litter) × extended_index ↑B) (unary_spec ↑B) set.has_mem (inl ↑x_2_fst, A) (@coe (subtype (spec.allowable B)) (spec ↑B) coe_to_lift σ).range,
         {
          rw dif_pos h4 at hx_2,
          have := atom_value_spec σ⁻¹ A x_2_fst _,
          exact (@hmaps x_2_fst x begin subst hx_2, exact this end).mp x_2_fst.prop,
        },
        {
          rw dif_neg h4 at hx_2,
          subst hx_2,
          let aaa : ↥{a' ∈ litter_set a.fst | (inl a', A) ∉ (@coe (subtype (spec.allowable B)) (spec ↑B) coe_to_lift σ).domain} := _,
          have haaa : aaa = _, refl,
          suffices : ↑aaa ∈ L', rw haaa at this, exact this,
          have := aaa.prop.left,
          simp only [subtype.val_eq_coe] at hM4,
          let bbb : atom := aaa.val, have hbbb : bbb = aaa.val, refl, rw ← hbbb at this,
          rw hM4 at this, rw symm_diff_def at this, cases this, dsimp [bbb] at this,
          exact this.left,
          have := set.mem_of_mem_diff this, simp only [set.mem_range, set_coe.exists] at this,
          obtain ⟨x_3, h5, h6⟩  := this,
          have := hM3 ⟨x_3, h5⟩, rw h6 at this, dsimp [bbb] at this,
          have this2 := aaa.prop.right, simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and] at this2,
          exfalso,
          have := this2 _ this_1,
          simp only [binary_condition.domain_mk, map_inl, eq_self_iff_true, not_true] at this, exact this,
        }
    },
   {
      refine spec.atom_cond.small_in L' (or.inl hL) _ _,
    {
        simp only [subtype.val_eq_coe], simp only[domain_sup], simp only [domain_inv],
        dsimp [small],
        have : {a_1 ∈ litter_set L | (inl a_1, A) ∈ (@coe (subtype (spec.allowable B)) (spec ↑B) coe_to_lift σ).range ∨ (inl a_1, A) ∈ (σ.new_atom_conds a A N hsmall ha).range} = {a_1 ∈ litter_set L | (inl a_1, A) ∈ (@coe (subtype (spec.allowable B)) (spec ↑B) coe_to_lift σ).range}∪{a_1 ∈ litter_set L | (inl a_1, A) ∈ (σ.new_atom_conds a A N hsmall ha).range},
        {
          ext, simp only [spec.mem_range, mem_sep_iff, mem_union],
          rw and_or_distrib_left,
        },
        rw this, clear this,
        apply lt_of_le_of_lt, apply mk_union_le,
        apply add_lt_of_lt κ_regular.aleph_0_le,
        suffices :_ = ↥{x : atom | x ∈ litter_set L ∧ (inl x, A) ∈ (@coe (subtype (spec.allowable B)) (spec ↑B) coe_to_lift σ).range},
        suffices is_small : #(↥{a : atom | _}) < #κ,
        rw ← this at is_small, exact is_small,
        convert hLsmall, dsimp [coe_sort), (has_coe_to_sort.coe],
        simp only [spec.mem_range], apply lt_of_le_of_lt,
        refine @mk_le_mk_of_subset _ _ (N.2.1 \ (litter_set N.1)) _,
        intros x hx, simp only [spec.mem_range, mem_sep_iff] at hx,
        dsimp [new_atom_conds] at hx, obtain ⟨hx1, ⟨⟨⟨e1, e2⟩ | ⟨l1, l2⟩, e⟩, ⟨y, hy⟩, hcond⟩⟩ := hx,
        obtain ⟨c, hc1, hc2⟩ := atom_to_cond_spec σ a A N hsmall ha y, rw hy at hc1, simp only [prod.mk.inj_iff] at hc1,
        obtain ⟨⟨rfl, rfl⟩, rfl⟩  := hc1,
        simp only [binary_condition.range_mk, map_inl, prod.mk.inj_iff, eq_self_iff_true, and_true] at hcond, subst hcond,
        split, exact hc2.1, by_contra hx2,
        exact h2 (eq_of_mem_litter_set_of_mem_litter_set hx1 hx2),
        simp only [binary_condition.range_mk, map_inr, prod.mk.inj_iff, false_and] at hcond, exfalso, exact hcond,
        apply lt_of_le_of_lt, refine @mk_le_mk_of_subset _ _ ((litter_set N.fst) ∆ (N.2 : set atom)) _,
        {rw symm_diff_def, simp only [sup_eq_union, subset_union_right],},
        exact (N.snd.prop),
        },
      { intros a_1 a_2 h,
      cases h,
      exact hmaps h,
      dsimp [new_atom_conds] at h,
      obtain ⟨y, hy⟩ := h, obtain ⟨c, hc1, hc2⟩ := atom_to_cond_spec σ a A N hsmall ha y,
      rw hy at hc1, simp only [prod.mk.inj_iff, eq_self_iff_true, and_true] at hc1,
      obtain ⟨rfl, rfl⟩ := hc1,
      split, intro ha_1,
      have : a_1 ∈ litter_set N.fst ∆ ↑(N.snd),
      {rw symm_diff_def,
      apply or.inr, split, exact hc2.left, by_contra, exact h2 (eq_of_mem_litter_set_of_mem_litter_set ha_1 h),
      },
      have := hM3 ⟨a_1, this⟩, simp only [subtype.coe_mk, subtype.val_eq_coe, inl_mem_inv, prod.swap_prod_mk] at this, simp only [subtype.val_eq_coe, spec.mem_range, not_exists, not_and] at hc2,
      have := hc2.right _ this, simp only [binary_condition.range_mk, map_inl, eq_self_iff_true, not_true] at this,
      exfalso, exact this,
      intro hy2,
      rw symm_diff_def at hM4, simp only [subtype.val_eq_coe, sup_eq_union] at hM4,
      have := y.prop, simp only [subtype.val_eq_coe, mem_domain, not_exists, not_and, mem_sep_iff] at this,
      have := this.left, simp_rw hM4 at this, exfalso, cases this, have disj:= litter_image_disjoint σ⁻¹ A hL hM1 h2,
      apply disj, simp only [subtype.val_eq_coe, inf_eq_inter, mem_inter_eq], split, exact hy2,
      exact set.mem_of_mem_diff this_1,
      have hy3 := set.mem_of_mem_diff this_1,
      dsimp [range] at hy3, simp only [set_coe.exists] at hy3,
      apply y.prop.right,
      obtain ⟨y_a, hy_a1, hy_a2⟩ := hy3,
      have := hM3 ⟨y_a, hy_a1⟩,
      rw hy_a2 at this,
      simp only [subtype.coe_mk, subtype.val_eq_coe, inl_mem_inv, prod.swap_prod_mk] at this,
      simp only [subtype.val_eq_coe, mem_domain],
      refine ⟨_, this, _⟩,
      simp only [binary_condition.domain_mk, map_inl],
       }    }    },
    { refine spec.atom_cond.small_in L' (or.inl hL) _ _,
      { convert hLsmall using 2,
        refine funext (λ x, eq_iff_iff.2 ⟨λ hx, or.rec id _ hx, or.inl⟩),
        rintro ⟨_, ⟨⟩⟩,
        cases h rfl },
      { rintro a b (hab | ⟨_, ⟨⟩⟩),
        { exact hmaps hab },
        cases h rfl } } },
end

lemma atom_union_near_litter_cond_forward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) :
  ∀ N₁ N₂ C,
    spec.near_litter_cond ((σ : spec B) ⊔ new_atom_conds σ a A N hsmall ha) N₁ N₂ C :=
begin
  rintro N₁ N₂ C (h | h),
  { obtain ⟨M, hM₁, sd, hsd₁, hsd₂⟩ := σ.prop.forward.near_litter_cond N₁ N₂ C h,
    exact ⟨M, or.inl hM₁, sd, λ a, or.inl (hsd₁ a), hsd₂⟩ },
  obtain ⟨d, hd⟩ := h,
  cases hd,
end

lemma atom_union_near_litter_cond_backward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) :
  ∀ N₁ N₂ C,
    spec.near_litter_cond ((σ : spec B) ⊔ new_atom_conds σ a A N hsmall ha)⁻¹ N₁ N₂ C :=
begin
  rintro N₁ N₂ C (h | h),
  { obtain ⟨M, hM₁, sd, hsd₁, hsd₂⟩ := σ.prop.backward.near_litter_cond N₁ N₂ C h,
    exact ⟨M, or.inl hM₁, sd, λ a, or.inl (hsd₁ a), hsd₂⟩ },
  obtain ⟨d, hd⟩ := h,
  cases hd,
end

lemma atom_union_non_flex_cond_forward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) :
  spec.non_flex_cond B ((σ : spec B) ⊔ new_atom_conds σ a A N hsmall ha) :=
begin
  rintro β δ γ hγ hδ hγδ N₁ C t (ht | ht) ρ hρ,
  { exact σ.prop.forward.non_flex_cond hγ hδ hγδ N₁ C t ht ρ
      (hρ.mono $ subset_union_left _ _) },
  obtain ⟨d, hd⟩ := ht,
  cases hd,
end

lemma atom_union_non_flex_cond_backward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) :
  spec.non_flex_cond B ((σ : spec B) ⊔ new_atom_conds σ a A N hsmall ha)⁻¹ :=
begin
  rintro β δ γ hγ hδ hγδ N₁ C t (ht | ⟨d, ⟨⟩⟩) ρ hρ,
  exact σ.prop.backward.non_flex_cond hγ hδ hγδ N₁ C t ht ρ
      (hρ.mono $ subset_union_left _ _),
end

lemma atom_union_support_closed_forward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) :
  ((σ : spec B) ⊔ new_atom_conds σ a A N hsmall ha).domain.support_closed B :=
begin
  intros β δ γ hγ hδ hγδ C t ht,
  rw spec.domain_sup at ht ⊢,
  rw unary_spec.lower_union,
  obtain (ht | ⟨_, ⟨_, ⟨⟩⟩, ⟨⟩⟩) := ht,
  exact (σ.prop.forward.support_closed hγ hδ hγδ C t ht).mono (subset_union_left _ _),
end

lemma atom_union_support_closed_backward
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) :
  ((σ : spec B) ⊔ new_atom_conds σ a A N hsmall ha).range.support_closed B :=
begin
  intros β δ γ hγ hδ hγδ C t ht,
  rw spec.range_sup at ht ⊢,
  rw unary_spec.lower_union,
  obtain (ht | ⟨_, ⟨_, ⟨⟩⟩, ⟨⟩⟩) := ht,
  convert (σ.prop.backward.support_closed hγ hδ hγδ C t $ by rwa spec.domain_inv).mono
    (subset_union_left _ _),
end

lemma atom_union_flex_cond
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) (C) :
  spec.flex_cond B ((σ : spec B) ⊔ new_atom_conds σ a A N hsmall ha) C :=
begin
  obtain (⟨hdom, hrge⟩ | ⟨hdom, hrge⟩) := σ.prop.flex_cond C,
  { refine spec.flex_cond.co_large _ _,
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
  { refine spec.flex_cond.all (λ L hL, _) (λ L hL, _),
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
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) :
  spec.allowable B ((σ : spec B) ⊔ new_atom_conds σ a A N hsmall ha) :=
{ forward :=
  { one_to_one := atom_union_one_to_one_forward σ a A N hsmall ha,
    atom_cond := atom_union_atom_cond_forward σ a A N hsmall ha,
    near_litter_cond := atom_union_near_litter_cond_forward σ a A N hsmall ha,
    non_flex_cond := atom_union_non_flex_cond_forward σ a A N hsmall ha,
    support_closed := atom_union_support_closed_forward σ a A N hsmall ha },
  backward :=
  { one_to_one := atom_union_one_to_one_backward σ a A N hsmall ha,
    atom_cond := atom_union_atom_cond_backward σ a A N hsmall ha,
    near_litter_cond := atom_union_near_litter_cond_backward σ a A N hsmall ha,
    non_flex_cond := atom_union_non_flex_cond_backward σ a A N hsmall ha,
    support_closed := by { rw spec.domain_inv,
      exact atom_union_support_closed_backward σ a A N hsmall ha } },
  flex_cond := atom_union_flex_cond σ a A N hsmall ha }

lemma atom_union_all_atoms_domain
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) (b₁ b₂ : atom)
  (L : litter) (hb₁ : b₁ ∈ litter_set L) (C : extended_index B)
  (hσ : (⟨inl ⟨b₁, b₂⟩, C⟩ : binary_condition B) ∈
    range (atom_to_cond σ a A N hsmall ha)) :
  ∀ c ∈ litter_set L, ∃ d, (⟨inl ⟨c, d⟩, C⟩ : binary_condition B) ∈
    (σ : spec B) ⊔ new_atom_conds σ a A N hsmall ha :=
begin
  intros c hc,
  by_cases (⟨inl c, C⟩ : support_condition B) ∈ (σ : spec B).domain,
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
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B))
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
  { obtain this | ⟨e, he⟩ := h₂ d d.prop.left,
    { cases d.prop.right (inl_mem_domain this) },
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
    have := (h₃ (or.inr ⟨d, hd⟩)).1 d.prop.left,
    rwa (atom_union_one_to_one_backward σ a A N hsmall ha A).near_litter
       a.fst.to_near_litter (or.inl ha) h₁
  }
end

/-- The atom map only ever maps to the intersection of `N` with its corresponding litter, `N.fst`.
In particular, we prove that if some atom `c` lies in the litter we're mapping to, it lies in the
precise near-litter we are mapping to as well. -/
lemma atom_union_mem'
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B))
  (b₁ b₂ : atom) (C : extended_index B)
  (hσ : (⟨inl ⟨b₁, b₂⟩, C⟩ : binary_condition B) ∈ range (atom_to_cond σ a A N hsmall ha))
  (c : atom) (hc₁ : c ∈ litter_set b₂.fst) (hc₂ : (inl c, A) ∉ (σ : spec B).range) :
  c ∈ (N.snd : set atom) :=
begin
  contrapose hc₂,
  rw not_not_mem,

  suffices hb₂ : b₂.fst = N.fst,
  { rw hb₂ at hc₁,
    obtain ⟨M, hM, symm_diff, hS₁, hS₂⟩ :=
      σ.prop.backward.near_litter_cond N a.fst.to_near_litter A ha,
    exact inl_mem_domain (hS₁ ⟨c, or.inl ⟨hc₁, hc₂⟩⟩) },

  obtain ⟨d, hd⟩ := hσ,
  have : b₁ = d,
  { unfold atom_to_cond at hd,
    have hd' := congr_arg prod.fst hd, have := congr_arg prod.fst (inl.inj hd'),
    cases this, refl },
  subst this,

  obtain ⟨M, hM, symm_diff, hS₁, hS₂⟩ :=
    σ.prop.backward.near_litter_cond N a.fst.to_near_litter A ha,
  by_contradiction hb₂,
  have := hS₁ ⟨b₂, or.inr ⟨atom_union_mem σ a A N hsmall ha d b₂ C ⟨d, hd⟩, hb₂⟩⟩,
  obtain ⟨e, he₁, he₂, he₃⟩ := atom_to_cond_spec σ a A N hsmall ha d,
  rw hd at he₁,
  cases he₁,
  exact he₃ (inl_mem_domain this),
end

lemma atom_union_all_atoms_range
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) (b₁ b₂ : atom)
  (L : litter) (hb₂ : b₂ ∈ litter_set L) (C : extended_index B)
  (hσ : (⟨inl ⟨b₁, b₂⟩, C⟩ : binary_condition B) ∈
    range (atom_to_cond σ a A N hsmall ha)) :
  ∀ c ∈ litter_set L, ∃ d, (⟨inl ⟨d, c⟩, C⟩ : binary_condition B) ∈
    (σ : spec B) ⊔ new_atom_conds σ a A N hsmall ha :=
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
      σ.prop.backward.near_litter_cond N a.fst.to_near_litter A ‹_›,
    rw spec.inr_mem_inv at hM,
    have mem_symm_diff : b₂ ∈ litter_set N.fst ∆ N.snd := or.inr ⟨b₂_mem, ne.symm h⟩,
    have hS₁' := hS₁ ⟨b₂, mem_symm_diff⟩,
    rw spec.inl_mem_inv at hS₁',
    have : symm_diff ⟨b₂, mem_symm_diff⟩ = d :=
      (atom_union_one_to_one_forward σ a A N hsmall ha A).atom b₂
        (or.inl hS₁') (or.inr ⟨_, hd⟩),
    refine d.prop.right _,
    rw [subtype.val_eq_coe, ← this],
    exact inl_mem_domain hS₁' },
  subst this,

  intros c hc,
  by_cases (⟨inl c, A⟩ : support_condition B) ∈ (σ : spec B).range,
  { rw spec.mem_range at h, obtain ⟨⟨⟨d₁, d₂⟩ | Ns, D⟩, hc₁, hc₂⟩ := h; cases hc₂,
    exact ⟨d₁, or.inl hc₁⟩ },
  have : c ∈ (N.2 : set atom),
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
  (hsmall : small {a ∈ litter_set a.fst | (inl a, A) ∈ (σ : spec B).domain})
  (ha : (inr (a.fst.to_near_litter, N), A) ∈ (σ : spec B)) :
  σ ≤ ⟨(σ : spec B) ⊔ new_atom_conds σ a A N hsmall ha, atom_union_allowable σ a A N hsmall ha⟩ := {
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
lemma exists_ge_atom (hσ : ∀ c, c ≺ (⟨inl a, A⟩ : support_condition B) → c ∈ (σ : spec B).domain) :
  ∃ ρ, σ ≤ ρ ∧ (⟨inl a, A⟩ : support_condition B) ∈ (ρ : spec B).domain :=
begin
  by_cases haσ : (⟨inl a, A⟩ : support_condition B) ∈ (σ : spec B).domain,
  { exact ⟨σ, le_rfl, haσ⟩ },
  have h := hσ (⟨inr a.fst.to_near_litter, A⟩ : support_condition B)
    (constrains.mem_litter a.fst a rfl _),
  rw mem_domain at h,
  obtain ⟨⟨_ | ⟨_, N⟩, A⟩, hc₁, hc₂⟩ := h; cases hc₂,
  obtain ⟨N', atom_map, hσ₁, hσ₂, hN'⟩ | ⟨ hL, hsmall⟩ | ⟨L', hL, hsmall, hequiv⟩:= σ.prop.forward.atom_cond a.fst A,
  { exfalso, apply haσ, simp only [subtype.val_eq_coe, mem_domain], exact ⟨_, ⟨hσ₂ a rfl, rfl⟩⟩ },
  all_goals {exact ⟨_, le_atom_union σ a A N hsmall hc₁, mem_union_right _ ⟨⟨a, rfl, haσ⟩, rfl⟩ ⟩},
end

end allowable_spec
end con_nf
