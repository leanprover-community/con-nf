import data.pfun
import phase2.approximation
import phase2.complete_orbit

open cardinal set
open_locale cardinal classical

universe u

namespace con_nf
variable [params.{u}]

/-!
# Weak approximations
-/

/-- A *weak near-litter approximation* is a partial function from atoms to atoms and a partial
function from litters to near-litters, both of which have small domain.
The image of a litter under the `litter_map` should be interpreted as the intended *precise* image
of this litter under an allowable permutation.
The atom and litter maps should be injective (in suitable senses) and cohere in the sense that
images of atoms in litters are mapped to atoms inside the corresponding near-litters. -/
@[ext] structure weak_near_litter_approx :=
(atom_map : atom →. atom)
(litter_map : litter →. near_litter)
(atom_map_dom_small : small atom_map.dom)
(litter_map_dom_small : small litter_map.dom)
(atom_map_injective : ∀ ⦃a b⦄ ha hb, (atom_map a).get ha = (atom_map b).get hb → a = b)
(litter_map_injective : ∀ ⦃L₁ L₂ : litter⦄ hL₁ hL₂,
  (((litter_map L₁).get hL₁ : set atom) ∩ (litter_map L₂).get hL₂).nonempty → L₁ = L₂)
(atom_mem : ∀ (a : atom) ha L hL, a.1 = L ↔ (atom_map a).get ha ∈ (litter_map L).get hL)

/-- A `β`-weak structural approximation is a product that assigns a weak near-litter approximation
to each `β`-extended index. -/
def weak_struct_approx (β : type_index) := extended_index β → weak_near_litter_approx

namespace weak_near_litter_approx

variable (w : weak_near_litter_approx)

/-- A litter that is not allowed to be used as a sandbox because it appears somewhere that
we need to preserve. -/
@[mk_iff] inductive banned_litter : litter → Prop
| atom_dom (a : atom) : (w.atom_map a).dom → banned_litter a.1
| litter_dom (L : litter) : (w.litter_map L).dom → banned_litter L
| atom_map (a : atom) (h) : banned_litter ((w.atom_map a).get h).1
| litter_map (L : litter) (h) : banned_litter ((w.litter_map L).get h).1
| diff (L : litter) (h) (a : atom) :
    a ∈ ((w.litter_map L).get h : set atom) \ litter_set ((w.litter_map L).get h).1 →
    banned_litter a.1

/-- There are only a small amount of banned litters. -/
lemma banned_litter_small : small {L | w.banned_litter L} :=
begin
  simp only [banned_litter_iff, mem_diff, set_like.mem_coe, mem_litter_set],
  refine small.union _ (small.union _ (small.union _ (small.union _ _))),
  { refine lt_of_le_of_lt _ w.atom_map_dom_small,
    refine ⟨⟨λ a, ⟨_, a.prop.some_spec.1⟩, λ a₁ a₂ h, _⟩⟩,
    simp only [subtype.mk_eq_mk, prod.mk.inj_iff] at h,
    have := a₁.prop.some_spec.2,
    rw h at this,
    exact subtype.coe_injective (this.trans a₂.prop.some_spec.2.symm), },
  { refine lt_of_le_of_lt _ w.litter_map_dom_small,
    refine ⟨⟨λ L, ⟨_, L.prop⟩, λ L₁ L₂ h, _⟩⟩,
    simp only [subtype.mk_eq_mk, prod.mk.inj_iff] at h,
    exact subtype.coe_injective h, },
  { refine lt_of_le_of_lt _ w.atom_map_dom_small,
    refine ⟨⟨λ L, ⟨_, L.prop.some_spec.some⟩, λ L₁ L₂ h, _⟩⟩,
    simp only [subtype.mk_eq_mk, prod.mk.inj_iff] at h,
    have := L₁.prop.some_spec.some_spec,
    simp_rw h at this,
    exact subtype.coe_injective (this.trans L₂.prop.some_spec.some_spec.symm), },
  { refine lt_of_le_of_lt _ w.litter_map_dom_small,
    refine ⟨⟨λ L, ⟨_, L.prop.some_spec.some⟩, λ L₁ L₂ h, _⟩⟩,
    simp only [subtype.mk_eq_mk, prod.mk.inj_iff] at h,
    have := L₁.prop.some_spec.some_spec,
    simp_rw h at this,
    exact subtype.coe_injective (this.trans L₂.prop.some_spec.some_spec.symm), },
  { have : small ⋃ (L : litter) (h : (w.litter_map L).dom),
      ((w.litter_map L).get h : set atom) \ litter_set ((w.litter_map L).get h).1,
    { refine small.bUnion _ _,
      { refine lt_of_le_of_lt _ w.litter_map_dom_small,
        refine ⟨⟨λ N, ⟨_, N.prop⟩, λ N₁ N₂ h, _⟩⟩,
        simp only [subtype.mk_eq_mk, prod.mk.inj_iff] at h,
        exact subtype.coe_inj.mp h, },
      { intros L hL,
        refine small.mono _ ((w.litter_map L).get hL).2.prop,
        exact λ x hx, or.inr hx, }, },
    refine lt_of_le_of_lt _ this,
    refine ⟨⟨λ L, ⟨L.prop.some_spec.some_spec.some, _⟩, λ L₁ L₂ h, _⟩⟩,
    { simp only [mem_Union],
      exact ⟨_, _, L.prop.some_spec.some_spec.some_spec.1⟩, },
    simp only [subtype.mk_eq_mk, prod.mk.inj_iff] at h,
    have := L₁.prop.some_spec.some_spec.some_spec.2,
    rw h at this,
    exact subtype.coe_injective
      (this.trans L₂.prop.some_spec.some_spec.some_spec.2.symm), },
end

lemma not_banned_litter_nonempty : nonempty {L | ¬w.banned_litter L} :=
begin
  rw ← mk_ne_zero_iff,
  intro h,
  have := mk_sum_compl {L | w.banned_litter L},
  rw [compl_set_of, h, add_zero, mk_litter] at this,
  exact κ_le_μ.not_lt (lt_of_eq_of_lt this.symm w.banned_litter_small),
end

/-- The *sandbox litter* for a weak near-litter approximation is an arbitrarily chosen litter that
isn't banned. -/
noncomputable def sandbox_litter : litter := w.not_banned_litter_nonempty.some

lemma sandbox_litter_not_banned : ¬w.banned_litter w.sandbox_litter :=
w.not_banned_litter_nonempty.some.prop

/-- If `a` is in the domain, this is the atom map. Otherwise, this gives an arbitrary atom. -/
noncomputable def atom_map_or_else (a : atom) : atom := (w.atom_map a).get_or_else (arbitrary atom)

lemma atom_map_or_else_of_dom {a : atom} (ha : (w.atom_map a).dom) :
  w.atom_map_or_else a = (w.atom_map a).get ha :=
by rw [atom_map_or_else, part.get_or_else_of_dom]

lemma mk_atom_map_image_le_mk_sandbox :
  #(w.atom_map.dom ∆ (w.atom_map_or_else '' w.atom_map.dom) : set atom) ≤
    #(litter_set w.sandbox_litter) :=
begin
  rw mk_litter_set,
  refine le_trans (mk_subtype_mono symm_diff_subset_union) (le_trans (mk_union_le _ _) _),
  refine add_le_of_le κ_regular.aleph_0_le _ _,
  exact le_of_lt w.atom_map_dom_small,
  exact le_trans mk_image_le (le_of_lt w.atom_map_dom_small),
end

lemma disjoint_sandbox :
  disjoint (w.atom_map.dom ∪ w.atom_map_or_else '' w.atom_map.dom) (litter_set w.sandbox_litter) :=
begin
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem],
  rintros a ⟨ha₁, ha₂⟩,
  rw mem_litter_set at ha₂,
  have hnb := w.sandbox_litter_not_banned,
  rw ← ha₂ at hnb,
  cases ha₁,
  { exact hnb (banned_litter.atom_dom a ha₁), },
  { refine hnb _,
    simp only [mem_image, pfun.mem_dom] at ha₁,
    obtain ⟨b, ⟨_, hb, rfl⟩, rfl⟩ := ha₁,
    rw w.atom_map_or_else_of_dom hb,
    exact banned_litter.atom_map b hb, },
end

lemma atom_map_or_else_injective : inj_on w.atom_map_or_else w.atom_map.dom :=
begin
  intros a ha b hb h,
  rw [w.atom_map_or_else_of_dom ha, w.atom_map_or_else_of_dom hb] at h,
  exact w.atom_map_injective ha hb h,
end

/-- A local permutation induced by completing the orbits of atoms in a weak near-litter
approximation. This function creates forward and backward images of atoms in the *sandbox litter*,
a litter which is away from the domain and range of the approximation in question, so it should
not interfere with other constructions. -/
noncomputable def complete_atom_perm : local_perm atom :=
local_perm.complete
  w.atom_map_or_else
  w.atom_map.dom
  (litter_set w.sandbox_litter)
  w.mk_atom_map_image_le_mk_sandbox
  (by simpa only [mk_litter_set] using κ_regular.aleph_0_le)
  w.disjoint_sandbox
  w.atom_map_or_else_injective

lemma sandbox_subset_small : small (local_perm.sandbox_subset
  w.mk_atom_map_image_le_mk_sandbox
  (by simpa only [mk_litter_set] using κ_regular.aleph_0_le)) :=
begin
  rw small,
  rw cardinal.mk_congr (local_perm.sandbox_subset_equiv _ _),
  simp only [mk_sum, mk_prod, mk_denumerable, lift_aleph_0, lift_uzero, lift_id],
  refine add_lt_of_lt κ_regular.aleph_0_le _ _;
    refine (mul_lt_of_lt κ_regular.aleph_0_le (lt_of_le_of_lt Λ_limit.aleph_0_le Λ_lt_κ) _);
    refine lt_of_le_of_lt (mk_subtype_mono (diff_subset _ _)) _,
  { exact w.atom_map_dom_small, },
  { exact lt_of_le_of_lt mk_image_le w.atom_map_dom_small, },
end

lemma complete_atom_perm_domain_small : small w.complete_atom_perm.domain :=
small.union (small.union w.atom_map_dom_small
  (lt_of_le_of_lt mk_image_le w.atom_map_dom_small)) w.sandbox_subset_small

/-- A near-litter approximation built from this weak near-litter approximation.
Its action on atoms matches that of the weak approximation, and its rough action on litters
matches the given litter permutation. -/
noncomputable def complete (litter_perm : local_perm litter) : near_litter_approx := {
  atom_perm := w.complete_atom_perm,
  litter_perm := litter_perm,
  domain_small := λ L, small.mono (inter_subset_right _ _) w.complete_atom_perm_domain_small,
}

variable {litter_perm : local_perm litter}

lemma complete_atom_perm_apply_eq {a : atom} (ha : (w.atom_map a).dom) :
  w.complete_atom_perm a = (w.atom_map a).get ha :=
by rwa [complete_atom_perm, local_perm.complete_apply_eq, atom_map_or_else_of_dom]

lemma complete_smul_atom_eq {a : atom} (ha : (w.atom_map a).dom) :
  w.complete litter_perm • a = (w.atom_map a).get ha := w.complete_atom_perm_apply_eq ha

@[simp] lemma complete_smul_litter_eq (L : litter) :
  w.complete litter_perm • L = litter_perm L := rfl

lemma smul_to_near_litter_eq_of_exactly_approximates
  {π : near_litter_perm} (hπ : (w.complete litter_perm).exactly_approximates π)
  {L : litter} (hL : (w.litter_map L).dom)
  (hπL : π • L = ((w.litter_map L).get hL).1)
  (hdiff : ((w.litter_map L).get hL : set atom) ∆
    litter_set ((w.litter_map L).get hL).1 ⊆ w.atom_map.ran)
  (hfwd : ∀ a ha, (w.atom_map a).get ha ∈ litter_set L → (w.atom_map ((w.atom_map a).get ha)).dom) :
  π • L.to_near_litter = (w.litter_map L).get hL :=
begin
  refine set_like.coe_injective _,
  ext a : 1,
  simp only [mem_smul_set_iff_inv_smul_mem, near_litter_perm.coe_smul, litter.coe_to_near_litter,
    mem_litter_set, set_like.mem_coe],
  split,
  { intro ha,
    by_cases π.is_exception a,
    { suffices h' : π⁻¹ • a ∈ w.atom_map.dom,
      { rw w.atom_mem _ h' L hL at ha,
        have := hπ.map_atom _ (or.inl (or.inl h')),
        rw w.complete_smul_atom_eq h' at this,
        rw [this, smul_inv_smul] at ha,
        exact ha, },
      rw ← hπ.symm_map_atom a (hπ.exception_mem _ h) at ha ⊢,
      obtain ((hdom | hdom) | hdom) := (w.complete litter_perm).atom_perm.symm.map_domain
        (hπ.exception_mem _ h),
      { exact hdom, },
      { obtain ⟨c, hc₁, hc₂⟩ := hdom,
        rw w.atom_map_or_else_of_dom hc₁ at hc₂,
        have := hfwd c hc₁ (by rwa hc₂),
        rw hc₂ at this,
        exact this, },
      { cases w.sandbox_litter_not_banned _,
        rw ← eq_of_mem_litter_set_of_mem_litter_set ha
          (local_perm.sandbox_subset_subset _ _ hdom),
        exact banned_litter.litter_dom L hL, }, },
    { by_contradiction h',
      simp only [near_litter_perm.is_exception, mem_litter_set, not_or_distrib, not_not, ha] at h,
      obtain ⟨b, hb, rfl⟩ := hdiff (or.inr ⟨by rw [← hπL, h.2, smul_inv_smul, mem_litter_set], h'⟩),
      refine h' ((w.atom_mem b hb L hL).mp _),
      have := hπ.map_atom b (or.inl (or.inl hb)),
      rw [w.complete_smul_atom_eq hb] at this,
      rw [this, inv_smul_smul] at ha,
      exact ha, }, },
  { intro ha,
    by_cases π⁻¹ • a ∈ w.atom_map.dom,
    { rw w.atom_mem _ h L hL,
      have := hπ.map_atom _ (or.inl (or.inl h)),
      rw w.complete_smul_atom_eq h at this,
      rw [this, smul_inv_smul],
      exact ha, },
    have haL : a ∈ litter_set ((w.litter_map L).get hL).fst,
    { by_contradiction h',
      obtain ⟨b, hb, rfl⟩ := hdiff (or.inl ⟨ha, h'⟩),
      have := hπ.map_atom b (or.inl (or.inl hb)),
      rw [w.complete_smul_atom_eq hb] at this,
      rw [this, inv_smul_smul] at h,
      exact h hb, },
    by_contradiction h',
    have : π.is_exception (π⁻¹ • a),
    { left,
      contrapose! h',
      rw smul_inv_smul at h',
      have := eq_of_mem_litter_set_of_mem_litter_set haL h',
      rw [← hπL, smul_left_cancel_iff] at this,
      exact this.symm, },
    have : π.is_exception a,
    { refine or.inr (λ h'', h' (h''.trans _)),
      rw [inv_smul_eq_iff, hπL],
      exact haL, },
    obtain ((hdom | hdom) | hdom) := hπ.exception_mem a this,
    { sorry, },
    { sorry, },
    { sorry, }, },
end

end weak_near_litter_approx

end con_nf
