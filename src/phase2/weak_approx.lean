import data.pfun
import phase2.approximation
import phase2.complete_orbit
import phase2.reduction

open cardinal quiver set sum with_bot
open_locale cardinal classical pointwise

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

/-- If `L` is in the domain, this is the litter map.
Otherwise, this gives an arbitrary near-litter. -/
noncomputable def litter_map_or_else (L : litter) : near_litter :=
(w.litter_map L).get_or_else (arbitrary near_litter)

lemma litter_map_or_else_of_dom {L : litter} (hL : (w.litter_map L).dom) :
  w.litter_map_or_else L = (w.litter_map L).get hL :=
by rw [litter_map_or_else, part.get_or_else_of_dom]

/-- The induced action of this weak approximation on near-litters. -/
noncomputable def near_litter_map_or_else (N : near_litter) : near_litter :=
⟨(w.litter_map_or_else N.fst).fst,
  w.litter_map_or_else N.fst ∆ (w.atom_map_or_else '' litter_set N.fst ∆ N),
  begin
    rw [is_near_litter, is_near, ← symm_diff_assoc],
    exact (w.litter_map_or_else N.fst).snd.prop.symm_diff (small.image N.2.prop),
  end⟩

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

/-- A weak approximation is precise at a litter in its domain if all atoms in the symmetric
difference of its image are accounted for. -/
@[mk_iff] structure precise_at {L : litter} (hL : (w.litter_map L).dom) : Prop :=
(diff : ((w.litter_map L).get hL : set atom) ∆
  litter_set ((w.litter_map L).get hL).1 ⊆ w.atom_map.ran)
(fwd : ∀ a ha, (w.atom_map a).get ha ∈ litter_set L → (w.atom_map ((w.atom_map a).get ha)).dom)
(back : w.atom_map.dom ∩ (w.litter_map L).get hL ⊆ w.atom_map.ran)

/-- A weak approximation is precise if it is precise at every litter in its domain. -/
def precise : Prop := ∀ ⦃L⦄ (hL : (w.litter_map L).dom), w.precise_at hL

lemma smul_atom_eq
  {π : near_litter_perm} (hπ : (w.complete litter_perm).exactly_approximates π)
  {a : atom} (ha : (w.atom_map a).dom) :
  π • a = (w.atom_map a).get ha :=
by rw [← hπ.map_atom a (or.inl (or.inl ha)), w.complete_smul_atom_eq ha]

lemma smul_to_near_litter_eq_of_precise_at
  {π : near_litter_perm} (hπ : (w.complete litter_perm).exactly_approximates π)
  {L : litter} (hL : (w.litter_map L).dom) (hw : w.precise_at hL)
  (hπL : π • L = ((w.litter_map L).get hL).1) :
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
        have := hw.fwd c hc₁ (by rwa hc₂),
        rw hc₂ at this,
        exact this, },
      { cases w.sandbox_litter_not_banned _,
        rw ← eq_of_mem_litter_set_of_mem_litter_set ha
          (local_perm.sandbox_subset_subset _ _ hdom),
        exact banned_litter.litter_dom L hL, }, },
    { by_contradiction h',
      simp only [near_litter_perm.is_exception, mem_litter_set, not_or_distrib, not_not, ha] at h,
      obtain ⟨b, hb, rfl⟩ := hw.diff
        (or.inr ⟨by rw [← hπL, h.2, smul_inv_smul, mem_litter_set], h'⟩),
      refine h' ((w.atom_mem b hb L hL).mp _),
      have := hπ.map_atom b (or.inl (or.inl hb)),
      rw [w.complete_smul_atom_eq hb] at this,
      rw [this, inv_smul_smul] at ha,
      exact ha, }, },
  { intro ha,
    -- TODO: probably possible to clean up `by_cases` into a `suffices`
    by_cases π⁻¹ • a ∈ w.atom_map.dom,
    { rw w.atom_mem _ h L hL,
      have := hπ.map_atom _ (or.inl (or.inl h)),
      rw w.complete_smul_atom_eq h at this,
      rw [this, smul_inv_smul],
      exact ha, },
    have haL : a ∈ litter_set ((w.litter_map L).get hL).fst,
    { by_contradiction h',
      obtain ⟨b, hb, rfl⟩ := hw.diff (or.inl ⟨ha, h'⟩),
      have := hπ.map_atom b (or.inl (or.inl hb)),
      rw [w.complete_smul_atom_eq hb] at this,
      rw [this, inv_smul_smul] at h,
      exact h hb, },
    by_contradiction h',
    have hex : π.is_exception a,
    { refine or.inr (λ h'', h' (h''.trans _)),
      rw [inv_smul_eq_iff, hπL],
      exact haL, },
    obtain ((hdom | ⟨b, hb₁, hb₂⟩) | hdom) := hπ.exception_mem a hex,
    { obtain ⟨b, hb₁, hb₂⟩ := hw.back ⟨hdom, ha⟩,
      have := hπ.map_atom b (or.inl (or.inl hb₁)),
      rw [w.complete_smul_atom_eq hb₁] at this,
      rw [this, smul_eq_iff_eq_inv_smul] at hb₂,
      rw hb₂ at hb₁,
      exact h hb₁, },
    { rw w.atom_map_or_else_of_dom hb₁ at hb₂,
      have := hπ.map_atom b (or.inl (or.inl hb₁)),
      rw [w.complete_smul_atom_eq hb₁, hb₂, ← inv_smul_eq_iff] at this,
      rw this at h,
      exact h hb₁, },
    { refine w.sandbox_litter_not_banned _,
      rw eq_of_mem_litter_set_of_mem_litter_set (local_perm.sandbox_subset_subset _ _ hdom) haL,
      exact banned_litter.litter_map L hL, }, },
end

lemma smul_near_litter_eq_of_precise_at
  {π : near_litter_perm} (hπ : (w.complete litter_perm).exactly_approximates π)
  {N : near_litter} (hN : (w.litter_map N.1).dom) (hw : w.precise_at hN)
  (hπL : π • N.1 = ((w.litter_map N.1).get hN).1) :
  ((π • N : near_litter) : set atom) = (w.litter_map N.1).get hN ∆ (π • (litter_set N.1 ∆ N)) :=
begin
  refine (near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul _ _).trans _,
  rw ← w.smul_to_near_litter_eq_of_precise_at hπ hN hw hπL,
  refl,
end

end weak_near_litter_approx

namespace weak_struct_approx

section

variables {β : type_index} (w : weak_struct_approx β)
  {litter_perm : extended_index β → local_perm litter}

noncomputable def complete (litter_perm : extended_index β → local_perm litter) : struct_approx β :=
λ B, (w B).complete (litter_perm B)

def precise : Prop := ∀ B, (w B).precise

lemma smul_atom_eq
  {π : struct_perm β} (hπ : (w.complete litter_perm).exactly_approximates π)
  {a : atom} {B : extended_index β} (ha : ((w B).atom_map a).dom) :
  struct_perm.derivative B π • a = ((w B).atom_map a).get ha :=
begin
  have := (w B).smul_atom_eq (hπ B) ha,
  rw struct_perm.of_bot_smul at this,
  exact this,
end

lemma smul_to_near_litter_eq_of_precise (hw : w.precise)
  {π : struct_perm β} (hπ : (w.complete litter_perm).exactly_approximates π)
  {L : litter} {B : extended_index β} (hL : ((w B).litter_map L).dom)
  (hπL : struct_perm.derivative B π • L = (((w B).litter_map L).get hL).1) :
  struct_perm.derivative B π • L.to_near_litter = ((w B).litter_map L).get hL :=
begin
  have := (w B).smul_to_near_litter_eq_of_precise_at (hπ B) hL (hw B hL) _,
  { rw struct_perm.of_bot_smul at this,
    exact this, },
  { rw struct_perm.of_bot_smul,
    exact hπL, },
end

lemma smul_near_litter_eq_of_precise (hw : w.precise)
  {π : struct_perm β} (hπ : (w.complete litter_perm).exactly_approximates π)
  {N : near_litter} {B : extended_index β} (hN : ((w B).litter_map N.1).dom)
  (hπL : struct_perm.derivative B π • N.1 = (((w B).litter_map N.1).get hN).1) :
  ((struct_perm.derivative B π • N : near_litter) : set atom) =
  ((w B).litter_map N.1).get hN ∆ (struct_perm.derivative B π • (litter_set N.1 ∆ N)) :=
begin
  have := (w B).smul_near_litter_eq_of_precise_at (hπ B) hN (hw B hN) _,
  { rw struct_perm.of_bot_smul at this,
    exact this, },
  { rw struct_perm.of_bot_smul,
    exact hπL, },
end

end

variables {α : Λ} [position_data.{}] [phase_2_assumptions α] {β : Iio α}
  {litter_perm : extended_index β → local_perm litter}

/-- A weak structural approximation *supports* a tangle if it defines an image for everything
in the reduction of its designated support. -/
structure supports (w : weak_struct_approx β) (t : tangle β) : Prop :=
(atom_mem : ∀ a B, (inl a, B) ∈ reduction α (designated_support t : set (support_condition β)) →
  ((w B).atom_map a).dom)
(litter_mem : ∀ (L : litter) B,
  (inr L.to_near_litter, B) ∈ reduction α (designated_support t : set (support_condition β)) →
  ((w B).litter_map L).dom)

/-- Two weak structural approximations are *compatible* for a tangle if they both support the
tangle and agree on the reduction of its designated support. -/
structure compatible (w v : weak_struct_approx β) (t : tangle β) : Prop :=
(w_supports : w.supports t)
(v_supports : v.supports t)
(atom_map : ∀ a B ha, ((w B).atom_map a).get (w_supports.atom_mem a B ha) =
  ((v B).atom_map a).get (v_supports.atom_mem a B ha))
(litter_map : ∀ L B hL, ((w B).litter_map L).get (w_supports.litter_mem L B hL) =
  ((v B).litter_map L).get (v_supports.litter_mem L B hL))

/-- The action of a weak structural approximation on support conditions. -/
noncomputable def support_condition_map_or_else (w : weak_struct_approx β) :
  support_condition β → support_condition β
| (inl a, B) := (inl ((w B).atom_map_or_else a), B)
| (inr N, B) := (inr ((w B).near_litter_map_or_else N), B)

def coherent_base (w : weak_struct_approx β) (litter_perm : extended_index β → local_perm litter) :
  Prop :=
∀ L B hL, flexible α L B → litter_perm B L = (((w B).litter_map L).get hL).fst

def coherent_coe (w : weak_struct_approx β) (litter_perm : extended_index β → local_perm litter) :
  Prop :=
∀ {π : allowable β} (hπ : (w.complete litter_perm).exactly_approximates π.to_struct_perm)
  (γ : Iic α) (δ ε : Iio α) (hδ : (δ : Λ) < γ) (hε : (ε : Λ) < γ) (hδε : δ ≠ ε)
  (C : path (β : type_index) γ) (t : tangle δ) (hL)
  (hc : ∀ (c : support_condition δ), c ∈ (designated_support t).carrier →
    π • (show support_condition β, from (c.fst, (C.cons (coe_lt hδ)).comp c.snd)) =
      w.support_condition_map_or_else (c.fst, (C.cons (coe_lt hδ)).comp c.snd)),
  f_map (subtype.coe_injective.ne (Iio.coe_injective.ne hδε))
      (show tangle δ, from
        (show allowable δ, from allowable_derivative (γ : Iic_index α) δ (coe_lt_coe.mpr hδ)
          (allowable.derivative
            (show path ((β : Iic_index α) : type_index) (γ : Iic_index α), from C) π)) • t) =
    (((w ((C.cons (coe_lt hε)).cons (bot_lt_coe _))).litter_map
      (f_map (subtype.coe_injective.ne (Iio.coe_injective.ne hδε)) t)).get hL).fst

def coherent_bot (w : weak_struct_approx β) (litter_perm : extended_index β → local_perm litter) :
  Prop :=
∀ {π : allowable β} (hπ : (w.complete litter_perm).exactly_approximates π.to_struct_perm)
  (γ : Iic α) (ε : Iio α) (hε : (ε : Λ) < γ)
  (C : path (β : type_index) γ) (a : tangle ⊥) (hL)
  (hc : struct_perm.derivative (C.cons (bot_lt_coe _)) π.to_struct_perm • a =
    (w (C.cons (bot_lt_coe _))).atom_map_or_else a),
  f_map (show ((⊥ : Iio_index α) : type_index) ≠ (ε : Iio_index α),
    from subtype.coe_injective.ne Iio_index.bot_ne_coe)
      ((struct_perm.derivative (C.cons (bot_lt_coe _))) π.to_struct_perm • a) =
    (((w ((C.cons (coe_lt hε)).cons (bot_lt_coe _))).litter_map
      (f_map (show (⊥ : type_index) ≠ (ε : Λ), from bot_ne_coe) a)).get hL).fst

@[mk_iff] structure coherent (w : weak_struct_approx β)
  (litter_perm : extended_index β → local_perm litter) : Prop :=
(base : w.coherent_base litter_perm)
(coe : w.coherent_coe litter_perm)
(bot : w.coherent_bot litter_perm)

lemma smul_litter_eq_of_supports (w : weak_struct_approx β)
  (hw : w.precise) (hwc : w.coherent litter_perm)
  (hl : ∀ B, {L | flexible α L B} ⊆ (litter_perm B).domain)
  {π : allowable β} (hπ : (w.complete litter_perm).exactly_approximates π.to_struct_perm)
  (t : tangle β) (h : w.supports t)
  (d : support_condition β) (hd : d ∈ designated_support t)
  (B : extended_index β) (L : litter)
  (ih : ∀ (e : support_condition β),
    relation.trans_gen (constrains α β) e (inr L.to_near_litter, B) →
    π • e = w.support_condition_map_or_else e)
  (hc : relation.refl_trans_gen (constrains α β) (inr L.to_near_litter, B) d) :
  struct_perm.derivative B π.to_struct_perm • L =
  (((w B).litter_map L).get
    (h.litter_mem L B ⟨⟨d, hd, refl_trans_gen_near_litter hc⟩, reduced.mk_litter _ _⟩)).fst :=
begin
  by_cases hflex : inflexible α L B,
  rw inflexible_iff at hflex,
  obtain (⟨γ, δ, ε, hδ, hε, hδε, C, t, rfl, rfl⟩ | ⟨γ, ε, hε, C, a, rfl, rfl⟩) := hflex,
  { have hc := λ c hc, ih _ (relation.trans_gen.single $ constrains.f_map hδ hε hδε C t c hc),
    have := smul_f_map (δ : Iio_index α) ε _ _ (Iio.coe_injective.ne hδε)
      (allowable.derivative
        (show path ((β : Iic_index α) : type_index) (γ : Iic_index α), from C) π) t,
    rw [← allowable.derivative_cons_apply, allowable.derivative_smul,
      ← struct_perm.derivative_bot_smul, ← struct_perm.derivative_cons] at this,
    refine this.trans (hwc.coe hπ γ δ ε hδ hε hδε C t _ hc), },
  { have hc : (_, _) = (_, _) := ih _ (relation.trans_gen.single $ constrains.f_map_bot hε C a),
    simp only [smul_inl, prod.mk.inj_iff, eq_self_iff_true, and_true] at hc,
    have := smul_f_map (⊥ : Iio_index α) ε _ _ _
      (allowable.derivative
        (show path ((β : Iic_index α) : type_index) (γ : Iic_index α), from C) π) a,
    rw [← allowable.derivative_cons_apply, allowable.derivative_smul,
      ← struct_perm.derivative_bot_smul, ← struct_perm.derivative_cons] at this,
    rw ← hwc.bot hπ γ ε hε C a _ hc,
    refine this.trans _,
    all_goals { sorry, }, },
  { rw [← struct_perm.of_bot_smul, ← (hπ B).map_litter _ (hl B hflex)],
    refine ((w B).complete_smul_litter_eq L).trans _,
    exact hwc.base L B (h.litter_mem L B
      ⟨⟨d, hd, refl_trans_gen_near_litter hc⟩, reduced.mk_litter _ _⟩) hflex, },
end

lemma smul_support_condition_eq (w : weak_struct_approx β)
  (hw : w.precise) (hwc : w.coherent litter_perm)
  (hl : ∀ B, {L | flexible α L B} ⊆ (litter_perm B).domain)
  {π : allowable β} (hπ : (w.complete litter_perm).exactly_approximates π.to_struct_perm)
  (t : tangle β) (h : w.supports t)
  (c d : support_condition β)
  (hc : relation.refl_trans_gen (constrains α β) c d)
  (hd : d ∈ designated_support t) :
  π • c = w.support_condition_map_or_else c :=
begin
  revert d,
  refine (constrains_wf α β).trans_gen.induction c _,
  rintros c ih d hc hd,
  obtain ⟨a | N, B⟩ := c,
  { refine prod.ext _ rfl,
    change inl _ = inl _,
    refine congr_arg inl _,
    rw [w.smul_atom_eq hπ (h.atom_mem a B ⟨⟨d, hd, hc⟩, reduced.mk_atom a B⟩),
      weak_near_litter_approx.atom_map_or_else_of_dom], },
  refine prod.ext _ rfl,
  change inr _ = inr _,
  refine congr_arg inr (set_like.coe_injective _),
  have ih' := λ e he, ih e (relation.trans_gen.single he) d
    (relation.refl_trans_gen.head he hc) hd,
  rw w.smul_near_litter_eq_of_precise hw hπ (h.litter_mem N.1 B _) _,
  { simp only [weak_near_litter_approx.near_litter_map_or_else,
      near_litter.coe_mk, subtype.coe_mk],
    rw (w B).litter_map_or_else_of_dom (h.litter_mem N.1 B _),
    congr' 1,
    ext a : 1,
    rw [mem_smul_set, mem_image],
    split,
    { rintro ⟨b, hb₁, hb₂⟩,
      have : (_, _) = (_, _) := ih' _ (constrains.symm_diff N _ hb₁ B),
      simp only [smul_inl, smul_inv_smul, prod.mk.inj_iff] at this,
      rw this.1 at hb₂,
      exact ⟨b, hb₁, hb₂⟩, },
    { rintro ⟨b, hb₁, hb₂⟩,
      have : (_, _) = (_, _) := ih' _ (constrains.symm_diff N _ hb₁ B),
      simp only [smul_inl, smul_inv_smul, prod.mk.inj_iff] at this,
      rw ← this.1 at hb₂,
      exact ⟨b, hb₁, hb₂⟩, },
    { exact ⟨⟨d, hd, refl_trans_gen_near_litter hc⟩, reduced.mk_litter _ _⟩, }, },
  refine w.smul_litter_eq_of_supports hw hwc hl hπ t h d hd B N.1 _ (refl_trans_gen_near_litter hc),
  exact λ e he, ih e (trans_gen_near_litter he) d
    (relation.refl_trans_gen.trans he.to_refl (refl_trans_gen_near_litter hc)) hd,
end

lemma smul_eq_smul_tangle (w v : weak_struct_approx β)
  (hw : w.precise) (hv : v.precise)
  (hwc : w.coherent litter_perm) (hvc : v.coherent litter_perm)
  (hl : ∀ B, {L | flexible α L B} ⊆ (litter_perm B).domain)
  {πw πv : allowable β} (hπw : (w.complete litter_perm).exactly_approximates πw.to_struct_perm)
  (hπv : (v.complete litter_perm).exactly_approximates πv.to_struct_perm)
  (t : tangle β) (h : compatible w v t) :
  πw • t = πv • t :=
begin
  rw [smul_eq_iff_eq_inv_smul, smul_smul],
  symmetry,
  refine (designated_support t).supports _ _,
  intros c hc,
  rw [mul_smul, inv_smul_eq_iff],
  symmetry,
  rw smul_support_condition_eq w hw hwc hl hπw t h.w_supports c c relation.refl_trans_gen.refl hc,
  rw smul_support_condition_eq v hv hvc hl hπv t h.v_supports c c relation.refl_trans_gen.refl hc,
  obtain ⟨a | N, B⟩ := c,
  { simp only [support_condition_map_or_else, prod.mk.inj_iff, eq_self_iff_true, and_true],
    rw [(w B).atom_map_or_else_of_dom, (v B).atom_map_or_else_of_dom],
    refine h.atom_map a B _,
    exact ⟨⟨_, hc, relation.refl_trans_gen.refl⟩, reduced.mk_atom _ _⟩, },
  { simp only [support_condition_map_or_else, prod.mk.inj_iff, eq_self_iff_true, and_true,
      weak_near_litter_approx.near_litter_map_or_else],
    refine set_like.coe_injective _,
    simp only [near_litter.coe_mk, subtype.coe_mk],
    congr' 1,
    { rw [(w B).litter_map_or_else_of_dom, (v B).litter_map_or_else_of_dom, h.litter_map N.1 B _],
      exact ⟨⟨_, hc, refl_trans_gen_near_litter relation.refl_trans_gen.refl⟩,
        reduced.mk_litter _ _⟩, },
    { ext a : 1,
      rw [mem_image, mem_image],
      split;
      rintro ⟨b, hb₁, hb₂⟩;
      refine ⟨b, hb₁, _⟩;
      rw [← hb₂, (w B).atom_map_or_else_of_dom, (v B).atom_map_or_else_of_dom],
      { refine (h.atom_map b B _).symm,
        exact ⟨⟨_, hc, relation.refl_trans_gen.single (constrains.symm_diff N b hb₁ B)⟩,
          reduced.mk_atom _ _⟩, },
      { refine h.atom_map b B _,
        exact ⟨⟨_, hc, relation.refl_trans_gen.single (constrains.symm_diff N b hb₁ B)⟩,
          reduced.mk_atom _ _⟩, }, }, },
end

end weak_struct_approx

end con_nf
