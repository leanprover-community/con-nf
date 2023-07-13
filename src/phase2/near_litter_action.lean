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
# Structural actions
-/

/-- Noncomputably eliminates a disjunction into a (possibly predicative) universe. -/
noncomputable def _root_.or.elim' {α : Sort*} {p q : Prop}
  (h : p ∨ q) (f : p → α) (g : q → α) : α :=
if hp : p then f hp else g (h.resolve_left hp)

lemma _root_.or.elim'_left {α : Sort*} {p q : Prop}
  (h : p ∨ q) (f : p → α) (g : q → α) (hp : p) : h.elim' f g = f hp :=
by rw [or.elim', dif_pos hp]

lemma _root_.or.elim'_right {α : Sort*} {p q : Prop}
  (h : p ∨ q) (f : p → α) (g : q → α) (hp : ¬p) : h.elim' f g = g (h.resolve_left hp) :=
by rw [or.elim', dif_neg hp]

/-- A *near-litter action* is a partial function from atoms to atoms and a partial
function from litters to near-litters, both of which have small domain.
The image of a litter under the `litter_map` should be interpreted as the intended *precise* image
of this litter under an allowable permutation. -/
@[ext] structure near_litter_action :=
(atom_map : atom →. atom)
(litter_map : litter →. near_litter)
(atom_map_dom_small : small atom_map.dom)
(litter_map_dom_small : small litter_map.dom)

/-- A near litter action in which the atom and litter maps are injective (in suitable senses) and
cohere in the sense that images of atoms in litters are mapped to atoms inside the corresponding
near-litters. -/
structure near_litter_action.lawful (φ : near_litter_action) : Prop :=
(atom_map_injective : ∀ ⦃a b⦄ ha hb, (φ.atom_map a).get ha = (φ.atom_map b).get hb → a = b)
(litter_map_injective : ∀ ⦃L₁ L₂ : litter⦄ hL₁ hL₂,
  (((φ.litter_map L₁).get hL₁ : set atom) ∩ (φ.litter_map L₂).get hL₂).nonempty → L₁ = L₂)
(atom_mem : ∀ (a : atom) ha L hL, a.1 = L ↔ (φ.atom_map a).get ha ∈ (φ.litter_map L).get hL)

namespace near_litter_action

variable (φ : near_litter_action)

/-- A litter that is not allowed to be used as a sandbox because it appears somewhere that
we need to preserve. -/
@[mk_iff] inductive banned_litter : litter → Prop
| atom_dom (a : atom) : (φ.atom_map a).dom → banned_litter a.1
| litter_dom (L : litter) : (φ.litter_map L).dom → banned_litter L
| atom_map (a : atom) (h) : banned_litter ((φ.atom_map a).get h).1
| litter_map (L : litter) (h) : banned_litter ((φ.litter_map L).get h).1
| diff (L : litter) (h) (a : atom) :
    a ∈ ((φ.litter_map L).get h : set atom) \ litter_set ((φ.litter_map L).get h).1 →
    banned_litter a.1

lemma banned_litter.mem_map (a : atom) (L : litter) (hL)
  (ha : a ∈ ((φ.litter_map L).get hL : set atom)) : φ.banned_litter a.1 :=
begin
  by_cases a.1 = ((φ.litter_map L).get hL).1,
  { rw h,
    exact banned_litter.litter_map L hL, },
  { exact banned_litter.diff L hL a ⟨ha, h⟩, },
end

/-- There are only a small amount of banned litters. -/
lemma banned_litter_small : small {L | φ.banned_litter L} :=
begin
  simp only [banned_litter_iff, mem_diff, set_like.mem_coe, mem_litter_set],
  refine small.union _ (small.union _ (small.union _ (small.union _ _))),
  { refine lt_of_le_of_lt _ φ.atom_map_dom_small,
    refine ⟨⟨λ a, ⟨_, a.prop.some_spec.1⟩, λ a₁ a₂ h, _⟩⟩,
    simp only [subtype.mk_eq_mk, prod.mk.inj_iff] at h,
    have := a₁.prop.some_spec.2,
    rw h at this,
    exact subtype.coe_injective (this.trans a₂.prop.some_spec.2.symm), },
  { refine lt_of_le_of_lt _ φ.litter_map_dom_small,
    refine ⟨⟨λ L, ⟨_, L.prop⟩, λ L₁ L₂ h, _⟩⟩,
    simp only [subtype.mk_eq_mk, prod.mk.inj_iff] at h,
    exact subtype.coe_injective h, },
  { refine lt_of_le_of_lt _ φ.atom_map_dom_small,
    refine ⟨⟨λ L, ⟨_, L.prop.some_spec.some⟩, λ L₁ L₂ h, _⟩⟩,
    simp only [subtype.mk_eq_mk, prod.mk.inj_iff] at h,
    have := L₁.prop.some_spec.some_spec,
    simp_rw h at this,
    exact subtype.coe_injective (this.trans L₂.prop.some_spec.some_spec.symm), },
  { refine lt_of_le_of_lt _ φ.litter_map_dom_small,
    refine ⟨⟨λ L, ⟨_, L.prop.some_spec.some⟩, λ L₁ L₂ h, _⟩⟩,
    simp only [subtype.mk_eq_mk, prod.mk.inj_iff] at h,
    have := L₁.prop.some_spec.some_spec,
    simp_rw h at this,
    exact subtype.coe_injective (this.trans L₂.prop.some_spec.some_spec.symm), },
  { have : small ⋃ (L : litter) (h : (φ.litter_map L).dom),
      ((φ.litter_map L).get h : set atom) \ litter_set ((φ.litter_map L).get h).1,
    { refine small.bUnion _ _,
      { refine lt_of_le_of_lt _ φ.litter_map_dom_small,
        refine ⟨⟨λ N, ⟨_, N.prop⟩, λ N₁ N₂ h, _⟩⟩,
        simp only [subtype.mk_eq_mk, prod.mk.inj_iff] at h,
        exact subtype.coe_inj.mp h, },
      { intros L hL,
        refine small.mono _ ((φ.litter_map L).get hL).2.prop,
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

lemma mk_not_banned_litter : #{L | ¬φ.banned_litter L} = #μ :=
begin
  have := mk_sum_compl {L | φ.banned_litter L},
  rw [compl_set_of, mk_litter] at this,
  rw [← this, add_eq_right],
  { by_contra' h,
    have h' := add_le_add (le_of_lt φ.banned_litter_small) h.le,
    rw this at h',
    refine not_lt_of_le h' _,
    refine cardinal.add_lt_of_lt μ_strong_limit.is_limit.aleph_0_le κ_lt_μ _,
    exact lt_of_le_of_lt κ_regular.aleph_0_le κ_lt_μ, },
  { by_contra' h,
    have h' := add_le_add (le_of_lt φ.banned_litter_small) h.le,
    rw this at h',
    refine not_lt_of_le h' _,
    refine cardinal.add_lt_of_lt μ_strong_limit.is_limit.aleph_0_le κ_lt_μ _,
    exact lt_trans φ.banned_litter_small κ_lt_μ, },
end

lemma not_banned_litter_nonempty : nonempty {L | ¬φ.banned_litter L} :=
by simp only [← mk_ne_zero_iff, mk_not_banned_litter, ne.def, mk_ne_zero, not_false_iff]

/-- The *sandbox litter* for a near-litter action is an arbitrarily chosen litter that
isn't banned. -/
noncomputable def sandbox_litter : litter := φ.not_banned_litter_nonempty.some

lemma sandbox_litter_not_banned : ¬φ.banned_litter φ.sandbox_litter :=
φ.not_banned_litter_nonempty.some.prop

/-- If `a` is in the domain, this is the atom map. Otherwise, this gives an arbitrary atom. -/
noncomputable def atom_map_or_else (a : atom) : atom := (φ.atom_map a).get_or_else (arbitrary atom)

lemma atom_map_or_else_of_dom {a : atom} (ha : (φ.atom_map a).dom) :
  φ.atom_map_or_else a = (φ.atom_map a).get ha :=
by rw [atom_map_or_else, part.get_or_else_of_dom]

lemma mk_atom_map_image_le_mk_sandbox :
  #(φ.atom_map.dom ∆ (φ.atom_map_or_else '' φ.atom_map.dom) : set atom) ≤
    #(litter_set φ.sandbox_litter) :=
begin
  rw mk_litter_set,
  refine le_trans (mk_subtype_mono symm_diff_subset_union) (le_trans (mk_union_le _ _) _),
  refine add_le_of_le κ_regular.aleph_0_le _ _,
  exact le_of_lt φ.atom_map_dom_small,
  exact le_trans mk_image_le (le_of_lt φ.atom_map_dom_small),
end

lemma disjoint_sandbox :
  disjoint (φ.atom_map.dom ∪ φ.atom_map_or_else '' φ.atom_map.dom) (litter_set φ.sandbox_litter) :=
begin
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem],
  rintros a ⟨ha₁, ha₂⟩,
  rw mem_litter_set at ha₂,
  have hnb := φ.sandbox_litter_not_banned,
  rw ← ha₂ at hnb,
  cases ha₁,
  { exact hnb (banned_litter.atom_dom a ha₁), },
  { refine hnb _,
    simp only [mem_image, pfun.mem_dom] at ha₁,
    obtain ⟨b, ⟨_, hb, rfl⟩, rfl⟩ := ha₁,
    rw φ.atom_map_or_else_of_dom hb,
    exact banned_litter.atom_map b hb, },
end

lemma atom_map_or_else_injective (hφ : φ.lawful) : inj_on φ.atom_map_or_else φ.atom_map.dom :=
begin
  intros a ha b hb h,
  rw [φ.atom_map_or_else_of_dom ha, φ.atom_map_or_else_of_dom hb] at h,
  exact hφ.atom_map_injective ha hb h,
end

/-- If `L` is in the domain, this is the litter map.
Otherwise, this gives an arbitrary near-litter. -/
noncomputable def litter_map_or_else (L : litter) : near_litter :=
(φ.litter_map L).get_or_else (arbitrary near_litter)

lemma litter_map_or_else_of_dom {L : litter} (hL : (φ.litter_map L).dom) :
  φ.litter_map_or_else L = (φ.litter_map L).get hL :=
by rw [litter_map_or_else, part.get_or_else_of_dom]

noncomputable def rough_litter_map_or_else (L : litter) : litter :=
(φ.litter_map_or_else L).1

lemma rough_litter_map_or_else_of_dom {L : litter} (hL : (φ.litter_map L).dom) :
  φ.rough_litter_map_or_else L = ((φ.litter_map L).get hL).1 :=
by rw [rough_litter_map_or_else, litter_map_or_else_of_dom]

/-- The induced action on near-litters. -/
noncomputable def near_litter_map_or_else (N : near_litter) : near_litter :=
⟨(φ.litter_map_or_else N.fst).fst,
  φ.litter_map_or_else N.fst ∆ (φ.atom_map_or_else '' litter_set N.fst ∆ N),
  begin
    rw [is_near_litter, is_near, ← symm_diff_assoc],
    exact (φ.litter_map_or_else N.fst).snd.prop.symm_diff (small.image N.2.prop),
  end⟩

lemma _root_.con_nf.small.pfun_image {α β : Type*} {s : set α} (h : small s) {f : α →. β} :
  small (f.image s) :=
begin
  have : small (f '' s) := small.image h,
  refine small.image_subset part.some part.some_injective this _,
  rintro x ⟨y, ⟨z, hz₁, hz₂⟩, rfl⟩,
  exact ⟨z, hz₁, part.eq_some_iff.mpr hz₂⟩,
end

lemma near_litter_map_or_else_of_dom {N : near_litter} (h₁ : (φ.litter_map N.fst).dom)
  (h₂ : ∀ a ∈ litter_set N.fst ∆ N, (φ.atom_map a).dom) :
  φ.near_litter_map_or_else N =
  ⟨((φ.litter_map N.fst).get h₁).fst,
    (φ.litter_map N.fst).get h₁ ∆ (φ.atom_map.image $ litter_set N.fst ∆ N),
    begin
      rw [is_near_litter, is_near, ← symm_diff_assoc],
      exact ((φ.litter_map N.fst).get h₁).snd.prop.symm_diff (small.pfun_image N.2.prop),
    end⟩ :=
begin
  rw [← set_like.coe_set_eq, near_litter_map_or_else, near_litter.coe_mk,
    subtype.coe_mk, φ.litter_map_or_else_of_dom h₁],
  refine congr_arg _ _,
  ext a : 1,
  split,
  { rintro ⟨b, hb, rfl⟩,
    rw φ.atom_map_or_else_of_dom (h₂ b hb),
    exact ⟨b, hb, part.get_mem (h₂ b hb)⟩, },
  { rintro ⟨b, hb₁, hb₂, rfl⟩,
    refine ⟨b, hb₁, _⟩,
    rw φ.atom_map_or_else_of_dom, },
end

/-- An action is precise at a litter in its domain if all atoms in the symmetric
difference of its image are accounted for. -/
@[mk_iff] structure precise_at ⦃L : litter⦄ (hL : (φ.litter_map L).dom) : Prop :=
(diff : ((φ.litter_map L).get hL : set atom) ∆ litter_set ((φ.litter_map L).get hL).1 ⊆
  φ.atom_map.ran)
(fwd : ∀ a ha, (φ.atom_map a).get ha ∈ litter_set L → (φ.atom_map ((φ.atom_map a).get ha)).dom)
(back : φ.atom_map.dom ∩ (φ.litter_map L).get hL ⊆ φ.atom_map.ran)

/-- An action is precise if it is precise at every litter in its domain. -/
def precise : Prop := ∀ ⦃L⦄ (hL : (φ.litter_map L).dom), φ.precise_at hL

/-!
## Induced litter permutation
-/

lemma mk_dom_symm_diff_le :
  #↥(φ.litter_map.dom ∆ (φ.rough_litter_map_or_else '' φ.litter_map.dom)) ≤
  #{L : litter | ¬φ.banned_litter L} :=
begin
  rw mk_not_banned_litter,
  refine le_trans (le_of_lt _) κ_le_μ,
  exact small.symm_diff φ.litter_map_dom_small φ.litter_map_dom_small.image,
end

lemma aleph_0_le_not_banned_litter : ℵ₀ ≤ #{L | ¬φ.banned_litter L} :=
begin
  rw mk_not_banned_litter,
  exact μ_strong_limit.is_limit.aleph_0_le,
end

lemma disjoint_dom_not_banned_litter :
  disjoint (φ.litter_map.dom ∪ φ.rough_litter_map_or_else '' φ.litter_map.dom)
    {L : litter | ¬φ.banned_litter L} :=
begin
  simp only [set.disjoint_left, mem_union, pfun.mem_dom, mem_image, mem_set_of_eq, not_not],
  rintros _ (⟨_, hL, rfl⟩ | ⟨L, ⟨_, hL, rfl⟩, rfl⟩),
  { exact banned_litter.litter_dom _ hL, },
  { rw φ.rough_litter_map_or_else_of_dom hL,
    exact banned_litter.litter_map _ hL, },
end

lemma rough_litter_map_or_else_inj_on (hφ : φ.lawful) :
  inj_on φ.rough_litter_map_or_else φ.litter_map.dom :=
begin
  intros L₁ hL₁ L₂ hL₂ h,
  rw [φ.rough_litter_map_or_else_of_dom hL₁, φ.rough_litter_map_or_else_of_dom hL₂] at h,
  exact hφ.litter_map_injective hL₁ hL₂ (near_litter.inter_nonempty_of_fst_eq_fst h),
end

/-- A local permutation on the set of litters that occur in the domain or range of `w`.
This permutes both flexible and inflexible litters. -/
noncomputable def litter_perm' (hφ : φ.lawful) : local_perm litter :=
local_perm.complete
  φ.rough_litter_map_or_else
  φ.litter_map.dom
  {L | ¬φ.banned_litter L}
  φ.mk_dom_symm_diff_le
  φ.aleph_0_le_not_banned_litter
  φ.disjoint_dom_not_banned_litter
  (φ.rough_litter_map_or_else_inj_on hφ)

def id_on_banned (s : set litter) : local_perm litter := {
  to_fun := id,
  inv_fun := id,
  domain := {L | φ.banned_litter L} \ s,
  to_fun_domain' := λ L h, h,
  inv_fun_domain' := λ L h, h,
  left_inv' := λ L h, rfl,
  right_inv' := λ L h, rfl,
}

noncomputable def litter_perm (hφ : φ.lawful) : local_perm litter :=
local_perm.piecewise (φ.litter_perm' hφ) (φ.id_on_banned (φ.litter_perm' hφ).domain)
  (by rw ← set.subset_compl_iff_disjoint_left; exact λ L h, h.2)

lemma litter_perm'_apply_eq {φ : near_litter_action} {hφ : φ.lawful}
  (L : litter) (hL : L ∈ φ.litter_map.dom) :
  φ.litter_perm' hφ L = φ.rough_litter_map_or_else L :=
local_perm.complete_apply_eq _ _ _ hL

lemma litter_perm_apply_eq {φ : near_litter_action} {hφ : φ.lawful}
  (L : litter) (hL : L ∈ φ.litter_map.dom) :
  φ.litter_perm hφ L = φ.rough_litter_map_or_else L :=
begin
  rw ← litter_perm'_apply_eq L hL,
  exact local_perm.piecewise_apply_eq_left (or.inl (or.inl hL)),
end

lemma litter_perm'_domain_small (hφ : φ.lawful) : small (φ.litter_perm' hφ).domain :=
begin
  refine small.union (small.union φ.litter_map_dom_small φ.litter_map_dom_small.image) _,
  rw small,
  rw cardinal.mk_congr (local_perm.sandbox_subset_equiv _ _),
  simp only [mk_sum, mk_prod, mk_denumerable, lift_aleph_0, lift_uzero, lift_id],
  refine add_lt_of_lt κ_regular.aleph_0_le _ _;
    refine (mul_lt_of_lt κ_regular.aleph_0_le (lt_of_le_of_lt Λ_limit.aleph_0_le Λ_lt_κ) _);
    refine lt_of_le_of_lt (mk_subtype_mono (diff_subset _ _)) _,
  exact φ.litter_map_dom_small,
  exact φ.litter_map_dom_small.image,
end

lemma litter_perm_domain_small (hφ : φ.lawful) : small (φ.litter_perm hφ).domain :=
small.union (φ.litter_perm'_domain_small hφ) (small.mono (diff_subset _ _) φ.banned_litter_small)

variables {α : Λ} [position_data.{}] [phase_2_assumptions α] {β : Iio α} {A : extended_index β}

lemma mk_not_banned_litter_and_flexible : #{L | ¬φ.banned_litter L ∧ flexible α L A} = #μ :=
begin
  refine le_antisymm ((mk_subtype_le _).trans mk_litter.le) _,
  by_contra,
  rw not_le at h,
  have h₁ := cardinal.le_mk_diff_add_mk {L | flexible α L A} {L | φ.banned_litter L},
  rw [mk_flexible, diff_eq, inter_comm] at h₁,
  have h₂ := add_lt_of_lt μ_strong_limit.is_limit.aleph_0_le h
    (lt_trans φ.banned_litter_small κ_lt_μ),
  exact h₁.not_lt h₂,
end

lemma mk_dom_inter_flexible_symm_diff_le :
  #↥((φ.litter_map.dom ∩ {L | flexible α L A}) ∆
    (φ.rough_litter_map_or_else '' (φ.litter_map.dom ∩ {L | flexible α L A}))) ≤
  #{L : litter | ¬φ.banned_litter L ∧ flexible α L A} :=
begin
  rw mk_not_banned_litter_and_flexible,
  refine le_trans (le_of_lt _) κ_le_μ,
  exact small.symm_diff
    (small.mono (inter_subset_left _ _) φ.litter_map_dom_small)
    (small.mono (inter_subset_left _ _) φ.litter_map_dom_small).image,
end

lemma aleph_0_le_not_banned_litter_and_flexible : ℵ₀ ≤ #{L | ¬φ.banned_litter L ∧ flexible α L A} :=
begin
  rw mk_not_banned_litter_and_flexible,
  exact μ_strong_limit.is_limit.aleph_0_le,
end

lemma disjoint_dom_inter_flexible_not_banned_litter :
  disjoint ((φ.litter_map.dom ∩ {L | flexible α L A})
    ∪ φ.rough_litter_map_or_else '' (φ.litter_map.dom ∩ {L | flexible α L A}))
    {L : litter | ¬φ.banned_litter L ∧ flexible α L A} :=
begin
  refine disjoint_of_subset _ (inter_subset_left _ _) φ.disjoint_dom_not_banned_litter,
  rintros a (ha | ⟨b, hb, rfl⟩),
  exact or.inl ha.1,
  exact or.inr ⟨b, hb.1, rfl⟩,
end

lemma rough_litter_map_or_else_inj_on_dom_inter_flexible (hφ : φ.lawful) :
  inj_on φ.rough_litter_map_or_else (φ.litter_map.dom ∩ {L | flexible α L A}) :=
(φ.rough_litter_map_or_else_inj_on hφ).mono (inter_subset_left _ _)

noncomputable def flexible_litter_perm (hφ : φ.lawful) (A : extended_index β) :
  local_perm litter :=
local_perm.complete
  φ.rough_litter_map_or_else
  (φ.litter_map.dom ∩ {L | flexible α L A})
  {L | ¬φ.banned_litter L ∧ flexible α L A}
  φ.mk_dom_inter_flexible_symm_diff_le
  φ.aleph_0_le_not_banned_litter_and_flexible
  φ.disjoint_dom_inter_flexible_not_banned_litter
  (φ.rough_litter_map_or_else_inj_on_dom_inter_flexible hφ)

lemma flexible_litter_perm_apply_eq {φ : near_litter_action} {hφ : φ.lawful} (L : litter)
  (hL₁ : L ∈ φ.litter_map.dom) (hL₂ : flexible α L A) :
  φ.flexible_litter_perm hφ A L = φ.rough_litter_map_or_else L :=
local_perm.complete_apply_eq _ _ _ ⟨hL₁, hL₂⟩

lemma flexible_litter_perm_domain_small (hφ : φ.lawful) :
  small (φ.flexible_litter_perm hφ A).domain :=
begin
  refine small.union (small.union _ _) _,
  { exact φ.litter_map_dom_small.mono (inter_subset_left _ _) },
  { exact (φ.litter_map_dom_small.mono (inter_subset_left _ _)).image, },
  { rw small,
    rw cardinal.mk_congr (local_perm.sandbox_subset_equiv _ _),
    simp only [mk_sum, mk_prod, mk_denumerable, lift_aleph_0, lift_uzero, lift_id],
    refine add_lt_of_lt κ_regular.aleph_0_le _ _;
      refine (mul_lt_of_lt κ_regular.aleph_0_le (lt_of_le_of_lt Λ_limit.aleph_0_le Λ_lt_κ) _);
      refine lt_of_le_of_lt (mk_subtype_mono (diff_subset _ _)) _,
    exact φ.litter_map_dom_small.mono (inter_subset_left _ _),
    exact (φ.litter_map_dom_small.mono (inter_subset_left _ _)).image, },
end

/-!
# Completed permutations
-/

/-- A local permutation induced by completing the orbits of atoms in a near-litter action.
This function creates forward and backward images of atoms in the *sandbox litter*,
a litter which is away from the domain and range of the approximation in question, so it should
not interfere with other constructions. -/
noncomputable def complete_atom_perm (hφ : φ.lawful) : local_perm atom :=
local_perm.complete
  φ.atom_map_or_else
  φ.atom_map.dom
  (litter_set φ.sandbox_litter)
  φ.mk_atom_map_image_le_mk_sandbox
  (by simpa only [mk_litter_set] using κ_regular.aleph_0_le)
  φ.disjoint_sandbox
  (φ.atom_map_or_else_injective hφ)

lemma sandbox_subset_small : small (local_perm.sandbox_subset
  φ.mk_atom_map_image_le_mk_sandbox
  (by simpa only [mk_litter_set] using κ_regular.aleph_0_le)) :=
begin
  rw small,
  rw cardinal.mk_congr (local_perm.sandbox_subset_equiv _ _),
  simp only [mk_sum, mk_prod, mk_denumerable, lift_aleph_0, lift_uzero, lift_id],
  refine add_lt_of_lt κ_regular.aleph_0_le _ _;
    refine (mul_lt_of_lt κ_regular.aleph_0_le (lt_of_le_of_lt Λ_limit.aleph_0_le Λ_lt_κ) _);
    refine lt_of_le_of_lt (mk_subtype_mono (diff_subset _ _)) _,
  { exact φ.atom_map_dom_small, },
  { exact lt_of_le_of_lt mk_image_le φ.atom_map_dom_small, },
end

lemma complete_atom_perm_domain_small (hφ : φ.lawful): small (φ.complete_atom_perm hφ).domain :=
small.union (small.union φ.atom_map_dom_small
  (lt_of_le_of_lt mk_image_le φ.atom_map_dom_small)) φ.sandbox_subset_small

/-- A near-litter approximation built from this near-litter action.
Its action on atoms matches that of the action, and its rough action on litters
matches the given litter permutation. -/
noncomputable def complete (hφ : φ.lawful) (A : extended_index β) : near_litter_approx := {
  atom_perm := φ.complete_atom_perm hφ,
  litter_perm := φ.flexible_litter_perm hφ A,
  domain_small := λ L, small.mono (inter_subset_right _ _) (φ.complete_atom_perm_domain_small hφ),
}

variable {litter_perm : local_perm litter}

lemma complete_atom_perm_apply_eq (hφ : φ.lawful) {a : atom} (ha : (φ.atom_map a).dom) :
  φ.complete_atom_perm hφ a = (φ.atom_map a).get ha :=
by rwa [complete_atom_perm, local_perm.complete_apply_eq, atom_map_or_else_of_dom]

lemma complete_smul_atom_eq {hφ : φ.lawful} {a : atom} (ha : (φ.atom_map a).dom) :
  φ.complete hφ A • a = (φ.atom_map a).get ha := φ.complete_atom_perm_apply_eq hφ ha

@[simp] lemma complete_smul_litter_eq {hφ : φ.lawful} (L : litter) :
  φ.complete hφ A • L = φ.flexible_litter_perm hφ A L := rfl

lemma smul_atom_eq {hφ : φ.lawful}
  {π : near_litter_perm} (hπ : (φ.complete hφ A).exactly_approximates π)
  {a : atom} (ha : (φ.atom_map a).dom) :
  π • a = (φ.atom_map a).get ha :=
by rw [← hπ.map_atom a (or.inl (or.inl ha)), φ.complete_smul_atom_eq ha]

lemma smul_to_near_litter_eq_of_precise_at {hφ : φ.lawful}
  {π : near_litter_perm} (hπ : (φ.complete hφ A).exactly_approximates π)
  {L : litter} (hL : (φ.litter_map L).dom) (hφL : φ.precise_at hL)
  (hπL : π • L = ((φ.litter_map L).get hL).1) :
  π • L.to_near_litter = (φ.litter_map L).get hL :=
begin
  refine set_like.coe_injective _,
  ext a : 1,
  simp only [mem_smul_set_iff_inv_smul_mem, near_litter_perm.coe_smul, litter.coe_to_near_litter,
    mem_litter_set, set_like.mem_coe],
  split,
  { intro ha,
    by_cases π.is_exception a,
    { suffices h' : π⁻¹ • a ∈ φ.atom_map.dom,
      { rw hφ.atom_mem _ h' L hL at ha,
        have := hπ.map_atom _ (or.inl (or.inl h')),
        rw φ.complete_smul_atom_eq h' at this,
        rw [this, smul_inv_smul] at ha,
        exact ha, },
      rw ← hπ.symm_map_atom a (hπ.exception_mem _ h) at ha ⊢,
      obtain ((hdom | hdom) | hdom) := (φ.complete hφ A).atom_perm.symm.map_domain
        (hπ.exception_mem _ h),
      { exact hdom, },
      { obtain ⟨c, hc₁, hc₂⟩ := hdom,
        rw φ.atom_map_or_else_of_dom hc₁ at hc₂,
        have := hφL.fwd c hc₁ (by rwa hc₂),
        rw hc₂ at this,
        exact this, },
      { cases φ.sandbox_litter_not_banned _,
        rw ← eq_of_mem_litter_set_of_mem_litter_set ha
          (local_perm.sandbox_subset_subset _ _ hdom),
        exact banned_litter.litter_dom L hL, }, },
    { by_contradiction h',
      simp only [near_litter_perm.is_exception, mem_litter_set, not_or_distrib, not_not, ha] at h,
      obtain ⟨b, hb, rfl⟩ := hφL.diff
        (or.inr ⟨by rw [← hπL, h.2, smul_inv_smul, mem_litter_set], h'⟩),
      refine h' ((hφ.atom_mem b hb L hL).mp _),
      have := hπ.map_atom b (or.inl (or.inl hb)),
      rw [φ.complete_smul_atom_eq hb] at this,
      rw [this, inv_smul_smul] at ha,
      exact ha, }, },
  { intro ha,
    -- TODO: probably possible to clean up `by_cases` into a `suffices`
    by_cases π⁻¹ • a ∈ φ.atom_map.dom,
    { rw hφ.atom_mem _ h L hL,
      have := hπ.map_atom _ (or.inl (or.inl h)),
      rw φ.complete_smul_atom_eq h at this,
      rw [this, smul_inv_smul],
      exact ha, },
    have haL : a ∈ litter_set ((φ.litter_map L).get hL).fst,
    { by_contradiction h',
      obtain ⟨b, hb, rfl⟩ := hφL.diff (or.inl ⟨ha, h'⟩),
      have := hπ.map_atom b (or.inl (or.inl hb)),
      rw [φ.complete_smul_atom_eq hb] at this,
      rw [this, inv_smul_smul] at h,
      exact h hb, },
    by_contradiction h',
    have hex : π.is_exception a,
    { refine or.inr (λ h'', h' (h''.trans _)),
      rw [inv_smul_eq_iff, hπL],
      exact haL, },
    obtain ((hdom | ⟨b, hb₁, hb₂⟩) | hdom) := hπ.exception_mem a hex,
    { obtain ⟨b, hb₁, hb₂⟩ := hφL.back ⟨hdom, ha⟩,
      have := hπ.map_atom b (or.inl (or.inl hb₁)),
      rw [φ.complete_smul_atom_eq hb₁] at this,
      rw [this, smul_eq_iff_eq_inv_smul] at hb₂,
      rw hb₂ at hb₁,
      exact h hb₁, },
    { rw φ.atom_map_or_else_of_dom hb₁ at hb₂,
      have := hπ.map_atom b (or.inl (or.inl hb₁)),
      rw [φ.complete_smul_atom_eq hb₁, hb₂, ← inv_smul_eq_iff] at this,
      rw this at h,
      exact h hb₁, },
    { refine φ.sandbox_litter_not_banned _,
      rw eq_of_mem_litter_set_of_mem_litter_set (local_perm.sandbox_subset_subset _ _ hdom) haL,
      exact banned_litter.litter_map L hL, }, },
end

lemma smul_near_litter_eq_of_precise_at {hφ : φ.lawful}
  {π : near_litter_perm} (hπ : (φ.complete hφ A).exactly_approximates π)
  {N : near_litter} (hN : (φ.litter_map N.1).dom) (hw : φ.precise_at hN)
  (hπL : π • N.1 = ((φ.litter_map N.1).get hN).1) :
  ((π • N : near_litter) : set atom) = (φ.litter_map N.1).get hN ∆ (π • (litter_set N.1 ∆ N)) :=
begin
  refine (near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul _ _).trans _,
  rw ← φ.smul_to_near_litter_eq_of_precise_at hπ hN hw hπL,
  refl,
end

end near_litter_action

end con_nf
