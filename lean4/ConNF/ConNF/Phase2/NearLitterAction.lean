import Mathlib.Data.Pfun
import ConNF.Phase2.Approximation
import ConNF.Phase2.CompleteOrbit
import ConNF.Phase2.Reduction

#align_import phase2.near_litter_action

open Cardinal Quiver Set Sum WithBot

open scoped Cardinal Classical Pointwise

universe u

namespace ConNf

variable [Params.{u}]

/-!
# Structural actions
-/


/-- Noncomputably eliminates a disjunction into a (possibly predicative) universe. -/
noncomputable def Or.elim' {α : Sort _} {p q : Prop} (h : p ∨ q) (f : p → α) (g : q → α) : α :=
  if hp : p then f hp else g (h.resolve_left hp)

theorem Or.elim'_left {α : Sort _} {p q : Prop} (h : p ∨ q) (f : p → α) (g : q → α) (hp : p) :
    h.elim' f g = f hp := by rw [Or.elim', dif_pos hp]

theorem Or.elim'_right {α : Sort _} {p q : Prop} (h : p ∨ q) (f : p → α) (g : q → α) (hp : ¬p) :
    h.elim' f g = g (h.resolve_left hp) := by rw [Or.elim', dif_neg hp]

/-- A *near-litter action* is a partial function from atoms to atoms and a partial
function from litters to near-litters, both of which have small domain.
The image of a litter under the `litter_map` should be interpreted as the intended *precise* image
of this litter under an allowable permutation. -/
@[ext]
structure NearLitterAction where
  atomMap : Atom →. Atom
  litterMap : Litter →. NearLitter
  atomMap_dom_small : Small atom_map.Dom
  litterMap_dom_small : Small litter_map.Dom

/-- A near litter action in which the atom and litter maps are injective (in suitable senses) and
cohere in the sense that images of atoms in litters are mapped to atoms inside the corresponding
near-litters. -/
structure NearLitterAction.Lawful (φ : NearLitterAction) : Prop where
  atomMap_injective : ∀ ⦃a b⦄ (ha hb), (φ.atomMap a).get ha = (φ.atomMap b).get hb → a = b
  litterMap_injective :
    ∀ ⦃L₁ L₂ : Litter⦄ (hL₁ hL₂),
      (((φ.litterMap L₁).get hL₁ : Set Atom) ∩ (φ.litterMap L₂).get hL₂).Nonempty → L₁ = L₂
  atom_mem : ∀ (a : Atom) (ha L hL), a.1 = L ↔ (φ.atomMap a).get ha ∈ (φ.litterMap L).get hL

namespace NearLitterAction

variable (φ : NearLitterAction)

/-- A litter that is not allowed to be used as a sandbox because it appears somewhere that
we need to preserve. -/
@[mk_iff]
inductive BannedLitter : Litter → Prop
  | atom_dom (a : Atom) : (φ.atomMap a).Dom → banned_litter a.1
  | litter_dom (L : Litter) : (φ.litterMap L).Dom → banned_litter L
  | atom_map (a : Atom) (h) : banned_litter ((φ.atomMap a).get h).1
  | litter_map (L : Litter) (h) : banned_litter ((φ.litterMap L).get h).1
  |
  diff (L : Litter) (h) (a : Atom) :
    a ∈ ((φ.litterMap L).get h : Set Atom) \ litterSet ((φ.litterMap L).get h).1 → banned_litter a.1

theorem BannedLitter.memMap (a : Atom) (L : Litter) (hL)
    (ha : a ∈ ((φ.litterMap L).get hL : Set Atom)) : φ.BannedLitter a.1 :=
  by
  by_cases a.1 = ((φ.litter_map L).get hL).1
  · rw [h]
    exact banned_litter.litter_map L hL
  · exact banned_litter.diff L hL a ⟨ha, h⟩

/-- There are only a small amount of banned litters. -/
theorem bannedLitter_small : Small {L | φ.BannedLitter L} :=
  by
  simp only [banned_litter_iff, mem_diff, SetLike.mem_coe, mem_litter_set]
  refine' small.union _ (small.union _ (small.union _ (small.union _ _)))
  · refine' lt_of_le_of_lt _ φ.atom_map_dom_small
    refine' ⟨⟨fun a => ⟨_, a.prop.some_spec.1⟩, fun a₁ a₂ h => _⟩⟩
    simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff] at h
    have := a₁.prop.some_spec.2
    rw [h] at this
    exact Subtype.coe_injective (this.trans a₂.prop.some_spec.2.symm)
  · refine' lt_of_le_of_lt _ φ.litter_map_dom_small
    refine' ⟨⟨fun L => ⟨_, L.Prop⟩, fun L₁ L₂ h => _⟩⟩
    simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff] at h
    exact Subtype.coe_injective h
  · refine' lt_of_le_of_lt _ φ.atom_map_dom_small
    refine' ⟨⟨fun L => ⟨_, L.prop.some_spec.some⟩, fun L₁ L₂ h => _⟩⟩
    simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff] at h
    have := L₁.prop.some_spec.some_spec
    simp_rw [h] at this
    exact Subtype.coe_injective (this.trans L₂.prop.some_spec.some_spec.symm)
  · refine' lt_of_le_of_lt _ φ.litter_map_dom_small
    refine' ⟨⟨fun L => ⟨_, L.prop.some_spec.some⟩, fun L₁ L₂ h => _⟩⟩
    simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff] at h
    have := L₁.prop.some_spec.some_spec
    simp_rw [h] at this
    exact Subtype.coe_injective (this.trans L₂.prop.some_spec.some_spec.symm)
  · have :
      Small
        (⋃ (L : litter) (h : (φ.litter_map L).Dom),
          ((φ.litter_map L).get h : Set atom) \ litter_set ((φ.litter_map L).get h).1) :=
      by
      refine' small.bUnion _ _
      · refine' lt_of_le_of_lt _ φ.litter_map_dom_small
        refine' ⟨⟨fun N => ⟨_, N.Prop⟩, fun N₁ N₂ h => _⟩⟩
        simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff] at h
        exact subtype.coe_inj.mp h
      · intro L hL
        refine' small.mono _ ((φ.litter_map L).get hL).2.Prop
        exact fun x hx => Or.inr hx
    refine' lt_of_le_of_lt _ this
    refine' ⟨⟨fun L => ⟨L.prop.some_spec.some_spec.some, _⟩, fun L₁ L₂ h => _⟩⟩
    · simp only [mem_Union]
      exact ⟨_, _, L.prop.some_spec.some_spec.some_spec.1⟩
    simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff] at h
    have := L₁.prop.some_spec.some_spec.some_spec.2
    rw [h] at this
    exact Subtype.coe_injective (this.trans L₂.prop.some_spec.some_spec.some_spec.2.symm)

theorem mk_not_bannedLitter : (#{L | ¬φ.BannedLitter L}) = (#μ) :=
  by
  have := mk_sum_compl {L | φ.banned_litter L}
  rw [compl_set_of, mk_litter] at this
  rw [← this, add_eq_right]
  · by_contra' h
    have h' := add_le_add (le_of_lt φ.banned_litter_small) h.le
    rw [this] at h'
    refine' not_lt_of_le h' _
    refine' Cardinal.add_lt_of_lt μ_strong_limit.is_limit.aleph_0_le κ_lt_μ _
    exact lt_of_le_of_lt κ_regular.aleph_0_le κ_lt_μ
  · by_contra' h
    have h' := add_le_add (le_of_lt φ.banned_litter_small) h.le
    rw [this] at h'
    refine' not_lt_of_le h' _
    refine' Cardinal.add_lt_of_lt μ_strong_limit.is_limit.aleph_0_le κ_lt_μ _
    exact lt_trans φ.banned_litter_small κ_lt_μ

theorem not_bannedLitter_nonempty : Nonempty {L | ¬φ.BannedLitter L} := by
  simp only [← mk_ne_zero_iff, mk_not_banned_litter, Ne.def, mk_ne_zero, not_false_iff]

/-- The *sandbox litter* for a near-litter action is an arbitrarily chosen litter that
isn't banned. -/
noncomputable def sandboxLitter : Litter :=
  φ.not_bannedLitter_nonempty.some

theorem sandboxLitter_not_banned : ¬φ.BannedLitter φ.sandboxLitter :=
  φ.not_bannedLitter_nonempty.some.Prop

/-- If `a` is in the domain, this is the atom map. Otherwise, this gives an arbitrary atom. -/
noncomputable def atomMapOrElse (a : Atom) : Atom :=
  (φ.atomMap a).getD (Inhabited.default Atom)

theorem atomMapOrElse_of_dom {a : Atom} (ha : (φ.atomMap a).Dom) :
    φ.atomMapOrElse a = (φ.atomMap a).get ha := by rw [atom_map_or_else, Part.getOrElse_of_dom]

theorem mk_atomMap_image_le_mk_sandbox :
    (#(φ.atomMap.Dom ∆ (φ.atomMapOrElse '' φ.atomMap.Dom) : Set Atom)) ≤
      (#litterSet φ.sandboxLitter) :=
  by
  rw [mk_litter_set]
  refine' le_trans (mk_subtype_mono symm_diff_subset_union) (le_trans (mk_union_le _ _) _)
  refine' add_le_of_le κ_regular.aleph_0_le _ _
  exact le_of_lt φ.atom_map_dom_small
  exact le_trans mk_image_le (le_of_lt φ.atom_map_dom_small)

theorem disjoint_sandbox :
    Disjoint (φ.atomMap.Dom ∪ φ.atomMapOrElse '' φ.atomMap.Dom) (litterSet φ.sandboxLitter) :=
  by
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem]
  rintro a ⟨ha₁, ha₂⟩
  rw [mem_litter_set] at ha₂
  have hnb := φ.sandbox_litter_not_banned
  rw [← ha₂] at hnb
  cases ha₁
  · exact hnb (banned_litter.atom_dom a ha₁)
  · refine' hnb _
    simp only [mem_image, PFun.mem_dom] at ha₁
    obtain ⟨b, ⟨_, hb, rfl⟩, rfl⟩ := ha₁
    rw [φ.atom_map_or_else_of_dom hb]
    exact banned_litter.atom_map b hb

theorem atomMapOrElse_injective (hφ : φ.Lawful) : InjOn φ.atomMapOrElse φ.atomMap.Dom :=
  by
  intro a ha b hb h
  rw [φ.atom_map_or_else_of_dom ha, φ.atom_map_or_else_of_dom hb] at h
  exact hφ.atom_map_injective ha hb h

/-- If `L` is in the domain, this is the litter map.
Otherwise, this gives an arbitrary near-litter. -/
noncomputable def litterMapOrElse (L : Litter) : NearLitter :=
  (φ.litterMap L).getD (Inhabited.default NearLitter)

theorem litterMapOrElse_of_dom {L : Litter} (hL : (φ.litterMap L).Dom) :
    φ.litterMapOrElse L = (φ.litterMap L).get hL := by
  rw [litter_map_or_else, Part.getOrElse_of_dom]

noncomputable def roughLitterMapOrElse (L : Litter) : Litter :=
  (φ.litterMapOrElse L).1

theorem roughLitterMapOrElse_of_dom {L : Litter} (hL : (φ.litterMap L).Dom) :
    φ.roughLitterMapOrElse L = ((φ.litterMap L).get hL).1 := by
  rw [rough_litter_map_or_else, litter_map_or_else_of_dom]

/-- The induced action on near-litters. -/
noncomputable def nearLitterMapOrElse (N : NearLitter) : NearLitter :=
  ⟨(φ.litterMapOrElse N.fst).fst,
    φ.litterMapOrElse N.fst ∆ (φ.atomMapOrElse '' litterSet N.fst ∆ N),
    by
    rw [is_near_litter, is_near, ← symmDiff_assoc]
    exact (φ.litter_map_or_else N.fst).snd.Prop.symmDiff (small.image N.2.Prop)⟩

theorem ConNf.Small.pFun_image {α β : Type _} {s : Set α} (h : Small s) {f : α →. β} :
    Small (f.image s) := by
  have : Small (f '' s) := small.image h
  refine' small.image_subset Part.some Part.some_injective this _
  rintro x ⟨y, ⟨z, hz₁, hz₂⟩, rfl⟩
  exact ⟨z, hz₁, part.eq_some_iff.mpr hz₂⟩

theorem nearLitterMapOrElse_of_dom {N : NearLitter} (h₁ : (φ.litterMap N.fst).Dom)
    (h₂ : ∀ a ∈ litterSet N.fst ∆ N, (φ.atomMap a).Dom) :
    φ.nearLitterMapOrElse N =
      ⟨((φ.litterMap N.fst).get h₁).fst,
        (φ.litterMap N.fst).get h₁ ∆ (φ.atomMap.image <| litterSet N.fst ∆ N),
        by
        rw [is_near_litter, is_near, ← symmDiff_assoc]
        exact ((φ.litter_map N.fst).get h₁).snd.Prop.symmDiff (small.pfun_image N.2.Prop)⟩ :=
  by
  rw [← SetLike.coe_set_eq, near_litter_map_or_else, near_litter.coe_mk, Subtype.coe_mk,
    φ.litter_map_or_else_of_dom h₁]
  refine' congr_arg _ _
  ext a : 1
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [φ.atom_map_or_else_of_dom (h₂ b hb)]
    exact ⟨b, hb, Part.get_mem (h₂ b hb)⟩
  · rintro ⟨b, hb₁, hb₂, rfl⟩
    refine' ⟨b, hb₁, _⟩
    rw [φ.atom_map_or_else_of_dom]

/-!
# Preorder structure
-/


/-- We define that `f ≤ g` if the domain of `f` is included in the domain of `g`, and
they agree where they are defined. -/
structure PFun.Le {α β : Type _} (f g : α →. β) : Prop where
  dom_of_dom : ∀ a, (f a).Dom → (g a).Dom
  get_eq : ∀ a h, (f a).get h = (g a).get (dom_of_dom a h)

instance {α β : Type _} : PartialOrder (α →. β)
    where
  le := PFun.Le
  le_refl f := ⟨fun a => id, fun a h => rfl⟩
  le_trans f g h fg gh :=
    ⟨fun a ha => gh.dom_of_dom a (fg.dom_of_dom a ha), fun a ha =>
      (fg.get_eq a ha).trans (gh.get_eq a _)⟩
  le_antisymm := by
    intro f g h₁ h₂
    funext a
    refine' Part.ext' ⟨h₁.dom_of_dom a, h₂.dom_of_dom a⟩ _
    intro ha₁ ha₂
    exact h₁.get_eq a ha₁

instance : PartialOrder NearLitterAction
    where
  le π π' := π.atomMap ≤ π'.atomMap ∧ π.litterMap ≤ π'.litterMap
  le_refl π := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm := by
    intro π π' h₁ h₂
    ext : 1
    exact le_antisymm h₁.1 h₂.1
    exact le_antisymm h₁.2 h₂.2

theorem Lawful.le {φ ψ : NearLitterAction} (h : φ.Lawful) (hψ : ψ ≤ φ) : ψ.Lawful :=
  { atomMap_injective := by
      intro a b ha hb hab
      refine' h.atom_map_injective (hψ.1.dom_of_dom a ha) (hψ.1.dom_of_dom b hb) _
      rwa [hψ.1.get_eq, hψ.1.get_eq] at hab
    litterMap_injective := by
      intro L₁ L₂ h₁ h₂ h₁₂
      refine' h.litter_map_injective (hψ.2.dom_of_dom L₁ h₁) (hψ.2.dom_of_dom L₂ h₂) _
      rwa [hψ.2.get_eq, hψ.2.get_eq] at h₁₂
    atom_mem := by
      intro a ha L hL
      rw [h.atom_mem a (hψ.1.dom_of_dom a ha) L (hψ.2.dom_of_dom L hL), hψ.1.get_eq, hψ.2.get_eq] }

/-- An action is precise at a litter in its domain if all atoms in the symmetric
difference of its image are accounted for. -/
@[mk_iff]
structure PreciseAt ⦃L : Litter⦄ (hL : (φ.litterMap L).Dom) : Prop where
  diffₓ : ((φ.litterMap L).get hL : Set Atom) ∆ litterSet ((φ.litterMap L).get hL).1 ⊆ φ.atomMap.ran
  fwd : ∀ a ha, (φ.atomMap a).get ha ∈ litterSet L → (φ.atomMap ((φ.atomMap a).get ha)).Dom
  back : φ.atomMap.Dom ∩ (φ.litterMap L).get hL ⊆ φ.atomMap.ran

/-- An action is precise if it is precise at every litter in its domain. -/
def Precise : Prop :=
  ∀ ⦃L⦄ (hL : (φ.litterMap L).Dom), φ.PreciseAt hL

/-!
## Induced litter permutation
-/


theorem mk_dom_symmDiff_le :
    (#↥(φ.litterMap.Dom ∆ (φ.roughLitterMapOrElse '' φ.litterMap.Dom))) ≤
      (#{L : Litter | ¬φ.BannedLitter L}) :=
  by
  rw [mk_not_banned_litter]
  refine' le_trans (le_of_lt _) κ_le_μ
  exact small.symm_diff φ.litter_map_dom_small φ.litter_map_dom_small.image

theorem aleph0_le_not_bannedLitter : ℵ₀ ≤ (#{L | ¬φ.BannedLitter L}) :=
  by
  rw [mk_not_banned_litter]
  exact μ_strong_limit.is_limit.aleph_0_le

theorem disjoint_dom_not_bannedLitter :
    Disjoint (φ.litterMap.Dom ∪ φ.roughLitterMapOrElse '' φ.litterMap.Dom)
      {L : Litter | ¬φ.BannedLitter L} :=
  by
  simp only [Set.disjoint_left, mem_union, PFun.mem_dom, mem_image, mem_set_of_eq,
    Classical.not_not]
  rintro _ (⟨_, hL, rfl⟩ | ⟨L, ⟨_, hL, rfl⟩, rfl⟩)
  · exact banned_litter.litter_dom _ hL
  · rw [φ.rough_litter_map_or_else_of_dom hL]
    exact banned_litter.litter_map _ hL

theorem roughLitterMapOrElse_injOn (hφ : φ.Lawful) : InjOn φ.roughLitterMapOrElse φ.litterMap.Dom :=
  by
  intro L₁ hL₁ L₂ hL₂ h
  rw [φ.rough_litter_map_or_else_of_dom hL₁, φ.rough_litter_map_or_else_of_dom hL₂] at h
  exact hφ.litter_map_injective hL₁ hL₂ (near_litter.inter_nonempty_of_fst_eq_fst h)

/-- A local permutation on the set of litters that occur in the domain or range of `w`.
This permutes both flexible and inflexible litters. -/
noncomputable def litterPerm' (hφ : φ.Lawful) : LocalPerm Litter :=
  LocalPerm.complete φ.roughLitterMapOrElse φ.litterMap.Dom {L | ¬φ.BannedLitter L}
    φ.mk_dom_symmDiff_le φ.aleph0_le_not_bannedLitter φ.disjoint_dom_not_bannedLitter
    (φ.roughLitterMapOrElse_injOn hφ)

def idOnBanned (s : Set Litter) : LocalPerm Litter
    where
  toFun := id
  invFun := id
  domain := {L | φ.BannedLitter L} \ s
  toFun_domain' L h := h
  invFun_domain' L h := h
  left_inv' L h := rfl
  right_inv' L h := rfl

noncomputable def litterPerm (hφ : φ.Lawful) : LocalPerm Litter :=
  LocalPerm.piecewise (φ.litterPerm' hφ) (φ.idOnBanned (φ.litterPerm' hφ).domain)
    (by rw [← Set.subset_compl_iff_disjoint_left] <;> exact fun L h => h.2)

theorem litterPerm'_apply_eq {φ : NearLitterAction} {hφ : φ.Lawful} (L : Litter)
    (hL : L ∈ φ.litterMap.Dom) : φ.litterPerm' hφ L = φ.roughLitterMapOrElse L :=
  LocalPerm.complete_apply_eq _ _ _ hL

theorem litterPerm_apply_eq {φ : NearLitterAction} {hφ : φ.Lawful} (L : Litter)
    (hL : L ∈ φ.litterMap.Dom) : φ.litterPerm hφ L = φ.roughLitterMapOrElse L :=
  by
  rw [← litter_perm'_apply_eq L hL]
  exact LocalPerm.piecewise_apply_eq_left (Or.inl (Or.inl hL))

theorem litterPerm'_domain_small (hφ : φ.Lawful) : Small (φ.litterPerm' hφ).domain :=
  by
  refine' small.union (small.union φ.litter_map_dom_small φ.litter_map_dom_small.image) _
  rw [Small]
  rw [Cardinal.mk_congr (LocalPerm.sandboxSubsetEquiv _ _)]
  simp only [mk_sum, mk_prod, mk_denumerable, lift_aleph_0, lift_uzero, lift_id]
  refine' add_lt_of_lt κ_regular.aleph_0_le _ _ <;>
      refine' mul_lt_of_lt κ_regular.aleph_0_le (lt_of_le_of_lt Λ_limit.aleph_0_le Λ_lt_κ) _ <;>
    refine' lt_of_le_of_lt (mk_subtype_mono (diff_subset _ _)) _
  exact φ.litter_map_dom_small
  exact φ.litter_map_dom_small.image

theorem litterPerm_domain_small (hφ : φ.Lawful) : Small (φ.litterPerm hφ).domain :=
  Small.union (φ.litterPerm'_domain_small hφ) (Small.mono (diff_subset _ _) φ.bannedLitter_small)

variable {α : Λ} [PositionData] [Phase2Assumptions α] {β : Iio α} {A : ExtendedIndex β}

theorem mk_not_bannedLitter_and_flexible : (#{L | ¬φ.BannedLitter L ∧ Flexible α L A}) = (#μ) :=
  by
  refine' le_antisymm ((mk_subtype_le _).trans mk_litter.le) _
  by_contra
  rw [not_le] at h
  have h₁ := Cardinal.le_mk_diff_add_mk {L | flexible α L A} {L | φ.banned_litter L}
  rw [mk_flexible, diff_eq, inter_comm] at h₁
  have h₂ :=
    add_lt_of_lt μ_strong_limit.is_limit.aleph_0_le h (lt_trans φ.banned_litter_small κ_lt_μ)
  exact h₁.not_lt h₂

theorem mk_dom_inter_flexible_symmDiff_le :
    (#↥((φ.litterMap.Dom ∩ {L | Flexible α L A}) ∆
            (φ.roughLitterMapOrElse '' (φ.litterMap.Dom ∩ {L | Flexible α L A})))) ≤
      (#{L : Litter | ¬φ.BannedLitter L ∧ Flexible α L A}) :=
  by
  rw [mk_not_banned_litter_and_flexible]
  refine' le_trans (le_of_lt _) κ_le_μ
  exact
    small.symm_diff (small.mono (inter_subset_left _ _) φ.litter_map_dom_small)
      (small.mono (inter_subset_left _ _) φ.litter_map_dom_small).image

theorem aleph0_le_not_bannedLitter_and_flexible :
    ℵ₀ ≤ (#{L | ¬φ.BannedLitter L ∧ Flexible α L A}) :=
  by
  rw [mk_not_banned_litter_and_flexible]
  exact μ_strong_limit.is_limit.aleph_0_le

theorem disjoint_dom_inter_flexible_not_bannedLitter :
    Disjoint
      (φ.litterMap.Dom ∩ {L | Flexible α L A} ∪
        φ.roughLitterMapOrElse '' (φ.litterMap.Dom ∩ {L | Flexible α L A}))
      {L : Litter | ¬φ.BannedLitter L ∧ Flexible α L A} :=
  by
  refine' disjoint_of_subset _ (inter_subset_left _ _) φ.disjoint_dom_not_banned_litter
  rintro a (ha | ⟨b, hb, rfl⟩)
  exact Or.inl ha.1
  exact Or.inr ⟨b, hb.1, rfl⟩

theorem roughLitterMapOrElse_injOn_dom_inter_flexible (hφ : φ.Lawful) :
    InjOn φ.roughLitterMapOrElse (φ.litterMap.Dom ∩ {L | Flexible α L A}) :=
  (φ.roughLitterMapOrElse_injOn hφ).mono (inter_subset_left _ _)

noncomputable def flexibleLitterPerm (hφ : φ.Lawful) (A : ExtendedIndex β) : LocalPerm Litter :=
  LocalPerm.complete φ.roughLitterMapOrElse (φ.litterMap.Dom ∩ {L | Flexible α L A})
    {L | ¬φ.BannedLitter L ∧ Flexible α L A} φ.mk_dom_inter_flexible_symmDiff_le
    φ.aleph0_le_not_bannedLitter_and_flexible φ.disjoint_dom_inter_flexible_not_bannedLitter
    (φ.roughLitterMapOrElse_injOn_dom_inter_flexible hφ)

theorem flexibleLitterPerm_apply_eq {φ : NearLitterAction} {hφ : φ.Lawful} (L : Litter)
    (hL₁ : L ∈ φ.litterMap.Dom) (hL₂ : Flexible α L A) :
    φ.flexibleLitterPerm hφ A L = φ.roughLitterMapOrElse L :=
  LocalPerm.complete_apply_eq _ _ _ ⟨hL₁, hL₂⟩

theorem flexibleLitterPerm_domain_small (hφ : φ.Lawful) :
    Small (φ.flexibleLitterPerm hφ A).domain :=
  by
  refine' small.union (small.union _ _) _
  · exact φ.litter_map_dom_small.mono (inter_subset_left _ _)
  · exact (φ.litter_map_dom_small.mono (inter_subset_left _ _)).image
  · rw [Small]
    rw [Cardinal.mk_congr (LocalPerm.sandboxSubsetEquiv _ _)]
    simp only [mk_sum, mk_prod, mk_denumerable, lift_aleph_0, lift_uzero, lift_id]
    refine' add_lt_of_lt κ_regular.aleph_0_le _ _ <;>
        refine' mul_lt_of_lt κ_regular.aleph_0_le (lt_of_le_of_lt Λ_limit.aleph_0_le Λ_lt_κ) _ <;>
      refine' lt_of_le_of_lt (mk_subtype_mono (diff_subset _ _)) _
    exact φ.litter_map_dom_small.mono (inter_subset_left _ _)
    exact (φ.litter_map_dom_small.mono (inter_subset_left _ _)).image

/-!
# Completed permutations
-/


/-- A local permutation induced by completing the orbits of atoms in a near-litter action.
This function creates forward and backward images of atoms in the *sandbox litter*,
a litter which is away from the domain and range of the approximation in question, so it should
not interfere with other constructions. -/
noncomputable def completeAtomPerm (hφ : φ.Lawful) : LocalPerm Atom :=
  LocalPerm.complete φ.atomMapOrElse φ.atomMap.Dom (litterSet φ.sandboxLitter)
    φ.mk_atomMap_image_le_mk_sandbox (by simpa only [mk_litter_set] using κ_regular.aleph_0_le)
    φ.disjoint_sandbox (φ.atomMapOrElse_injective hφ)

theorem sandboxSubset_small :
    Small
      (LocalPerm.sandboxSubset φ.mk_atomMap_image_le_mk_sandbox
        (by simpa only [mk_litter_set] using κ_regular.aleph_0_le)) :=
  by
  rw [Small]
  rw [Cardinal.mk_congr (LocalPerm.sandboxSubsetEquiv _ _)]
  simp only [mk_sum, mk_prod, mk_denumerable, lift_aleph_0, lift_uzero, lift_id]
  refine' add_lt_of_lt κ_regular.aleph_0_le _ _ <;>
      refine' mul_lt_of_lt κ_regular.aleph_0_le (lt_of_le_of_lt Λ_limit.aleph_0_le Λ_lt_κ) _ <;>
    refine' lt_of_le_of_lt (mk_subtype_mono (diff_subset _ _)) _
  · exact φ.atom_map_dom_small
  · exact lt_of_le_of_lt mk_image_le φ.atom_map_dom_small

theorem completeAtomPerm_domain_small (hφ : φ.Lawful) : Small (φ.completeAtomPerm hφ).domain :=
  Small.union (Small.union φ.atomMap_dom_small (lt_of_le_of_lt mk_image_le φ.atomMap_dom_small))
    φ.sandboxSubset_small

/-- A near-litter approximation built from this near-litter action.
Its action on atoms matches that of the action, and its rough action on litters
matches the given litter permutation. -/
noncomputable def complete (hφ : φ.Lawful) (A : ExtendedIndex β) : NearLitterApprox
    where
  atomPerm := φ.completeAtomPerm hφ
  litterPerm := φ.flexibleLitterPerm hφ A
  domain_small L := Small.mono (inter_subset_right _ _) (φ.completeAtomPerm_domain_small hφ)

variable {litter_perm : LocalPerm Litter}

theorem completeAtomPerm_apply_eq (hφ : φ.Lawful) {a : Atom} (ha : (φ.atomMap a).Dom) :
    φ.completeAtomPerm hφ a = (φ.atomMap a).get ha := by
  rwa [complete_atom_perm, LocalPerm.complete_apply_eq, atom_map_or_else_of_dom]

theorem complete_smul_atom_eq {hφ : φ.Lawful} {a : Atom} (ha : (φ.atomMap a).Dom) :
    φ.complete hφ A • a = (φ.atomMap a).get ha :=
  φ.completeAtomPerm_apply_eq hφ ha

@[simp]
theorem complete_smul_litter_eq {hφ : φ.Lawful} (L : Litter) :
    φ.complete hφ A • L = φ.flexibleLitterPerm hφ A L :=
  rfl

theorem smul_atom_eq {hφ : φ.Lawful} {π : NearLitterPerm}
    (hπ : (φ.complete hφ A).ExactlyApproximates π) {a : Atom} (ha : (φ.atomMap a).Dom) :
    π • a = (φ.atomMap a).get ha := by
  rw [← hπ.map_atom a (Or.inl (Or.inl ha)), φ.complete_smul_atom_eq ha]

theorem smul_toNearLitter_eq_of_preciseAt {hφ : φ.Lawful} {π : NearLitterPerm}
    (hπ : (φ.complete hφ A).ExactlyApproximates π) {L : Litter} (hL : (φ.litterMap L).Dom)
    (hφL : φ.PreciseAt hL) (hπL : π • L = ((φ.litterMap L).get hL).1) :
    π • L.toNearLitter = (φ.litterMap L).get hL :=
  by
  refine' SetLike.coe_injective _
  ext a : 1
  simp only [mem_smul_set_iff_inv_smul_mem, near_litter_perm.coe_smul, litter.coe_to_near_litter,
    mem_litter_set, SetLike.mem_coe]
  constructor
  · intro ha
    by_cases π.is_exception a
    · suffices h' : π⁻¹ • a ∈ φ.atom_map.dom
      · rw [hφ.atom_mem _ h' L hL] at ha
        have := hπ.map_atom _ (Or.inl (Or.inl h'))
        rw [φ.complete_smul_atom_eq h'] at this
        rw [this, smul_inv_smul] at ha
        exact ha
      rw [← hπ.symm_map_atom a (hπ.exception_mem _ h)] at ha ⊢
      obtain (hdom | hdom) | hdom :=
        (φ.complete hφ A).atomPerm.symm.map_domain (hπ.exception_mem _ h)
      · exact hdom
      · obtain ⟨c, hc₁, hc₂⟩ := hdom
        rw [φ.atom_map_or_else_of_dom hc₁] at hc₂
        have := hφL.fwd c hc₁ (by rwa [hc₂])
        rw [hc₂] at this
        exact this
      · cases φ.sandbox_litter_not_banned _
        rw [← eq_of_mem_litter_set_of_mem_litter_set ha (LocalPerm.sandboxSubset_subset _ _ hdom)]
        exact banned_litter.litter_dom L hL
    · by_contra h'
      simp only [near_litter_perm.is_exception, mem_litter_set, not_or, Classical.not_not, ha] at h
      obtain ⟨b, hb, rfl⟩ :=
        hφL.diff (Or.inr ⟨by rw [← hπL, h.2, smul_inv_smul, mem_litter_set], h'⟩)
      refine' h' ((hφ.atom_mem b hb L hL).mp _)
      have := hπ.map_atom b (Or.inl (Or.inl hb))
      rw [φ.complete_smul_atom_eq hb] at this
      rw [this, inv_smul_smul] at ha
      exact ha
  · intro ha
    -- TODO: probably possible to clean up `by_cases` into a `suffices`
    by_cases π⁻¹ • a ∈ φ.atom_map.dom
    · rw [hφ.atom_mem _ h L hL]
      have := hπ.map_atom _ (Or.inl (Or.inl h))
      rw [φ.complete_smul_atom_eq h] at this
      rw [this, smul_inv_smul]
      exact ha
    have haL : a ∈ litter_set ((φ.litter_map L).get hL).fst :=
      by
      by_contra h'
      obtain ⟨b, hb, rfl⟩ := hφL.diff (Or.inl ⟨ha, h'⟩)
      have := hπ.map_atom b (Or.inl (Or.inl hb))
      rw [φ.complete_smul_atom_eq hb] at this
      rw [this, inv_smul_smul] at h
      exact h hb
    by_contra h'
    have hex : π.is_exception a :=
      by
      refine' Or.inr fun h'' => h' (h''.trans _)
      rw [inv_smul_eq_iff, hπL]
      exact haL
    obtain (hdom | ⟨b, hb₁, hb₂⟩) | hdom := hπ.exception_mem a hex
    · obtain ⟨b, hb₁, hb₂⟩ := hφL.back ⟨hdom, ha⟩
      have := hπ.map_atom b (Or.inl (Or.inl hb₁))
      rw [φ.complete_smul_atom_eq hb₁] at this
      rw [this, smul_eq_iff_eq_inv_smul] at hb₂
      rw [hb₂] at hb₁
      exact h hb₁
    · rw [φ.atom_map_or_else_of_dom hb₁] at hb₂
      have := hπ.map_atom b (Or.inl (Or.inl hb₁))
      rw [φ.complete_smul_atom_eq hb₁, hb₂, ← inv_smul_eq_iff] at this
      rw [this] at h
      exact h hb₁
    · refine' φ.sandbox_litter_not_banned _
      rw [eq_of_mem_litter_set_of_mem_litter_set (LocalPerm.sandboxSubset_subset _ _ hdom) haL]
      exact banned_litter.litter_map L hL

theorem smul_nearLitter_eq_of_preciseAt {hφ : φ.Lawful} {π : NearLitterPerm}
    (hπ : (φ.complete hφ A).ExactlyApproximates π) {N : NearLitter} (hN : (φ.litterMap N.1).Dom)
    (hw : φ.PreciseAt hN) (hπL : π • N.1 = ((φ.litterMap N.1).get hN).1) :
    ((π • N : NearLitter) : Set Atom) = (φ.litterMap N.1).get hN ∆ (π • litterSet N.1 ∆ N) :=
  by
  refine' (near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul _ _).trans _
  rw [← φ.smul_to_near_litter_eq_of_precise_at hπ hN hw hπL]
  rfl

end NearLitterAction

end ConNf
