import ConNF.Foa.Basic.Approximation
import ConNF.Foa.Basic.CompleteOrbit
import ConNF.Foa.Basic.Reduction

open Cardinal Quiver Set Sum WithBot

open scoped Cardinal Classical Pointwise

universe u

namespace ConNF

variable [Params.{u}]

/-!
# Structural actions
-/

/-- Noncomputably eliminates a disjunction into a (possibly predicative) universe. -/
noncomputable def _root_.Or.elim' {α : Sort _} {p q : Prop}
    (h : p ∨ q) (f : p → α) (g : q → α) : α :=
  if hp : p then f hp else g (h.resolve_left hp)

lemma _root_.Or.elim'_left {α : Sort _} {p q : Prop}
    (h : p ∨ q) (f : p → α) (g : q → α) (hp : p) : h.elim' f g = f hp :=
  by rw [Or.elim', dif_pos hp]

lemma _root_.Or.elim'_right {α : Sort _} {p q : Prop}
    (h : p ∨ q) (f : p → α) (g : q → α) (hp : ¬p) : h.elim' f g = g (h.resolve_left hp) :=
  by rw [Or.elim', dif_neg hp]

/-- A *near-litter action* is a partial function from atoms to atoms and a partial
function from litters to near-litters, both of which have small domain.
The image of a litter under the `litter_map` should be interpreted as the intended *precise* image
of this litter under an allowable permutation. -/
@[ext]
structure NearLitterAction where
  atomMap : Atom →. Atom
  litterMap : Litter →. NearLitter
  atomMap_dom_small : Small atomMap.Dom
  litterMap_dom_small : Small litterMap.Dom

/-- A near litter action in which the atom and litter maps are injective (in suitable senses) and
cohere in the sense that images of atoms in litters are mapped to atoms inside the corresponding
near-litters. -/
structure NearLitterAction.Lawful (φ : NearLitterAction) : Prop where
  atomMap_injective : ∀ ⦃a b⦄ (ha hb),
    (φ.atomMap a).get ha = (φ.atomMap b).get hb → a = b
  litterMap_injective : ∀ ⦃L₁ L₂ : Litter⦄ (hL₁ hL₂),
    (((φ.litterMap L₁).get hL₁ : Set Atom) ∩ (φ.litterMap L₂).get hL₂).Nonempty → L₁ = L₂
  atom_mem : ∀ (a : Atom) (ha L hL), a.1 = L ↔ (φ.atomMap a).get ha ∈ (φ.litterMap L).get hL

namespace NearLitterAction

variable (φ : NearLitterAction)

/-- A litter that is not allowed to be used as a sandbox because it appears somewhere that
we need to preserve. -/
@[mk_iff]
inductive BannedLitter : Litter → Prop
  | atomDom (a : Atom) : (φ.atomMap a).Dom → BannedLitter a.1
  | litterDom (L : Litter) : (φ.litterMap L).Dom → BannedLitter L
  | atomMap (a : Atom) (h) : BannedLitter ((φ.atomMap a).get h).1
  | litterMap (L : Litter) (h) : BannedLitter ((φ.litterMap L).get h).1
  | diff (L : Litter) (h) (a : Atom) :
    a ∈ ((φ.litterMap L).get h : Set Atom) \ litterSet ((φ.litterMap L).get h).1 → BannedLitter a.1

theorem BannedLitter.memMap (a : Atom) (L : Litter) (hL)
    (ha : a ∈ ((φ.litterMap L).get hL : Set Atom)) : φ.BannedLitter a.1 := by
  by_cases a.1 = ((φ.litterMap L).get hL).1
  · rw [h]
    exact BannedLitter.litterMap L hL
  · exact BannedLitter.diff L hL a ⟨ha, h⟩

/-- There are only a small amount of banned litters. -/
theorem bannedLitter_small : Small {L | φ.BannedLitter L} := by
  simp only [BannedLitter_iff, mem_diff, SetLike.mem_coe, mem_litterSet]
  refine' Small.union _ (Small.union _ (Small.union _ (Small.union _ _)))
  · refine' lt_of_le_of_lt _ φ.atomMap_dom_small
    refine' ⟨⟨fun a => ⟨_, a.prop.choose_spec.1⟩, fun a₁ a₂ h => _⟩⟩
    simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff] at h
    have := a₁.prop.choose_spec.2
    rw [h] at this
    exact Subtype.coe_injective (this.trans a₂.prop.choose_spec.2.symm)
  · refine' lt_of_le_of_lt _ φ.litterMap_dom_small
    refine' ⟨⟨fun L => ⟨_, L.prop⟩, fun L₁ L₂ h => _⟩⟩
    simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff] at h
    exact Subtype.coe_injective h
  · refine' lt_of_le_of_lt _ φ.atomMap_dom_small
    refine' ⟨⟨fun L => ⟨_, L.prop.choose_spec.choose⟩, fun L₁ L₂ h => _⟩⟩
    simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff] at h
    have := L₁.prop.choose_spec.choose_spec
    simp_rw [h] at this
    exact Subtype.coe_injective (this.trans L₂.prop.choose_spec.choose_spec.symm)
  · refine' lt_of_le_of_lt _ φ.litterMap_dom_small
    refine' ⟨⟨fun L => ⟨_, L.prop.choose_spec.choose⟩, fun L₁ L₂ h => _⟩⟩
    simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff] at h
    have := L₁.prop.choose_spec.choose_spec
    simp_rw [h] at this
    exact Subtype.coe_injective (this.trans L₂.prop.choose_spec.choose_spec.symm)
  · have : Small
      (⋃ (L : Litter) (h : (φ.litterMap L).Dom),
        ((φ.litterMap L).get h : Set Atom) \ litterSet ((φ.litterMap L).get h).1)
    · refine' Small.bUnion _ _
      · refine' lt_of_le_of_lt _ φ.litterMap_dom_small
        refine' ⟨⟨fun N => ⟨_, N.prop⟩, fun N₁ N₂ h => _⟩⟩
        simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff] at h
        exact Subtype.coe_inj.mp h
      · intro L hL
        refine' Small.mono _ ((φ.litterMap L).get hL).2.prop
        exact fun x hx => Or.inr hx
    refine' lt_of_le_of_lt _ this
    refine' ⟨⟨fun L => ⟨L.prop.choose_spec.choose_spec.choose, _⟩, fun L₁ L₂ h => _⟩⟩
    · simp only [mem_iUnion]
      exact ⟨_, _, L.prop.choose_spec.choose_spec.choose_spec.1⟩
    simp only [Subtype.mk_eq_mk, Prod.mk.inj_iff] at h
    have := L₁.prop.choose_spec.choose_spec.choose_spec.2
    rw [h] at this
    exact Subtype.coe_injective (this.trans L₂.prop.choose_spec.choose_spec.choose_spec.2.symm)

theorem mk_not_bannedLitter : #{L | ¬φ.BannedLitter L} = #μ := by
  have := mk_sum_compl {L | φ.BannedLitter L}
  rw [compl_setOf, mk_litter] at this
  rw [← this, add_eq_right]
  · by_contra' h
    have h' := add_le_add (le_of_lt φ.bannedLitter_small) h.le
    rw [this] at h'
    refine' not_lt_of_le h' _
    refine' Cardinal.add_lt_of_lt μ_isStrongLimit.isLimit.aleph0_le κ_lt_μ _
    exact lt_of_le_of_lt κ_isRegular.aleph0_le κ_lt_μ
  · by_contra' h
    have h' := add_le_add (le_of_lt φ.bannedLitter_small) h.le
    rw [this] at h'
    refine' not_lt_of_le h' _
    refine' Cardinal.add_lt_of_lt μ_isStrongLimit.isLimit.aleph0_le κ_lt_μ _
    exact lt_trans φ.bannedLitter_small κ_lt_μ

theorem not_bannedLitter_nonempty : Nonempty {L | ¬φ.BannedLitter L} := by
  simp only [← mk_ne_zero_iff, mk_not_bannedLitter, Ne.def, mk_ne_zero, not_false_iff]

/-- The *sandbox litter* for a near-litter action is an arbitrarily chosen litter that
isn't banned. -/
noncomputable def sandboxLitter : Litter :=
  φ.not_bannedLitter_nonempty.some

theorem sandboxLitter_not_banned : ¬φ.BannedLitter φ.sandboxLitter :=
  φ.not_bannedLitter_nonempty.some.prop

/-- If `a` is in the domain, this is the atom map. Otherwise, this gives an arbitrary atom. -/
noncomputable def atomMapOrElse (a : Atom) : Atom :=
  (φ.atomMap a).getOrElse default

theorem atomMapOrElse_of_dom {a : Atom} (ha : (φ.atomMap a).Dom) :
    φ.atomMapOrElse a = (φ.atomMap a).get ha := by rw [atomMapOrElse, Part.getOrElse_of_dom]

theorem mk_atomMap_image_le_mk_sandbox :
    #(φ.atomMap.Dom ∆ (φ.atomMapOrElse '' φ.atomMap.Dom) : Set Atom) ≤
      #(litterSet φ.sandboxLitter) := by
  rw [mk_litterSet]
  refine' le_trans (mk_subtype_mono symmDiff_subset_union) (le_trans (mk_union_le _ _) _)
  refine' add_le_of_le κ_isRegular.aleph0_le _ _
  exact le_of_lt φ.atomMap_dom_small
  exact le_trans mk_image_le (le_of_lt φ.atomMap_dom_small)

theorem disjoint_sandbox :
    Disjoint (φ.atomMap.Dom ∪ φ.atomMapOrElse '' φ.atomMap.Dom) (litterSet φ.sandboxLitter) := by
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem]
  rintro a ⟨ha₁, ha₂⟩
  rw [mem_litterSet] at ha₂
  have hnb := φ.sandboxLitter_not_banned
  rw [← ha₂] at hnb
  obtain (ha₁ | ha₁) := ha₁
  · exact hnb (BannedLitter.atomDom a ha₁)
  · refine' hnb _
    simp only [mem_image, PFun.mem_dom] at ha₁
    obtain ⟨b, ⟨_, hb, rfl⟩, rfl⟩ := ha₁
    rw [φ.atomMapOrElse_of_dom hb]
    exact BannedLitter.atomMap b hb

theorem atomMapOrElse_injective (hφ : φ.Lawful) : InjOn φ.atomMapOrElse φ.atomMap.Dom := by
  intro a ha b hb h
  rw [φ.atomMapOrElse_of_dom ha, φ.atomMapOrElse_of_dom hb] at h
  exact hφ.atomMap_injective ha hb h

/-- If `L` is in the domain, this is the litter map.
Otherwise, this gives an arbitrary near-litter. -/
noncomputable def litterMapOrElse (L : Litter) : NearLitter :=
  (φ.litterMap L).getOrElse default

theorem litterMapOrElse_of_dom {L : Litter} (hL : (φ.litterMap L).Dom) :
    φ.litterMapOrElse L = (φ.litterMap L).get hL := by
  rw [litterMapOrElse, Part.getOrElse_of_dom]

noncomputable def roughLitterMapOrElse (L : Litter) : Litter :=
  (φ.litterMapOrElse L).1

theorem roughLitterMapOrElse_of_dom {L : Litter} (hL : (φ.litterMap L).Dom) :
    φ.roughLitterMapOrElse L = ((φ.litterMap L).get hL).1 := by
  rw [roughLitterMapOrElse, litterMapOrElse_of_dom]

/-- The induced action on near-litters. -/
noncomputable def nearLitterMapOrElse (N : NearLitter) : NearLitter :=
  ⟨(φ.litterMapOrElse N.fst).fst,
    φ.litterMapOrElse N.fst ∆ (φ.atomMapOrElse '' litterSet N.fst ∆ N), by
    rw [IsNearLitter, IsNear, ← symmDiff_assoc]
    exact (φ.litterMapOrElse N.fst).snd.prop.symmDiff (Small.image N.2.prop)⟩

theorem nearLitterMapOrElse_of_dom {N : NearLitter} (h₁ : (φ.litterMap N.fst).Dom)
    (h₂ : ∀ a ∈ litterSet N.fst ∆ N, (φ.atomMap a).Dom) :
    φ.nearLitterMapOrElse N =
      ⟨((φ.litterMap N.fst).get h₁).fst,
        (φ.litterMap N.fst).get h₁ ∆ (φ.atomMap.image <| litterSet N.fst ∆ N), by
        rw [IsNearLitter, IsNear, ← symmDiff_assoc]
        exact ((φ.litterMap N.fst).get h₁).snd.prop.symmDiff (Small.pFun_image N.2.prop)⟩ := by
  rw [← SetLike.coe_set_eq, nearLitterMapOrElse, NearLitter.coe_mk, Subtype.coe_mk,
    φ.litterMapOrElse_of_dom h₁]
  refine' congr_arg _ _
  ext a : 1
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [φ.atomMapOrElse_of_dom (h₂ b hb)]
    exact ⟨b, hb, Part.get_mem (h₂ b hb)⟩
  · rintro ⟨b, hb₁, hb₂, rfl⟩
    refine' ⟨b, hb₁, _⟩
    rw [φ.atomMapOrElse_of_dom]

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
    intro ha _
    exact h₁.get_eq a ha

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
      refine' h.atomMap_injective (hψ.1.dom_of_dom a ha) (hψ.1.dom_of_dom b hb) _
      rwa [hψ.1.get_eq, hψ.1.get_eq] at hab
    litterMap_injective := by
      intro L₁ L₂ h₁ h₂ h₁₂
      refine' h.litterMap_injective (hψ.2.dom_of_dom L₁ h₁) (hψ.2.dom_of_dom L₂ h₂) _
      rwa [hψ.2.get_eq, hψ.2.get_eq] at h₁₂
    atom_mem := by
      intro a ha L hL
      rw [h.atom_mem a (hψ.1.dom_of_dom a ha) L (hψ.2.dom_of_dom L hL), hψ.1.get_eq, hψ.2.get_eq] }

/-- An action is precise at a litter in its domain if all atoms in the symmetric
difference of its image are accounted for. -/
@[mk_iff]
structure PreciseAt ⦃L : Litter⦄ (hL : (φ.litterMap L).Dom) : Prop where
  diff : ((φ.litterMap L).get hL : Set Atom) ∆ litterSet ((φ.litterMap L).get hL).1 ⊆ φ.atomMap.ran
  fwd : ∀ a ha, (φ.atomMap a).get ha ∈ litterSet L → (φ.atomMap ((φ.atomMap a).get ha)).Dom
  back : φ.atomMap.Dom ∩ (φ.litterMap L).get hL ⊆ φ.atomMap.ran

/-- An action is precise if it is precise at every litter in its domain. -/
def Precise : Prop :=
  ∀ ⦃L⦄ (hL : (φ.litterMap L).Dom), φ.PreciseAt hL

/-!
## Induced litter permutation
-/

theorem mk_dom_symmDiff_le :
    #(φ.litterMap.Dom ∆ (φ.roughLitterMapOrElse '' φ.litterMap.Dom) : Set Litter) ≤
      #{L : Litter | ¬φ.BannedLitter L} := by
  rw [mk_not_bannedLitter]
  refine' le_trans (le_of_lt _) κ_le_μ
  exact Small.symmDiff φ.litterMap_dom_small φ.litterMap_dom_small.image

theorem aleph0_le_not_bannedLitter : ℵ₀ ≤ #{L | ¬φ.BannedLitter L} := by
  rw [mk_not_bannedLitter]
  exact μ_isStrongLimit.isLimit.aleph0_le

theorem disjoint_dom_not_bannedLitter :
    Disjoint (φ.litterMap.Dom ∪ φ.roughLitterMapOrElse '' φ.litterMap.Dom)
      {L : Litter | ¬φ.BannedLitter L} := by
  simp only [Set.disjoint_left, mem_union, PFun.mem_dom, mem_image, mem_setOf_eq,
    Classical.not_not]
  rintro _ (⟨_, hL, rfl⟩ | ⟨L, ⟨_, hL, rfl⟩, rfl⟩)
  · exact BannedLitter.litterDom _ hL
  · rw [φ.roughLitterMapOrElse_of_dom hL]
    exact BannedLitter.litterMap _ hL

theorem roughLitterMapOrElse_injOn (hφ : φ.Lawful) :
    InjOn φ.roughLitterMapOrElse φ.litterMap.Dom := by
  intro L₁ hL₁ L₂ hL₂ h
  rw [φ.roughLitterMapOrElse_of_dom hL₁, φ.roughLitterMapOrElse_of_dom hL₂] at h
  exact hφ.litterMap_injective hL₁ hL₂ (NearLitter.inter_nonempty_of_fst_eq_fst h)

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
  toFun_domain' _ h := h
  invFun_domain' _ h := h
  left_inv' _ _ := rfl
  right_inv' _ _ := rfl

noncomputable def litterPerm (hφ : φ.Lawful) : LocalPerm Litter :=
  LocalPerm.piecewise (φ.litterPerm' hφ) (φ.idOnBanned (φ.litterPerm' hφ).domain)
    (by rw [← Set.subset_compl_iff_disjoint_left]; exact fun L h => h.2)

theorem litterPerm'_apply_eq {φ : NearLitterAction} {hφ : φ.Lawful} (L : Litter)
    (hL : L ∈ φ.litterMap.Dom) : φ.litterPerm' hφ L = φ.roughLitterMapOrElse L :=
  LocalPerm.complete_apply_eq _ _ _ hL

theorem litterPerm_apply_eq {φ : NearLitterAction} {hφ : φ.Lawful} (L : Litter)
    (hL : L ∈ φ.litterMap.Dom) : φ.litterPerm hφ L = φ.roughLitterMapOrElse L := by
  rw [← litterPerm'_apply_eq L hL]
  exact LocalPerm.piecewise_apply_eq_left (Or.inl (Or.inl hL))

theorem litterPerm'_domain_small (hφ : φ.Lawful) : Small (φ.litterPerm' hφ).domain := by
  refine' Small.union (Small.union φ.litterMap_dom_small φ.litterMap_dom_small.image) _
  rw [Small]
  rw [Cardinal.mk_congr (LocalPerm.sandboxSubsetEquiv _ _)]
  simp only [mk_sum, mk_prod, mk_denumerable, lift_aleph0, lift_uzero, lift_id]
  refine' add_lt_of_lt κ_isRegular.aleph0_le _ _ <;>
      refine' mul_lt_of_lt κ_isRegular.aleph0_le (lt_of_le_of_lt aleph0_le_mk_Λ Λ_lt_κ) _ <;>
    refine' lt_of_le_of_lt (mk_subtype_mono (diff_subset _ _)) _
  exact φ.litterMap_dom_small
  exact φ.litterMap_dom_small.image

theorem litterPerm_domain_small (hφ : φ.Lawful) : Small (φ.litterPerm hφ).domain :=
  Small.union (φ.litterPerm'_domain_small hφ) (Small.mono (diff_subset _ _) φ.bannedLitter_small)

variable {α : Λ} [BasePositions] [Phase2Assumptions α] {β : Iio α} {A : ExtendedIndex β}

theorem mk_not_bannedLitter_and_flexible : #{L | ¬φ.BannedLitter L ∧ Flexible α L A} = #μ := by
  refine' le_antisymm ((mk_subtype_le _).trans mk_litter.le) _
  by_contra h
  rw [not_le] at h
  have h₁ := Cardinal.le_mk_diff_add_mk {L | Flexible α L A} {L | φ.BannedLitter L}
  rw [mk_flexible, diff_eq, inter_comm] at h₁
  have h₂ :=
    add_lt_of_lt μ_isStrongLimit.isLimit.aleph0_le h (lt_trans φ.bannedLitter_small κ_lt_μ)
  exact h₁.not_lt h₂

theorem mk_dom_inter_flexible_symmDiff_le :
    #((φ.litterMap.Dom ∩ {L | Flexible α L A}) ∆
        (φ.roughLitterMapOrElse '' (φ.litterMap.Dom ∩ {L | Flexible α L A})) : Set Litter) ≤
      #{L : Litter | ¬φ.BannedLitter L ∧ Flexible α L A} := by
  rw [mk_not_bannedLitter_and_flexible]
  refine' le_trans (le_of_lt _) κ_le_μ
  exact Small.symmDiff (Small.mono (inter_subset_left _ _) φ.litterMap_dom_small)
    (Small.mono (inter_subset_left _ _) φ.litterMap_dom_small).image

theorem aleph0_le_not_bannedLitter_and_flexible :
    ℵ₀ ≤ #{L | ¬φ.BannedLitter L ∧ Flexible α L A} := by
  rw [mk_not_bannedLitter_and_flexible]
  exact μ_isStrongLimit.isLimit.aleph0_le

theorem disjoint_dom_inter_flexible_not_bannedLitter :
    Disjoint
      (φ.litterMap.Dom ∩ {L | Flexible α L A} ∪
        φ.roughLitterMapOrElse '' (φ.litterMap.Dom ∩ {L | Flexible α L A}))
      {L : Litter | ¬φ.BannedLitter L ∧ Flexible α L A} := by
  refine' disjoint_of_subset _ (inter_subset_left _ _) φ.disjoint_dom_not_bannedLitter
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
    Small (φ.flexibleLitterPerm hφ A).domain := by
  refine' Small.union (Small.union _ _) _
  · exact φ.litterMap_dom_small.mono (inter_subset_left _ _)
  · exact (φ.litterMap_dom_small.mono (inter_subset_left _ _)).image
  · rw [Small]
    rw [Cardinal.mk_congr (LocalPerm.sandboxSubsetEquiv _ _)]
    simp only [mk_sum, mk_prod, mk_denumerable, lift_aleph0, lift_uzero, lift_id]
    refine' add_lt_of_lt κ_isRegular.aleph0_le _ _ <;>
        refine' mul_lt_of_lt κ_isRegular.aleph0_le (lt_of_le_of_lt aleph0_le_mk_Λ Λ_lt_κ) _ <;>
      refine' lt_of_le_of_lt (mk_subtype_mono (diff_subset _ _)) _
    exact φ.litterMap_dom_small.mono (inter_subset_left _ _)
    exact (φ.litterMap_dom_small.mono (inter_subset_left _ _)).image

/-!
# Completed permutations
-/


/-- A local permutation induced by completing the orbits of atoms in a near-litter action.
This function creates forward and backward images of atoms in the *sandbox litter*,
a litter which is away from the domain and range of the approximation in question, so it should
not interfere with other constructions. -/
noncomputable def completeAtomPerm (hφ : φ.Lawful) : LocalPerm Atom :=
  LocalPerm.complete φ.atomMapOrElse φ.atomMap.Dom (litterSet φ.sandboxLitter)
    φ.mk_atomMap_image_le_mk_sandbox (by simpa only [mk_litterSet] using κ_isRegular.aleph0_le)
    φ.disjoint_sandbox (φ.atomMapOrElse_injective hφ)

theorem sandboxSubset_small :
    Small
      (LocalPerm.sandboxSubset φ.mk_atomMap_image_le_mk_sandbox
        (by simpa only [mk_litterSet] using κ_isRegular.aleph0_le)) := by
  rw [Small]
  rw [Cardinal.mk_congr (LocalPerm.sandboxSubsetEquiv _ _)]
  simp only [mk_sum, mk_prod, mk_denumerable, lift_aleph0, lift_uzero, lift_id]
  refine' add_lt_of_lt κ_isRegular.aleph0_le _ _ <;>
    refine' mul_lt_of_lt κ_isRegular.aleph0_le (lt_of_le_of_lt aleph0_le_mk_Λ Λ_lt_κ) _ <;>
    refine' lt_of_le_of_lt (mk_subtype_mono (diff_subset _ _)) _
  · exact φ.atomMap_dom_small
  · exact lt_of_le_of_lt mk_image_le φ.atomMap_dom_small

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
  domain_small _ := Small.mono (inter_subset_right _ _) (φ.completeAtomPerm_domain_small hφ)

variable {litter_perm : LocalPerm Litter}

theorem completeAtomPerm_apply_eq (hφ : φ.Lawful) {a : Atom} (ha : (φ.atomMap a).Dom) :
    φ.completeAtomPerm hφ a = (φ.atomMap a).get ha := by
  rwa [completeAtomPerm, LocalPerm.complete_apply_eq, atomMapOrElse_of_dom]

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
    π • L.toNearLitter = (φ.litterMap L).get hL := by
  refine' SetLike.coe_injective _
  ext a : 1
  simp only [mem_smul_set_iff_inv_smul_mem, NearLitterPerm.smul_nearLitter_coe, Litter.coe_toNearLitter,
    mem_litterSet, SetLike.mem_coe]
  constructor
  · intro ha
    by_cases π.IsException a
    · suffices h' : π⁻¹ • a ∈ φ.atomMap.Dom
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
        rw [φ.atomMapOrElse_of_dom hc₁] at hc₂
        have := hφL.fwd c hc₁ (by rwa [hc₂])
        rw [hc₂] at this
        exact this
      · exfalso
        refine φ.sandboxLitter_not_banned ?_
        rw [← eq_of_mem_litterSet_of_mem_litterSet ha (LocalPerm.sandboxSubset_subset _ _ hdom)]
        exact BannedLitter.litterDom L hL
    · by_contra h'
      simp only [NearLitterPerm.IsException, mem_litterSet, not_or, Classical.not_not, ha] at h
      obtain ⟨b, hb, rfl⟩ :=
        hφL.diff (Or.inr ⟨by rw [← hπL, h.2, smul_inv_smul, mem_litterSet], h'⟩)
      refine' h' ((hφ.atom_mem b hb L hL).mp _)
      have := hπ.map_atom b (Or.inl (Or.inl hb))
      rw [φ.complete_smul_atom_eq hb] at this
      rw [this, inv_smul_smul] at ha
      exact ha
  · intro ha
    -- TODO: probably possible to clean up `by_cases` into a `suffices`
    by_cases π⁻¹ • a ∈ φ.atomMap.Dom
    · rw [hφ.atom_mem _ h L hL]
      have := hπ.map_atom _ (Or.inl (Or.inl h))
      rw [φ.complete_smul_atom_eq h] at this
      rw [this, smul_inv_smul]
      exact ha
    have haL : a ∈ litterSet ((φ.litterMap L).get hL).fst
    · by_contra h'
      obtain ⟨b, hb, rfl⟩ := hφL.diff (Or.inl ⟨ha, h'⟩)
      have := hπ.map_atom b (Or.inl (Or.inl hb))
      rw [φ.complete_smul_atom_eq hb] at this
      rw [this, inv_smul_smul] at h
      exact h hb
    by_contra h'
    have hex : π.IsException a
    · refine' Or.inr fun h'' => h' (h''.trans _)
      rw [inv_smul_eq_iff, hπL]
      exact haL
    obtain (hdom | ⟨b, hb₁, hb₂⟩) | hdom := hπ.exception_mem a hex
    · obtain ⟨b, hb₁, hb₂⟩ := hφL.back ⟨hdom, ha⟩
      have := hπ.map_atom b (Or.inl (Or.inl hb₁))
      rw [φ.complete_smul_atom_eq hb₁] at this
      rw [this, smul_eq_iff_eq_inv_smul] at hb₂
      rw [hb₂] at hb₁
      exact h hb₁
    · rw [φ.atomMapOrElse_of_dom hb₁] at hb₂
      have := hπ.map_atom b (Or.inl (Or.inl hb₁))
      rw [φ.complete_smul_atom_eq hb₁, hb₂, ← inv_smul_eq_iff] at this
      rw [this] at h
      exact h hb₁
    · refine' φ.sandboxLitter_not_banned _
      rw [eq_of_mem_litterSet_of_mem_litterSet (LocalPerm.sandboxSubset_subset _ _ hdom) haL]
      exact BannedLitter.litterMap L hL

theorem smul_nearLitter_eq_of_preciseAt {hφ : φ.Lawful} {π : NearLitterPerm}
    (hπ : (φ.complete hφ A).ExactlyApproximates π) {N : NearLitter} (hN : (φ.litterMap N.1).Dom)
    (hw : φ.PreciseAt hN) (hπL : π • N.1 = ((φ.litterMap N.1).get hN).1) :
    ((π • N : NearLitter) : Set Atom) =
    ((φ.litterMap N.1).get hN : Set Atom) ∆ (π • litterSet N.1 ∆ N) := by
  refine' (NearLitterPerm.smul_nearLitter_eq_smul_symmDiff_smul _ _).trans _
  rw [← φ.smul_toNearLitter_eq_of_preciseAt hπ hN hw hπL]
  rfl

end NearLitterAction

end ConNF
