import Mathlib.Order.Extension.Well
import ConNF.Foa.Complete.AtomCompletion
import ConNF.Foa.Complete.NearLitterCompletion

open Equiv Function Quiver Set Sum WithBot

open scoped Classical Pointwise

universe u

namespace ConNF

namespace StructApprox

variable [Params.{u}] {α : Λ} [PositionData] [Phase2Assumptions α] {β : Iic α}
  [FreedomOfActionHypothesis β]

/-!
We now construct the completed action of a structural approximation using well-founded recursion
on support conditions. It remains to prove that this map yields an allowable permutation.
TODO: Rename `completeAtomMap`, `atomCompletion` etc.
-/

noncomputable def completeAtomMap (π : StructApprox β) : ExtendedIndex β → Atom → Atom :=
  Hypothesis.fixAtom π.atomCompletion π.nearLitterCompletion

noncomputable def completeNearLitterMap (π : StructApprox β) :
    ExtendedIndex β → NearLitter → NearLitter :=
  Hypothesis.fixNearLitter π.atomCompletion π.nearLitterCompletion

noncomputable def completeLitterMap (π : StructApprox β) (A : ExtendedIndex β) (L : Litter) :
    Litter :=
  (π.completeNearLitterMap A L.toNearLitter).1

noncomputable def foaHypothesis (π : StructApprox β) {c : SupportCondition β} : Hypothesis c :=
  ⟨fun B b _ => π.completeAtomMap B b, fun B N _ => π.completeNearLitterMap B N⟩

variable {π : StructApprox β}

section MapSpec

variable {A : ExtendedIndex β} {a : Atom} {L : Litter} {N : NearLitter}

theorem completeAtomMap_eq : π.completeAtomMap A a = π.atomCompletion A a π.foaHypothesis :=
  Hypothesis.fixAtom_eq _ _ _ _

theorem completeNearLitterMap_eq :
    π.completeNearLitterMap A N = π.nearLitterCompletion A N π.foaHypothesis :=
  Hypothesis.fixNearLitter_eq _ _ _ _

theorem completeLitterMap_eq :
    π.completeLitterMap A L = π.litterCompletion A L π.foaHypothesis := by
  rw [completeLitterMap, completeNearLitterMap_eq]
  rfl

theorem completeNearLitterMap_fst_eq :
    (π.completeNearLitterMap A L.toNearLitter).1 = π.completeLitterMap A L :=
  rfl

@[simp]
theorem completeNearLitterMap_fst_eq' :
    (π.completeNearLitterMap A N).1 = π.completeLitterMap A N.1 := by
  rw [completeNearLitterMap_eq, nearLitterCompletion, completeLitterMap_eq]
  rfl

@[simp]
theorem foaHypothesis_atomImage {c : SupportCondition β} (h : (inl a, A) <[α] c) :
    (π.foaHypothesis : Hypothesis c).atomImage A a h = π.completeAtomMap A a :=
  rfl

@[simp]
theorem foaHypothesis_nearLitterImage {c : SupportCondition β} (h : (inr N, A) <[α] c) :
    (π.foaHypothesis : Hypothesis c).nearLitterImage A N h = π.completeNearLitterMap A N :=
  rfl

end MapSpec

theorem completeAtomMap_eq_of_mem_domain {a} {A} (h : a ∈ (π A).atomPerm.domain) :
    π.completeAtomMap A a = π A • a := by rw [completeAtomMap_eq, atomCompletion, dif_pos h]

theorem completeAtomMap_eq_of_not_mem_domain {a} {A} (h : a ∉ (π A).atomPerm.domain) :
    π.completeAtomMap A a =
      ((π A).largestSublitter a.1).equiv ((π A).largestSublitter (π.completeLitterMap A a.1))
        ⟨a, (π A).mem_largestSublitter_of_not_mem_domain a h⟩ := by
  rw [completeAtomMap_eq, atomCompletion, dif_neg h]
  rfl

@[simp]
def nearLitterHypothesis_eq (A : ExtendedIndex β) (N : NearLitter) :
    nearLitterHypothesis A N π.foaHypothesis = π.foaHypothesis :=
  rfl

/-- A basic definition unfold. -/
theorem completeLitterMap_eq_of_inflexibleCoe {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleCoe L A) (h₁ h₂) :
    π.completeLitterMap A L =
      fuzz (WithBot.coe_ne_coe.mpr <| coe_ne' h.hδε)
        ((ihAction (π.foaHypothesis : Hypothesis ⟨inr L.toNearLitter, A⟩)).hypothesisedAllowable h
            h₁ h₂ •
          h.t) := by
  rw [completeLitterMap_eq, litterCompletion_of_inflexibleCoe]

theorem completeLitterMap_eq_of_inflexible_coe' {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleCoe L A) :
    π.completeLitterMap A L =
      if h' : _ ∧ _ then
        fuzz (WithBot.coe_ne_coe.mpr <| coe_ne' h.hδε)
          ((ihAction (π.foaHypothesis : Hypothesis ⟨inr L.toNearLitter, A⟩)).hypothesisedAllowable h
              h'.1 h'.2 •
            h.t)
      else L := by
  rw [completeLitterMap_eq, litterCompletion_of_inflexibleCoe']

/-- A basic definition unfold. -/
theorem completeLitterMap_eq_of_inflexibleBot {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleBot L A) :
    π.completeLitterMap A L =
      fuzz (show (⊥ : TypeIndex) ≠ (h.ε : Λ) from WithBot.bot_ne_coe)
        (π.completeAtomMap (h.B.cons (WithBot.bot_lt_coe _)) h.a) := by
  rw [completeLitterMap_eq, litterCompletion_of_inflexibleBot] <;> rfl

/-- A basic definition unfold. -/
theorem completeLitterMap_eq_of_flexible {A : ExtendedIndex β} {L : Litter} (h : Flexible α L A) :
    π.completeLitterMap A L = NearLitterApprox.flexibleCompletion α (π A) A • L := by
  rw [completeLitterMap_eq, litterCompletion_of_flexible _ _ _ _ h]

-- TODO: move to StructPerm
@[simp]
theorem _root_.ConNF.StructPerm.derivative_fst {α β : TypeIndex} (π : StructPerm α) (A : Path α β)
    (N : NearLitter) : (StructPerm.derivative A π • N).fst = StructPerm.derivative A π • N.fst :=
  rfl

theorem toStructPerm_bot :
    (Allowable.toStructPerm : Allowable ⊥ → StructPerm ⊥) = StructPerm.toBotIso.toMonoidHom :=
  rfl

@[simp]
theorem toStructPerm_toNearLitterPerm (π : Allowable ⊥) :
    StructPerm.toNearLitterPerm (Allowable.toStructPerm π) = π := by
  rfl

-- TODO: use this
theorem completeNearLitterMap_eq' (A : ExtendedIndex β) (N : NearLitter) :
    (π.completeNearLitterMap A N : Set Atom) =
      (π.completeNearLitterMap A N.fst.toNearLitter : Set Atom) ∆
        (π.completeAtomMap A '' litterSet N.fst ∆ ↑N) := by
  simp only [completeNearLitterMap_eq, nearLitterCompletion, nearLitterCompletionMap,
    nearLitterHypothesis_eq, NearLitterApprox.coe_largestSublitter, mem_diff,
    foaHypothesis_atomImage, NearLitter.coe_mk, Subtype.coe_mk, Litter.coe_toNearLitter,
    Litter.toNearLitter_fst, symmDiff_self, bot_eq_empty, mem_empty_iff_false, false_and_iff,
    iUnion_neg', not_false_iff, iUnion_empty, symmDiff_empty]
  ext a : 1
  constructor
  · rintro (⟨ha₁ | ⟨a, ha₁, rfl⟩, ha₂⟩ | ⟨⟨_, ⟨b, rfl⟩, _, ⟨⟨hb₁, hb₂⟩, rfl⟩, ha⟩, ha₂⟩)
    · refine' Or.inl ⟨Or.inl ha₁, _⟩
      simp only [mem_image, not_exists, not_and]
      intro b hb
      by_cases b ∈ (π A).atomPerm.domain
      · rw [completeAtomMap_eq_of_mem_domain h]
        rintro rfl
        exact ha₁.2 ((π A).atomPerm.map_domain h)
      · simp only [mem_iUnion, mem_singleton_iff, not_exists, and_imp] at ha₂
        exact Ne.symm (ha₂ b hb h)
    · by_cases a ∈ litterSet N.fst
      · refine' Or.inl ⟨Or.inr ⟨a, ⟨h, ha₁.2⟩, rfl⟩, _⟩
        simp only [mem_image, not_exists, not_and]
        intro b hb
        by_cases hb' : b ∈ (π A).atomPerm.domain
        · rw [completeAtomMap_eq_of_mem_domain hb']
          intro hab
          cases (π A).atomPerm.injOn hb' ha₁.2 hab
          obtain hb | hb := hb
          exact hb.2 ha₁.1
          exact hb.2 h
        · simp only [mem_iUnion, mem_singleton_iff, not_exists, and_imp] at ha₂
          exact Ne.symm (ha₂ b hb hb')
      · refine' Or.inr ⟨⟨a, Or.inr ⟨ha₁.1, h⟩, _⟩, _⟩
        · simp only [completeAtomMap_eq_of_mem_domain ha₁.2]
        rintro (ha | ⟨b, hb₁, hb₂⟩)
        · exact ha.2 ((π A).atomPerm.map_domain ha₁.2)
        · cases (π A).atomPerm.injOn hb₁.2 ha₁.2 hb₂
          exact h hb₁.1
    · simp only [mem_singleton_iff] at ha
      subst ha
      refine' Or.inr ⟨⟨b, hb₁, rfl⟩, _⟩
      contrapose! ha₂
      obtain ha₂ | ha₂ := ha₂
      · exact Or.inl ha₂
      obtain ⟨a, ha₁, ha₂⟩ := ha₂
      by_cases a ∈ N
      · rw [← ha₂]
        exact Or.inr ⟨a, ⟨h, ha₁.2⟩, rfl⟩
      rw [completeAtomMap_eq_of_not_mem_domain hb₂]
      simp only [mem_union, mem_diff, mem_litterSet, Sublitter.equiv_apply_fst_eq,
        NearLitterApprox.largestSublitter_litter]
      refine' Or.inl ⟨_, _⟩
      · suffices b ∈ litterSet N.fst by
          rw [mem_litterSet] at this
          rw [this, completeLitterMap_eq]
        obtain hb₁ | hb₁ := hb₁
        · exact hb₁.1
        · exfalso
          rw [completeAtomMap_eq_of_not_mem_domain hb₂] at ha₂
          have : π A • a ∈ _ := (π A).atomPerm.map_domain ha₁.2
          dsimp only at ha₂
          rw [ha₂] at this
          exact NearLitterApprox.not_mem_domain_of_mem_largestSublitter _
            (Sublitter.equiv_apply_mem _) this
      · exact NearLitterApprox.not_mem_domain_of_mem_largestSublitter _
          (Sublitter.equiv_apply_mem _)
  · rintro (⟨ha₁ | ⟨a, ha₁, rfl⟩, ha₂⟩ | ⟨⟨a, ha₁, rfl⟩, ha₂⟩)
    · refine' Or.inl ⟨Or.inl ha₁, _⟩
      simp only [mem_iUnion, mem_singleton_iff, not_exists, and_imp]
      rintro b hb _ rfl
      exact ha₂ ⟨b, hb, rfl⟩
    · refine' Or.inl ⟨_, _⟩
      · by_cases a ∈ N
        · exact Or.inr ⟨a, ⟨h, ha₁.2⟩, rfl⟩
        · simp only [mem_image, not_exists, not_and] at ha₂
          have := ha₂ a (Or.inl ⟨ha₁.1, h⟩)
          rw [completeAtomMap_eq_of_mem_domain ha₁.2] at this
          cases this rfl
      · contrapose! ha₂
        obtain ⟨_, ⟨b, rfl⟩, _, ⟨hb, rfl⟩, ha₂⟩ := ha₂
        simp only [mem_singleton_iff] at ha₂
        rw [ha₂]
        exact ⟨b, hb.1, rfl⟩
    · rw [mem_union, not_or] at ha₂
      by_cases ha : a ∈ litterSet N.fst
      · have : a ∉ (π A).atomPerm.domain := by
          intro h
          refine' ha₂.2 ⟨a, ⟨ha, h⟩, _⟩
          simp only [completeAtomMap_eq_of_mem_domain h]
        refine' Or.inr ⟨_, _⟩
        · exact ⟨_, ⟨a, rfl⟩, _, ⟨⟨ha₁, this⟩, rfl⟩, rfl⟩
        · rintro (h | ⟨b, hb₁, hb₂⟩)
          · exact ha₂.1 h
          simp only [completeAtomMap_eq_of_not_mem_domain this] at hb₂
          have : π A • b ∈ _ := (π A).atomPerm.map_domain hb₁.2
          rw [hb₂] at this
          exact
            NearLitterApprox.not_mem_domain_of_mem_largestSublitter _
              (Sublitter.equiv_apply_mem _) this
      · by_cases a ∈ (π A).atomPerm.domain
        · refine' Or.inl ⟨_, _⟩
          · simp only [completeAtomMap_eq_of_mem_domain h]
            refine' Or.inr ⟨a, ⟨_, h⟩, rfl⟩
            obtain ha₁ | ha₁ := ha₁
            · cases ha ha₁.1
            · exact ha₁.1
          · simp only [mem_iUnion, mem_singleton_iff, not_exists, and_imp]
            intro b _ hb hab
            rw [completeAtomMap_eq_of_mem_domain h, completeAtomMap_eq_of_not_mem_domain hb] at hab
            have : π A • a ∈ _ := (π A).atomPerm.map_domain h
            rw [hab] at this
            exact
              NearLitterApprox.not_mem_domain_of_mem_largestSublitter _
                (Sublitter.equiv_apply_mem _) this
        · refine' Or.inr ⟨_, _⟩
          · exact ⟨_, ⟨a, rfl⟩, _, ⟨⟨ha₁, h⟩, rfl⟩, rfl⟩
          rintro (h' | ⟨b, hb₁, hb₂⟩)
          · exact ha₂.1 h'
          simp only [completeAtomMap_eq_of_not_mem_domain h] at hb₂
          have : π A • b ∈ _ := (π A).atomPerm.map_domain hb₁.2
          rw [hb₂] at this
          exact NearLitterApprox.not_mem_domain_of_mem_largestSublitter _
            (Sublitter.equiv_apply_mem _) this

theorem completeNearLitterMap_toNearLitter_eq (A : ExtendedIndex β) (L : Litter) :
    (completeNearLitterMap π A L.toNearLitter : Set Atom) =
      litterSet (completeLitterMap π A L) \ (π A).atomPerm.domain ∪
        π A • (litterSet L ∩ (π A).atomPerm.domain) := by
  rw [completeNearLitterMap_eq, nearLitterCompletion, NearLitter.coe_mk, Subtype.coe_mk,
    nearLitterCompletionMap]
  simp only [nearLitterHypothesis_eq, NearLitterApprox.coe_largestSublitter,
    Litter.coe_toNearLitter, mem_diff, Litter.toNearLitter_fst, symmDiff_self, bot_eq_empty,
    mem_empty_iff_false, false_and_iff, iUnion_neg', not_false_iff, iUnion_empty, symmDiff_empty]
  rw [completeLitterMap_eq]
  rfl

theorem eq_of_mem_completeNearLitterMap {L₁ L₂ : Litter} {A : ExtendedIndex β} (a : Atom)
    (ha₁ : a ∈ π.completeNearLitterMap A L₁.toNearLitter)
    (ha₂ : a ∈ π.completeNearLitterMap A L₂.toNearLitter) :
    π.completeLitterMap A L₁ = π.completeLitterMap A L₂ := by
  rw [← SetLike.mem_coe, completeNearLitterMap_toNearLitter_eq] at ha₁ ha₂
  obtain ⟨ha₁, ha₁'⟩ | ha₁ := ha₁ <;> obtain ⟨ha₂, ha₂'⟩ | ha₂ := ha₂
  · exact eq_of_mem_litterSet_of_mem_litterSet ha₁ ha₂
  · obtain ⟨b, hb, rfl⟩ := ha₂
    cases ha₁' ((π A).atomPerm.map_domain hb.2)
  · obtain ⟨b, hb, rfl⟩ := ha₁
    cases ha₂' ((π A).atomPerm.map_domain hb.2)
  · obtain ⟨b, hb, rfl⟩ := ha₁
    obtain ⟨c, hc, hc'⟩ := ha₂
    cases (π A).atomPerm.injOn hc.2 hb.2 hc'
    rw [eq_of_mem_litterSet_of_mem_litterSet hb.1 hc.1]

theorem eq_of_completeLitterMap_inter_nonempty {L₁ L₂ : Litter} {A : ExtendedIndex β}
    (h :
      ((π.completeNearLitterMap A L₁.toNearLitter : Set Atom) ∩
          π.completeNearLitterMap A L₂.toNearLitter).Nonempty) :
    π.completeLitterMap A L₁ = π.completeLitterMap A L₂ := by
  obtain ⟨a, ha₁, ha₂⟩ := h
  exact eq_of_mem_completeNearLitterMap a ha₁ ha₂

end StructApprox

end ConNF
