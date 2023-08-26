import Mathlib.Order.Extension.Well
import ConNF.Foa.AtomCompletion
import ConNF.Foa.NearLitterCompletion

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
      fMap (WithBot.coe_ne_coe.mpr <| coe_ne' h.hδε)
        ((ihAction (π.foaHypothesis : Hypothesis ⟨inr L.toNearLitter, A⟩)).hypothesisedAllowable h
            h₁ h₂ •
          h.t) := by
  rw [completeLitterMap_eq, litterCompletion_of_inflexibleCoe]

theorem completeLitterMap_eq_of_inflexible_coe' {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleCoe L A) :
    π.completeLitterMap A L =
      if h' : _ ∧ _ then
        fMap (WithBot.coe_ne_coe.mpr <| coe_ne' h.hδε)
          ((ihAction (π.foaHypothesis : Hypothesis ⟨inr L.toNearLitter, A⟩)).hypothesisedAllowable h
              h'.1 h'.2 •
            h.t)
      else L := by
  rw [completeLitterMap_eq, litterCompletion_of_inflexibleCoe']

/-- A basic definition unfold. -/
theorem completeLitterMap_eq_of_inflexibleBot {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleBot L A) :
    π.completeLitterMap A L =
      fMap (show (⊥ : TypeIndex) ≠ (h.ε : Λ) from WithBot.bot_ne_coe)
        (π.completeAtomMap (h.B.cons (WithBot.bot_lt_coe _)) h.a) := by
  rw [completeLitterMap_eq, litterCompletion_of_inflexibleBot] <;> rfl

/-- A basic definition unfold. -/
theorem completeLitterMap_eq_of_flexible {A : ExtendedIndex β} {L : Litter} (h : Flexible α L A) :
    π.completeLitterMap A L = NearLitterApprox.flexibleCompletion α (π A) A • L := by
  rw [completeLitterMap_eq, litterCompletion_of_flexible _ _ _ _ h]

def transConstrained (c d : SupportCondition β) : Set (SupportCondition β) :=
  {e | e <[α] c} ∪ {e | e <[α] d}

def reflTransConstrained (c d : SupportCondition β) : Set (SupportCondition β) :=
  {e | e ≤[α] c} ∪ {e | e ≤[α] d}

theorem transConstrained_symm (c d : SupportCondition β) :
    transConstrained c d = transConstrained d c :=
  union_comm _ _

theorem reflTransConstrained_symm (c d : SupportCondition β) :
    reflTransConstrained c d = reflTransConstrained d c :=
  union_comm _ _

@[simp]
theorem transConstrained_self (c : SupportCondition β) : transConstrained c c = {e | e <[α] c} :=
  union_self _

@[simp]
theorem reflTransConstrained_self (c : SupportCondition β) :
    reflTransConstrained c c = {e | e ≤[α] c} :=
  union_self _

theorem mem_reflTransConstrained_of_mem_transConstrained {c d e : SupportCondition β}
    (he : e ∈ transConstrained c d) : e ∈ reflTransConstrained c d := by
  obtain he | he := he
  exact Or.inl he.to_reflTransGen
  exact Or.inr he.to_reflTransGen

theorem transConstrained_trans {c d e f : SupportCondition β} (he : e ∈ transConstrained c d)
    (hf : f ≤[α] e) : f ∈ transConstrained c d := by
  obtain he | he := he
  exact Or.inl (Relation.TransGen.trans_right hf he)
  exact Or.inr (Relation.TransGen.trans_right hf he)

theorem reflTransConstrained_trans {c d e f : SupportCondition β}
    (he : e ∈ reflTransConstrained c d) (hf : f ≤[α] e) : f ∈ reflTransConstrained c d := by
  obtain he | he := he
  exact Or.inl (hf.trans he)
  exact Or.inr (hf.trans he)

theorem transConstrained_of_reflTransConstrained_of_trans_constrains {c d e f : SupportCondition β}
    (he : e ∈ reflTransConstrained c d) (hf : f <[α] e) : f ∈ transConstrained c d := by
  obtain he | he := he
  exact Or.inl (hf.trans_left he)
  exact Or.inr (hf.trans_left he)

theorem transConstrained_of_constrains {c d e f : SupportCondition β}
    (he : e ∈ transConstrained c d) (hf : f ≺[α] e) : f ∈ transConstrained c d :=
  transConstrained_trans he (Relation.ReflTransGen.single hf)

theorem reflTransConstrained_of_constrains {c d e f : SupportCondition β}
    (he : e ∈ reflTransConstrained c d) (hf : f ≺[α] e) : f ∈ reflTransConstrained c d :=
  reflTransConstrained_trans he (Relation.ReflTransGen.single hf)

theorem transConstrained_of_reflTransConstrained_of_constrains {c d e f : SupportCondition β}
    (he : e ∈ reflTransConstrained c d) (hf : f ≺[α] e) : f ∈ transConstrained c d :=
  transConstrained_of_reflTransConstrained_of_trans_constrains he (Relation.TransGen.single hf)

theorem fst_transConstrained {c d : SupportCondition β} {A : ExtendedIndex β} {a : Atom}
    (hac : (inl a, A) ∈ reflTransConstrained c d) :
    (inr a.fst.toNearLitter, A) ∈ transConstrained c d :=
  transConstrained_of_reflTransConstrained_of_constrains hac (Constrains.atom a A)

theorem fst_mem_trans_constrained' {c d : SupportCondition β} {A : ExtendedIndex β} {a : Atom}
    (h : (inl a, A) ∈ transConstrained c d) :
  (inr a.fst.toNearLitter, A) ∈ transConstrained c d :=
  transConstrained_of_constrains h (Constrains.atom a A)

theorem fst_mem_transConstrained {c d : SupportCondition β} {A : ExtendedIndex β} {N : NearLitter}
    (hN : (inr N, A) ∈ transConstrained c d) :
  (inr N.fst.toNearLitter, A) ∈ transConstrained c d := by
  obtain hN | hN := hN
  exact Or.inl (transGen_nearLitter' hN)
  exact Or.inr (transGen_nearLitter' hN)

theorem fst_mem_refl_trans_constrained' {c d : SupportCondition β} {A : ExtendedIndex β} {a : Atom}
    (h : (inl a, A) ∈ reflTransConstrained c d) :
    (inr a.fst.toNearLitter, A) ∈ reflTransConstrained c d :=
  reflTransConstrained_of_constrains h (Constrains.atom a A)

theorem fst_mem_reflTransConstrained {c d : SupportCondition β} {A : ExtendedIndex β}
    {N : NearLitter} (hN : (inr N, A) ∈ reflTransConstrained c d) :
    (inr N.fst.toNearLitter, A) ∈ reflTransConstrained c d := by
  obtain hN | hN := hN
  exact Or.inl (reflTransGen_nearLitter hN)
  exact Or.inr (reflTransGen_nearLitter hN)

theorem fst_mem_transConstrained_of_mem_symmDiff {c d : SupportCondition β} {A : ExtendedIndex β}
    {N : NearLitter} {a : Atom} (h : a ∈ litterSet N.1 ∆ N)
    (hN : (inr N, A) ∈ transConstrained c d) :
    (inr a.fst.toNearLitter, A) ∈ transConstrained c d := by
  obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := h
  · rw [mem_litterSet] at h₁
    rw [h₁]
    exact fst_mem_transConstrained hN
  · obtain hN | hN := hN
    · refine' fst_mem_trans_constrained' (Or.inl _)
      exact Relation.TransGen.head (Constrains.symmDiff N a (Or.inr ⟨h₁, h₂⟩) A) hN
    · refine' fst_mem_trans_constrained' (Or.inr _)
      exact Relation.TransGen.head (Constrains.symmDiff N a (Or.inr ⟨h₁, h₂⟩) A) hN

theorem fst_mem_reflTransConstrained_of_mem_symmDiff {c d : SupportCondition β}
    {A : ExtendedIndex β} {N : NearLitter} {a : Atom} (h : a ∈ litterSet N.1 ∆ N)
    (hN : (inr N, A) ∈ reflTransConstrained c d) :
    (inr a.fst.toNearLitter, A) ∈ reflTransConstrained c d := by
  obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := h
  · rw [mem_litterSet] at h₁
    rw [h₁]
    exact fst_mem_reflTransConstrained hN
  · obtain hN | hN := hN
    · refine' fst_mem_refl_trans_constrained' (Or.inl _)
      exact Relation.ReflTransGen.head (Constrains.symmDiff N a (Or.inr ⟨h₁, h₂⟩) A) hN
    · refine' fst_mem_refl_trans_constrained' (Or.inr _)
      exact Relation.ReflTransGen.head (Constrains.symmDiff N a (Or.inr ⟨h₁, h₂⟩) A) hN

theorem fst_mem_transConstrained_of_mem {c d : SupportCondition β} {A : ExtendedIndex β}
    {N : NearLitter} {a : Atom} (h : a ∈ N) (hN : (inr N, A) ∈ transConstrained c d) :
    (inr a.fst.toNearLitter, A) ∈ transConstrained c d := by
  by_cases ha : a.1 = N.1
  · rw [ha]
    exact fst_mem_transConstrained hN
  · exact fst_mem_transConstrained_of_mem_symmDiff (Or.inr ⟨h, ha⟩) hN

theorem eq_of_sublitter_bijection_apply_eq {π : NearLitterApprox} {L₁ L₂ L₃ L₄ : Litter} {a b} :
    ((π.largestSublitter L₁).equiv (π.largestSublitter L₂) a : Atom) =
        (π.largestSublitter L₃).equiv (π.largestSublitter L₄) b →
      L₁ = L₃ → L₂ = L₄ → (a : Atom) = b := by
  rintro h₁ rfl rfl
  simp only [Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq] at h₁
  rw [h₁]

noncomputable def constrainedAction (π : StructApprox β) (s : Set (SupportCondition β))
    (hs : Small s) : StructAction β := fun B =>
  { atomMap := fun a =>
      ⟨∃ c : SupportCondition β, c ∈ s ∧ (inl a, B) ≤[α] c,
        fun _ => π.completeAtomMap B a⟩
    litterMap := fun L =>
      ⟨∃ c : SupportCondition β, c ∈ s ∧ (inr L.toNearLitter, B) ≤[α] c,
        fun _ => π.completeNearLitterMap B L.toNearLitter⟩
    atomMap_dom_small := by
      change Small ((fun a : Atom => (inl a, B)) ⁻¹'
        {c : SupportCondition β | ∃ d : SupportCondition β, d ∈ s ∧ c ≤[α] d})
      refine' Small.preimage _ (reduction_small' α hs)
      intro a b h
      cases h
      rfl
    litterMap_dom_small := by
      change Small ((fun L : Litter => (inr L.toNearLitter, B)) ⁻¹'
        {c : SupportCondition β | ∃ d : SupportCondition β, d ∈ s ∧ c ≤[α] d})
      refine' Small.preimage _ (reduction_small' α hs)
      intro a b h
      cases h
      rfl }

/-- An object like `ih_action` that can take two support conditions. -/
noncomputable def ihsAction (π : StructApprox β) (c d : SupportCondition β) : StructAction β :=
  fun B =>
  { atomMap := fun a => ⟨(inl a, B) ∈ transConstrained c d,
      fun _ => π.completeAtomMap B a⟩
    litterMap := fun L => ⟨(inr L.toNearLitter, B) ∈ transConstrained c d,
      fun _ => π.completeNearLitterMap B L.toNearLitter⟩
    atomMap_dom_small :=
      Small.union (ihAction π.foaHypothesis B).atomMap_dom_small
        (ihAction π.foaHypothesis B).atomMap_dom_small
    litterMap_dom_small :=
      Small.union (ihAction π.foaHypothesis B).litterMap_dom_small
        (ihAction π.foaHypothesis B).litterMap_dom_small }

@[simp]
theorem constrainedAction_atomMap {π : StructApprox β} {s : Set (SupportCondition β)} {hs : Small s}
    {B : ExtendedIndex β} {a : Atom} :
    (constrainedAction π s hs B).atomMap a =
      ⟨∃ c : SupportCondition β, c ∈ s ∧ (inl a, B) ≤[α] c,
        fun _ => completeAtomMap π B a⟩ :=
  rfl

@[simp]
theorem constrainedAction_litterMap {π : StructApprox β} {s : Set (SupportCondition β)}
    {hs : Small s} {B : ExtendedIndex β} {L : Litter} :
    (constrainedAction π s hs B).litterMap L =
      ⟨∃ c : SupportCondition β, c ∈ s ∧ (inr L.toNearLitter, B) ≤[α] c,
        fun _ => π.completeNearLitterMap B L.toNearLitter⟩ :=
  rfl

@[simp]
theorem ihsAction_atomMap {π : StructApprox β} {c d : SupportCondition β} {B : ExtendedIndex β}
    {a : Atom} :
    (ihsAction π c d B).atomMap a =
      ⟨(inl a, B) ∈ transConstrained c d,
        fun _ => completeAtomMap π B a⟩ :=
  rfl

@[simp]
theorem ihsAction_litterMap {π : StructApprox β} {c d : SupportCondition β} {B : ExtendedIndex β}
    {L : Litter} :
    (ihsAction π c d B).litterMap L =
      ⟨(inr L.toNearLitter, B) ∈ transConstrained c d,
        fun _ => π.completeNearLitterMap B L.toNearLitter⟩ :=
  rfl

theorem ihsAction_symm (π : StructApprox β) (c d : SupportCondition β) :
    ihsAction π c d = ihsAction π d c := by
  funext
  ext
  · funext
    rw [ihsAction_atomMap, ihsAction_atomMap, transConstrained_symm]
  · funext
    rw [ihsAction_litterMap, ihsAction_litterMap, transConstrained_symm]

@[simp]
theorem ihsAction_self (π : StructApprox β) (c : SupportCondition β) :
    ihsAction π c c = ihAction (π.foaHypothesis : Hypothesis c) := by
  funext
  ext
  · funext
    rw [ihsAction_atomMap, ihAction_atomMap, transConstrained_self]
    rfl
  · funext
    rw [ihsAction_litterMap, ihAction_litterMap, transConstrained_self]
    rfl

theorem constrainedAction_mono {π : StructApprox β} {s t : Set (SupportCondition β)} {hs : Small s}
    {ht : Small t} (h : s ⊆ t) : constrainedAction π s hs ≤ constrainedAction π t ht :=
  fun _ =>
  ⟨⟨fun _ ha => ⟨ha.choose, h ha.choose_spec.1, ha.choose_spec.2⟩, fun _ _ => rfl⟩,
    ⟨fun _ hL => ⟨hL.choose, h hL.choose_spec.1, hL.choose_spec.2⟩, fun _ _ => rfl⟩⟩

theorem ihAction_le_constrainedAction {π : StructApprox β} {s : Set (SupportCondition β)}
    {hs : Small s} (c : SupportCondition β) (hc : ∃ d : SupportCondition β, d ∈ s ∧ c ≤[α] d) :
    ihAction (π.foaHypothesis : Hypothesis c) ≤ constrainedAction π s hs :=
  fun _ =>
  ⟨⟨fun _ ha => ⟨hc.choose, hc.choose_spec.1, _root_.trans ha.to_reflTransGen hc.choose_spec.2⟩,
    fun _ _ => rfl⟩,
  ⟨fun _ hL => ⟨hc.choose, hc.choose_spec.1, _root_.trans hL.to_reflTransGen hc.choose_spec.2⟩,
    fun _ _ => rfl⟩⟩

theorem ihAction_eq_constrainedAction (π : StructApprox β) (c : SupportCondition β) :
    ihAction (π.foaHypothesis : Hypothesis c) =
      constrainedAction π {d | d ≺[α] c} (small_constrains c) := by
  funext
  ext
  · funext
    ext
    simp only [ihAction_atomMap, foaHypothesis_atomImage, Part.mem_mk_iff,
      Relation.TransGen.tail'_iff, exists_prop,
      constrainedAction_atomMap, mem_setOf_eq, and_congr_left_iff]
    intro
    simp_rw [and_comm]
  · funext
    ext
    simp only [ihAction_litterMap, foaHypothesis_nearLitterImage, Part.mem_mk_iff,
      Relation.TransGen.tail'_iff, exists_prop,
      constrainedAction_litterMap, mem_setOf_eq, and_congr_left_iff]
    intro
    simp_rw [and_comm]

theorem ihsAction_eq_constrainedAction (π : StructApprox β) (c d : SupportCondition β) :
    ihsAction π c d =
      constrainedAction π ({e | e ≺[α] c} ∪ {e | e ≺[α] d})
        ((small_constrains c).union (small_constrains d)) := by
  funext
  ext
  · funext
    ext
    simp only [Relation.TransGen.tail'_iff, transConstrained, mem_union, ihsAction_atomMap,
      Part.mem_mk_iff, exists_prop, mem_setOf_eq, constrainedAction_atomMap, and_congr_left_iff]
    intro
    constructor
    · rintro (⟨b, hb₁, hb₂⟩ | ⟨b, hb₁, hb₂⟩)
      · exact ⟨b, Or.inl hb₂, hb₁⟩
      · exact ⟨b, Or.inr hb₂, hb₁⟩
    · rintro ⟨b, hb₁ | hb₁, hb₂⟩
      · exact Or.inl ⟨b, hb₂, hb₁⟩
      · exact Or.inr ⟨b, hb₂, hb₁⟩
  · funext
    ext
    simp only [Relation.TransGen.tail'_iff, transConstrained, mem_union, Part.mem_mk_iff,
      exists_prop, mem_setOf_eq, and_congr_left_iff, ihsAction_litterMap,
      constrainedAction_litterMap]
    intro
    constructor
    · rintro (⟨b, hb₁, hb₂⟩ | ⟨b, hb₁, hb₂⟩)
      · exact ⟨b, Or.inl hb₂, hb₁⟩
      · exact ⟨b, Or.inr hb₂, hb₁⟩
    · rintro ⟨b, hb₁ | hb₁, hb₂⟩
      · exact Or.inl ⟨b, hb₂, hb₁⟩
      · exact Or.inr ⟨b, hb₂, hb₁⟩

theorem ihAction_le_ihsAction (π : StructApprox β) (c d : SupportCondition β) :
    ihAction (π.foaHypothesis : Hypothesis c) ≤ ihsAction π c d :=
  fun _ => ⟨⟨fun _ => Or.inl, fun _ _ => rfl⟩, ⟨fun _ => Or.inl, fun _ _ => rfl⟩⟩

theorem ihAction_le {π : StructApprox β} {c d : SupportCondition β} (h : c ≤[α] d) :
    ihAction (π.foaHypothesis : Hypothesis c) ≤ ihAction (π.foaHypothesis : Hypothesis d) := by
  refine' fun B => ⟨⟨_, fun a h => rfl⟩, ⟨_, fun L h => rfl⟩⟩
  · intro a ha
    exact Relation.TransGen.trans_left ha h
  · intro a ha
    exact Relation.TransGen.trans_left ha h

theorem ihActionSupports {A : ExtendedIndex β} {L : Litter} (h : InflexibleCoe L A) :
    ((ihAction (π.foaHypothesis : Hypothesis ⟨inr L.toNearLitter, A⟩)).comp
      (h.B.cons (coe_lt h.hδ))).Supports h.t
    where
  atom_mem := by
    intro a B ha
    simp only [StructAction.comp_apply, ihAction_atomMap]
    have := mem_reduction_designated_support α h.hδ h.hε h.hδε h.B h.t _ ha
    rw [← h.hL, ← h.hA] at this
    exact this
  litter_mem := by
    intro L B hL
    simp only [StructAction.comp_apply, ihAction_litterMap]
    have := mem_reduction_designated_support α h.hδ h.hε h.hδε h.B h.t _ hL
    rw [← h.hL, ← h.hA] at this
    exact this

theorem transGen_constrains_of_mem_designatedSupport {A : ExtendedIndex β} {L : Litter}
    {h : InflexibleCoe L A} {γ : Iic α} {δ ε : Iio α} {hδ : (δ : Λ) < γ} {hε : (ε : Λ) < γ}
    (hδε : δ ≠ ε) {C : Path (h.δ : TypeIndex) γ} {t : Tangle δ} {d : SupportCondition h.δ}
    (hd₂ :
      (inr (fMap (Subtype.coe_injective.ne (Iio.coe_injective.ne hδε)) t).toNearLitter,
          (C.cons (coe_lt hε)).cons (bot_lt_coe _)) ≤[α]
        d)
    (hd : (d.fst, (h.B.cons (coe_lt h.hδ)).comp d.snd) ≺[α] (inr L.toNearLitter, A))
    {B : ExtendedIndex δ} {a : Atom} (hc : (inl a, B) ∈ (designatedSupport t).carrier) :
    (inl a, (h.B.cons (coe_lt h.hδ)).comp ((C.cons (coe_lt hδ)).comp B)) <[α]
      (inr L.toNearLitter, A) := by
  refine' Relation.TransGen.tail' _ hd
  refine' reflTransGen_constrains_comp (c := (inl a, _)) (d := d) _ (h.B.cons <| coe_lt h.hδ)
  refine' Relation.ReflTransGen.trans _ hd₂
  exact Relation.ReflTransGen.single (Constrains.fMap hδ hε hδε C t _ hc)

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

-- TODO: move earlier and use
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

theorem atom_injective_extends {c d : SupportCondition β} (hcd : (ihsAction π c d).Lawful)
    {a b : Atom} {A : ExtendedIndex β} (hac : (inl a, A) ∈ reflTransConstrained c d)
    (hbc : (inl b, A) ∈ reflTransConstrained c d)
    (h : π.completeAtomMap A a = π.completeAtomMap A b) : a = b :=
  by
  by_cases ha : a ∈ (π A).atomPerm.domain <;> by_cases hb : b ∈ (π A).atomPerm.domain
  · rw [completeAtomMap_eq_of_mem_domain ha, completeAtomMap_eq_of_mem_domain hb] at h
    exact (π A).atomPerm.injOn ha hb h
  · rw [completeAtomMap_eq_of_mem_domain ha, completeAtomMap_eq_of_not_mem_domain hb] at h
    cases
      (π A).not_mem_domain_of_mem_largestSublitter (Subtype.coe_eq_iff.mp h.symm).choose
        ((π A).atomPerm.map_domain ha)
  · rw [completeAtomMap_eq_of_not_mem_domain ha, completeAtomMap_eq_of_mem_domain hb] at h
    cases
      (π A).not_mem_domain_of_mem_largestSublitter (Subtype.coe_eq_iff.mp h).choose
        ((π A).atomPerm.map_domain hb)
  · rw [completeAtomMap_eq_of_not_mem_domain ha, completeAtomMap_eq_of_not_mem_domain hb] at h
    have h₁ := (Subtype.coe_eq_iff.mp h).choose.1
    have h₂ :=
      (((π A).largestSublitter b.1).equiv ((π A).largestSublitter (π.completeLitterMap A b.1))
            ⟨b, (π A).mem_largestSublitter_of_not_mem_domain b hb⟩).prop.1
    have := (hcd A).litterMap_injective (fst_transConstrained hac) (fst_transConstrained hbc) ?_
    · have := eq_of_sublitter_bijection_apply_eq h this (by rw [this])
      exact this
    · refine' NearLitter.inter_nonempty_of_fst_eq_fst _
      simp only [ihsAction_litterMap, completeNearLitterMap_fst_eq]
      exact eq_of_mem_litterSet_of_mem_litterSet h₁ h₂

def InOut (π : NearLitterPerm) (a : Atom) (L : Litter) : Prop :=
  Xor' (a.1 = L) ((π • a).1 = π • L)

theorem inOut_def {π : NearLitterPerm} {a : Atom} {L : Litter} :
    InOut π a L ↔ Xor' (a.1 = L) ((π • a).1 = π • L) :=
  Iff.rfl

structure _root_.ConNF.NearLitterPerm.Biexact (π π' : NearLitterPerm) (atoms : Set Atom)
    (litters : Set Litter) : Prop where
  smul_eq_smul_atom : ∀ a ∈ atoms, π • a = π' • a
  smul_eq_smul_litter : ∀ L ∈ litters, π • L = π' • L
  left_exact : ∀ L ∈ litters, ∀ a, InOut π a L → π • a = π' • a
  right_exact : ∀ L ∈ litters, ∀ a, InOut π' a L → π • a = π' • a

@[simp]
theorem xor'_elim_left {a b : Prop} (h : a) : Xor' a b ↔ ¬b := by unfold Xor'; tauto

@[simp]
theorem xor'_elim_right {a b : Prop} (h : b) : Xor' a b ↔ ¬a := by unfold Xor'; tauto

@[simp]
theorem xor'_elim_not_left {a b : Prop} (h : ¬a) : Xor' a b ↔ b := by unfold Xor'; tauto

@[simp]
theorem xor'_elim_not_right {a b : Prop} (h : ¬b) : Xor' a b ↔ a := by unfold Xor'; tauto

theorem _root_.ConNF.NearLitterPerm.Biexact.atoms {π π' : NearLitterPerm} (s : Set Atom)
    (hs : ∀ a ∈ s, π • a = π' • a) : NearLitterPerm.Biexact π π' s ∅ :=
  ⟨hs, fun _ => False.elim, fun _ => False.elim, fun _ => False.elim⟩

theorem _root_.ConNF.NearLitterPerm.Biexact.litter {π π' : NearLitterPerm} (L : Litter)
    (hL : π • L = π' • L) (hL₁ : ∀ a, InOut π a L → π • a = π' • a)
    (hL₂ : ∀ a, InOut π' a L → π • a = π' • a) : NearLitterPerm.Biexact π π' ∅ {L} :=
  ⟨fun a ha => ha.elim, fun L' hL' => by cases hL'; exact hL, fun L' hL' => by
    cases hL'; exact hL₁, fun L' hL' => by cases hL'; exact hL₂⟩

theorem _root_.ConNF.NearLitterPerm.Biexact.symm {π π' : NearLitterPerm} {atoms : Set Atom}
    {litters : Set Litter} (h : NearLitterPerm.Biexact π π' atoms litters) :
    NearLitterPerm.Biexact π' π atoms litters :=
  ⟨fun a ha => (h.smul_eq_smul_atom a ha).symm, fun L hL => (h.smul_eq_smul_litter L hL).symm,
    fun L hL a ha => (h.right_exact L hL a ha).symm, fun L hL a ha => (h.left_exact L hL a ha).symm⟩

theorem _root_.ConNF.NearLitterPerm.Biexact.union {π π' : NearLitterPerm} {s₁ s₂ : Set Atom}
    {t₁ t₂ : Set Litter} (h₁ : NearLitterPerm.Biexact π π' s₁ t₁)
    (h₂ : NearLitterPerm.Biexact π π' s₂ t₂) : NearLitterPerm.Biexact π π' (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  ⟨fun a ha => ha.elim (h₁.smul_eq_smul_atom a) (h₂.smul_eq_smul_atom a), fun L hL =>
    hL.elim (h₁.smul_eq_smul_litter L) (h₂.smul_eq_smul_litter L), fun L hL =>
    hL.elim (h₁.left_exact L) (h₂.left_exact L), fun L hL =>
    hL.elim (h₁.right_exact L) (h₂.right_exact L)⟩

theorem _root_.ConNF.NearLitterPerm.Biexact.smul_litter_subset {π π' : NearLitterPerm}
    {atoms : Set Atom} {litters : Set Litter}
    (h : NearLitterPerm.Biexact π π' atoms litters)
    (L : Litter) (hL : L ∈ litters) : (π • L.toNearLitter : Set Atom) ⊆ π' • L.toNearLitter := by
  rintro _ ⟨a, ha, rfl⟩
  simp only [Litter.coe_toNearLitter, mem_litterSet] at ha
  by_cases h' : (π • a).1 = π • L
  by_cases h'' : (π'⁻¹ • π • a).1 = L
  · refine' ⟨_, h'', _⟩
    dsimp only
    rw [smul_inv_smul]
  · have := h.right_exact L hL _ (Or.inr ⟨?_, h''⟩)
    · rw [smul_inv_smul, smul_left_cancel_iff, inv_smul_eq_iff] at this
      dsimp only
      rw [this]
      exact ⟨a, ha, rfl⟩
    · rw [smul_inv_smul, h', h.smul_eq_smul_litter L hL]
  · dsimp only
    rw [h.left_exact L hL a (Or.inl ⟨ha, h'⟩)]
    exact ⟨a, ha, rfl⟩

theorem _root_.ConNF.NearLitterPerm.Biexact.smul_litter {π π' : NearLitterPerm} {atoms : Set Atom}
    {litters : Set Litter} (h : NearLitterPerm.Biexact π π' atoms litters) (L : Litter)
    (hL : L ∈ litters) : π • L.toNearLitter = π' • L.toNearLitter := by
  refine' SetLike.coe_injective _
  refine' subset_antisymm _ _
  exact h.smul_litter_subset L hL
  exact h.symm.smul_litter_subset L hL

theorem _root_.ConNF.NearLitterPerm.Biexact.smul_nearLitter {π π' : NearLitterPerm} {atoms : Set Atom}
    {litters : Set Litter} (h : NearLitterPerm.Biexact π π' atoms litters) (N : NearLitter)
    (hN : N.1 ∈ litters) (hN' : litterSet N.1 ∆ N ⊆ atoms) : π • N = π' • N := by
  refine' SetLike.coe_injective _
  conv_lhs => rw [NearLitterPerm.smul_nearLitter_eq_smul_symmDiff_smul]
  conv_rhs => rw [NearLitterPerm.smul_nearLitter_eq_smul_symmDiff_smul]
  refine' congr_arg₂ _ (congr_arg SetLike.coe (h.smul_litter N.1 hN)) _
  ext a : 1
  constructor
  · rintro ⟨b, hb, rfl⟩
    dsimp only
    rw [h.smul_eq_smul_atom b (hN' hb)]
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    dsimp only
    rw [← h.smul_eq_smul_atom b (hN' hb)]
    exact ⟨b, hb, rfl⟩

/- `in_out` is just another way to quantify exceptions, focusing on a slightly different litter.
Basically `in_out` looks only at images not preimages. -/
theorem isException_of_inOut {π : NearLitterPerm} {a : Atom} {L : Litter} :
    InOut π a L → π.IsException a ∨ π.IsException (π • a) := by
  rintro (⟨rfl, ha⟩ | ha)
  · refine' Or.inr (Or.inr _)
    intro h
    rw [mem_litterSet, eq_inv_smul_iff] at h
    rw [← h, inv_smul_smul] at ha
    exact ha rfl
  · refine' Or.inl (Or.inl _)
    rw [mem_litterSet, ha.1, smul_left_cancel_iff]
    exact Ne.symm ha.2

structure Biexact {β : Iio α} (π π' : StructPerm β) (c : SupportCondition β) : Prop where
  smul_eq_smul_atom :
    ∀ A : ExtendedIndex β,
      ∀ a : Atom, (inl a, A) ≤[α] c → StructPerm.derivative A π • a = StructPerm.derivative A π' • a
  smul_eq_smul_litter :
    ∀ A : ExtendedIndex β,
      ∀ L : Litter,
        (inr L.toNearLitter, A) ≤[α] c →
          Flexible α L A → StructPerm.derivative A π • L = StructPerm.derivative A π' • L
  exact :
    ∀ A : ExtendedIndex β,
      ∀ L : Litter,
        (inr L.toNearLitter, A) ≤[α] c →
          StructPerm.derivative A π • L = StructPerm.derivative A π' • L →
            StructPerm.derivative A π • L.toNearLitter = StructPerm.derivative A π' • L.toNearLitter

theorem Biexact.atoms {β : Iio α} {π π' : StructPerm β} {c : SupportCondition β}
    (h : Biexact π π' c) (A : ExtendedIndex β) :
    NearLitterPerm.Biexact (StructPerm.ofBot <| StructPerm.derivative A π)
      (StructPerm.ofBot <| StructPerm.derivative A π') {a | (inl a, A) ≤[α] c} ∅ :=
  NearLitterPerm.Biexact.atoms _ (h.smul_eq_smul_atom A)

theorem Biexact.constrains {β : Iio α} {π π' : StructPerm β} {c d : SupportCondition β}
    (h : Biexact π π' c) (h' : d ≤[α] c) : Biexact π π' d :=
  ⟨fun A a ha => h.smul_eq_smul_atom A a (ha.trans h'), fun A L hL =>
    h.smul_eq_smul_litter A L (hL.trans h'), fun A L hL => h.exact A L (hL.trans h')⟩

theorem Biexact.smul_eq_smul {β : Iio α} {π π' : Allowable β} {c : SupportCondition β}
    (h : Biexact (Allowable.toStructPerm π) (Allowable.toStructPerm π') c) :
    π • c = π' • c := by
  revert h
  refine' WellFounded.induction (C := fun c => Biexact _ _ c → π • c = π' • c)
    (constrains_wf α β) c _
  clear c
  intro c ih h
  obtain ⟨a | N, A⟩ := c <;> refine' Prod.ext _ rfl
  · change inl _ = inl _
    simp only [inl.injEq]
    exact h.smul_eq_smul_atom A a Relation.ReflTransGen.refl
  change inr _ = inr _
  simp only [inr.injEq]
  by_cases hL : N.IsLitter
  swap
  · have :=
      ih _ (Constrains.nearLitter N (NearLitter.not_isLitter hL) A)
        (h.constrains (reflTransGen_nearLitter Relation.ReflTransGen.refl))
    change (inr _, _) = (inr _, _) at this
    simp only [Prod.mk.injEq, inr.injEq, and_true] at this
    refine' SetLike.coe_injective _
    refine' (NearLitterPerm.smul_nearLitter_eq_smul_symmDiff_smul _ _).trans _
    refine' Eq.trans _ (NearLitterPerm.smul_nearLitter_eq_smul_symmDiff_smul _ _).symm
    refine' congr_arg₂ _ (congr_arg SetLike.coe this) _
    ext a : 1
    constructor
    · rintro ⟨b, hb, rfl⟩
      have : (inl _, _) = (inl _, _) :=
        ih _ (Constrains.symmDiff N b hb A)
          (h.constrains (Relation.ReflTransGen.single <| Constrains.symmDiff N b hb A))
      simp only [Prod.mk.injEq, inl.injEq, and_true] at this
      exact ⟨b, hb, this.symm⟩
    · rintro ⟨b, hb, rfl⟩
      have : (inl _, _) = (inl _, _) :=
        ih _ (Constrains.symmDiff N b hb A)
          (h.constrains (Relation.ReflTransGen.single <| Constrains.symmDiff N b hb A))
      simp only [Prod.mk.injEq, inl.injEq, and_true] at this
      exact ⟨b, hb, this⟩
  obtain ⟨L, rfl⟩ := hL.exists_litter_eq
  suffices
    StructPerm.derivative A (Allowable.toStructPerm π) • L =
    StructPerm.derivative A (Allowable.toStructPerm π') • L
    by exact h.exact _ _ Relation.ReflTransGen.refl this
  obtain hL | hL := flexible_cases α L A
  swap
  · exact h.smul_eq_smul_litter A L Relation.ReflTransGen.refl hL
  induction' hL with γ δ ε hδ hε hδε B t γ ε hε B a
  · rw [StructPerm.derivative_cons, StructPerm.derivative_bot_smul, StructPerm.derivative_cons]
    rw [Allowable.derivative_toStructPerm
      (show Path ((β : IicBot α) : TypeIndex) (γ : IicBot α) from _)]
    refine'
      (toStructPerm_smul_fMap (γ : IicBot α) δ ε (coe_lt hδ) (coe_lt hε)
            (Iio.coe_injective.ne hδε) _ _).trans
        _
    rw [StructPerm.derivative_cons, StructPerm.derivative_bot_smul, StructPerm.derivative_cons]
    rw [Allowable.derivative_toStructPerm
      (show Path ((β : IicBot α) : TypeIndex) (γ : IicBot α) from _)]
    refine'
      Eq.trans _
        (toStructPerm_smul_fMap (γ : IicBot α) δ ε (coe_lt hδ) (coe_lt hε)
            (Iio.coe_injective.ne hδε) _ _).symm
    refine' congr_arg _ _
    rw [← inv_smul_eq_iff, smul_smul]
    refine' (designatedSupport t).supports _ _
    intro c hc
    rw [mul_smul, inv_smul_eq_iff]
    rw [← Allowable.toStructPerm_smul, ← Allowable.toStructPerm_smul, ←
      Allowable.derivative_cons_apply, ← Allowable.derivative_cons_apply, ←
      Allowable.derivative_toStructPerm, ← Allowable.derivative_toStructPerm]
    have := ih (c.fst, (B.cons <| coe_lt hδ).comp c.snd) ?_ ?_
    · refine' Prod.ext _ rfl
      apply_fun Prod.fst at this
      change _ • _ = _ • _
      rw [StructPerm.derivative_derivative, StructPerm.derivative_derivative]
      exact this
    · exact Constrains.fMap hδ hε hδε _ _ _ hc
    · refine' h.constrains (Relation.ReflTransGen.single _)
      exact Constrains.fMap hδ hε hδε _ _ _ hc
  · rw [StructPerm.derivative_cons, StructPerm.derivative_bot_smul, StructPerm.derivative_cons]
    rw [Allowable.derivative_toStructPerm
      (show Path ((β : IicBot α) : TypeIndex) (γ : IicBot α) from _)]
    refine'
      (toStructPerm_smul_fMap (γ : IicBot α) ⊥ ε (bot_lt_coe _) (coe_lt hε)
            IioBot.bot_ne_coe _ _).trans
        _
    rw [StructPerm.derivative_cons, StructPerm.derivative_bot_smul, StructPerm.derivative_cons]
    rw [Allowable.derivative_toStructPerm
      (show Path ((β : IicBot α) : TypeIndex) (γ : IicBot α) from _)]
    refine'
      Eq.trans _
        (toStructPerm_smul_fMap (γ : IicBot α) ⊥ ε (bot_lt_coe _) (coe_lt hε)
            IioBot.bot_ne_coe _ _).symm
    refine' congr_arg _ _
    rw [← Allowable.derivative_cons_apply, ← Allowable.derivative_cons_apply]
    have := ih (inl a, B.cons <| bot_lt_coe _) ?_ ?_
    · change (inl _, _) = (inl _, _) at this
      simp only [Prod.mk.injEq, inl.injEq, and_true] at this
      have h' := Allowable.derivative_toStructPerm
        (show Path ((β : IicBot α) : TypeIndex) (⊥ : IicBot α) from B.cons (bot_lt_coe _))
      dsimp only at h'
      rw [h', h'] at this
      exact this
    · exact Constrains.fMap_bot hε _ _
    · refine' h.constrains (Relation.ReflTransGen.single _)
      exact Constrains.fMap_bot hε _ _

theorem Biexact.smul_eq_smul_nearLitter {β : Iio α} {π π' : Allowable β} {A : ExtendedIndex β}
    {N : NearLitter}
    (h : Biexact (Allowable.toStructPerm π) (Allowable.toStructPerm π') (inr N, A)) :
    StructPerm.derivative A (Allowable.toStructPerm π) • N =
    StructPerm.derivative A (Allowable.toStructPerm π') • N := by
  have : (inr _, _) = (inr _, _) := h.smul_eq_smul
  rw [Prod.mk.inj_iff] at this
  exact inr_injective this.1

theorem mem_dom_of_exactlyApproximates {β : Iio α} {π₀ : StructApprox β} {π : StructPerm β}
    (hπ : π₀.ExactlyApproximates π) {A : ExtendedIndex β} {a : Atom} {L : Litter}
    (h : InOut (StructPerm.ofBot <| StructPerm.derivative A π) a L) :
    a ∈ (π₀ A).atomPerm.domain := by
  obtain h | h := isException_of_inOut h
  · exact (hπ A).exception_mem _ h
  · have h₁ := (hπ A).exception_mem _ h
    have := (hπ A).symm_map_atom _ h₁
    rw [inv_smul_smul] at this
    rw [← this]
    exact (π₀ A).atomPerm.symm.map_domain h₁

/--
We can prove that `map_flexible` holds at any `constrained_action` without any `lawful` hypothesis.
-/
theorem constrainedAction_comp_mapFlexible (hπf : π.Free) {γ : Iio α} {s : Set (SupportCondition β)}
    {hs : Small s} (A : Path (β : TypeIndex) γ) :
    ((constrainedAction π s hs).comp A).MapFlexible := by
  rintro L B ⟨c, hc, hL₁⟩ hL₂
  simp only [StructAction.comp_apply, constrainedAction_litterMap,
    foaHypothesis_nearLitterImage]
  rw [completeNearLitterMap_fst_eq]
  obtain hL₃ | (⟨⟨hL₃⟩⟩ | ⟨⟨hL₃⟩⟩) := flexible_cases' _ L (A.comp B)
  · rw [completeLitterMap_eq_of_flexible hL₃]
    refine' NearLitterApprox.flexibleCompletion_smul_flexible _ _ _ _ _ hL₂
    intro L' hL'
    exact flexible_of_comp_flexible (hπf (A.comp B) L' hL')
  · rw [completeLitterMap_eq_of_inflexibleBot hL₃]
    obtain ⟨δ, ε, hε, C, a, rfl, hC⟩ := hL₃
    contrapose hL₂
    rw [not_flexible_iff] at hL₂ ⊢
    rw [Inflexible_iff] at hL₂
    obtain ⟨δ', ε', ζ', _, hζ', hεζ', C', t', h', rfl⟩ | ⟨δ', ε', hε', C', a', h', rfl⟩ := hL₂
    · have := congr_arg Litter.β h'
      simp only [fMap_β, bot_ne_coe] at this
    · rw [Path.comp_cons, Path.comp_cons] at hC
      cases Subtype.coe_injective (coe_eq_coe.mp (Path.obj_eq_of_cons_eq_cons hC))
      have hC := (Path.heq_of_cons_eq_cons hC).eq
      cases Subtype.coe_injective (coe_eq_coe.mp (Path.obj_eq_of_cons_eq_cons hC))
      exact Inflexible.mk_bot hε _ _
  · rw [completeLitterMap_eq_of_inflexible_coe' hL₃]
    split_ifs
    swap
    · exact hL₂
    obtain ⟨δ, ε, ζ, hε, hζ, hεζ, C, t, rfl, hC⟩ := hL₃
    contrapose hL₂
    rw [not_flexible_iff] at hL₂ ⊢
    rw [Inflexible_iff] at hL₂
    obtain ⟨δ', ε', ζ', hε', hζ', hεζ', C', t', h', rfl⟩ | ⟨δ', ε', hε', C', a', h', rfl⟩ := hL₂
    · rw [Path.comp_cons, Path.comp_cons] at hC
      cases Subtype.coe_injective (coe_eq_coe.mp (Path.obj_eq_of_cons_eq_cons hC))
      have hC := (Path.heq_of_cons_eq_cons hC).eq
      cases Subtype.coe_injective (coe_eq_coe.mp (Path.obj_eq_of_cons_eq_cons hC))
      refine' Inflexible.mk_coe hε hζ hεζ _ _
    · have := congr_arg Litter.β h'
      simp only [fMap_β, bot_ne_coe] at this
      cases this

theorem ihAction_comp_mapFlexible (hπf : π.Free) {γ : Iio α} (c : SupportCondition β)
    (A : Path (β : TypeIndex) γ) :
    ((ihAction (π.foaHypothesis : Hypothesis c)).comp A).MapFlexible := by
  rw [ihAction_eq_constrainedAction]
  exact constrainedAction_comp_mapFlexible hπf A

theorem ihsAction_comp_mapFlexible (hπf : π.Free) {γ : Iio α} (c d : SupportCondition β)
    (A : Path (β : TypeIndex) γ) : ((ihsAction π c d).comp A).MapFlexible := by
  rw [ihsAction_eq_constrainedAction]
  exact constrainedAction_comp_mapFlexible hπf A

theorem completeLitterMap_flexible (hπf : π.Free) {A : ExtendedIndex β} {L : Litter}
    (h : Flexible α L A) : Flexible α (π.completeLitterMap A L) A := by
  rw [completeLitterMap_eq_of_flexible h]
  exact NearLitterApprox.flexibleCompletion_smul_flexible _ _ _ (hπf A) _ h

theorem completeLitterMap_inflexibleBot {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleBot L A) : InflexibleBot (π.completeLitterMap A L) A := by
  rw [completeLitterMap_eq_of_inflexibleBot h]
  obtain ⟨γ, ε, hγε, B, a, rfl, rfl⟩ := h
  exact ⟨γ, ε, hγε, B, _, rfl, rfl⟩

theorem completeLitterMap_inflexibleCoe (hπf : π.Free) {c d : SupportCondition β}
    (hcd : (ihsAction π c d).Lawful) {A : ExtendedIndex β} {L : Litter} (h : InflexibleCoe L A)
    (hL : (inr L.toNearLitter, A) ∈ reflTransConstrained c d) :
    InflexibleCoe (π.completeLitterMap A L) A := by
  rw [completeLitterMap_eq_of_inflexibleCoe h]
  obtain ⟨γ, δ, ε, hδ, hε, hδε, B, a, rfl, rfl⟩ := h
  refine' ⟨_, _, _, hδ, hε, hδε, _, _, rfl, rfl⟩
  · intros A L hL h
    refine' (hcd.le _).comp _
    obtain hL | hL := hL
    · exact (ihAction_le hL).trans (ihAction_le_ihsAction _ _ _)
    · rw [ihsAction_symm]
      exact (ihAction_le hL).trans (ihAction_le_ihsAction _ _ _)
  · intros A L _ h
    exact ihAction_comp_mapFlexible hπf _ _

theorem completeLitterMap_flexible' (hπf : π.Free) {c d : SupportCondition β}
    (hcd : (ihsAction π c d).Lawful) {A : ExtendedIndex β} {L : Litter}
    (hL : (inr L.toNearLitter, A) ∈ reflTransConstrained c d)
    (h : Flexible α (π.completeLitterMap A L) A) : Flexible α L A := by
  obtain h' | h' | h' := flexible_cases' β L A
  · exact h'
  · have := completeLitterMap_inflexibleBot (π := π) h'.some
    rw [flexible_iff_not_inflexibleBot_inflexibleCoe] at h
    cases h.1.false this
  · have := completeLitterMap_inflexibleCoe hπf hcd h'.some hL
    rw [flexible_iff_not_inflexibleBot_inflexibleCoe] at h
    cases h.2.false this

theorem completeLitterMap_flexible_iff (hπf : π.Free) {c d : SupportCondition β}
    (hcd : (ihsAction π c d).Lawful) {A : ExtendedIndex β} {L : Litter}
    (hL : (inr L.toNearLitter, A) ∈ reflTransConstrained c d) :
    Flexible α (π.completeLitterMap A L) A ↔ Flexible α L A :=
  ⟨completeLitterMap_flexible' hπf hcd hL, completeLitterMap_flexible hπf⟩

theorem completeLitterMap_inflexibleBot' (hπf : π.Free) {c d : SupportCondition β}
    (hcd : (ihsAction π c d).Lawful) {A : ExtendedIndex β} {L : Litter}
    (hL : (inr L.toNearLitter, A) ∈ reflTransConstrained c d)
    (h : InflexibleBot (π.completeLitterMap A L) A) : InflexibleBot L A := by
  refine' Nonempty.some _
  obtain h' | h' | h' := flexible_cases' β L A
  · have := completeLitterMap_flexible hπf h'
    rw [flexible_iff_not_inflexibleBot_inflexibleCoe] at this
    cases this.1.false h
  · exact h'
  · have := completeLitterMap_inflexibleCoe hπf hcd h'.some hL
    cases inflexibleBot_inflexibleCoe h this

theorem completeLitterMap_inflexibleBot_iff (hπf : π.Free) {c d : SupportCondition β}
    (hcd : (ihsAction π c d).Lawful) {A : ExtendedIndex β} {L : Litter}
    (hL : (inr L.toNearLitter, A) ∈ reflTransConstrained c d) :
    Nonempty (InflexibleBot (π.completeLitterMap A L) A) ↔ Nonempty (InflexibleBot L A) :=
  ⟨fun ⟨h⟩ => ⟨completeLitterMap_inflexibleBot' hπf hcd hL h⟩, fun ⟨h⟩ =>
    ⟨completeLitterMap_inflexibleBot h⟩⟩

theorem completeLitterMap_inflexibleCoe' (hπf : π.Free) {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleCoe (π.completeLitterMap A L) A) : InflexibleCoe L A := by
  refine' Nonempty.some _
  obtain h' | h' | h' := flexible_cases' β L A
  · have := completeLitterMap_flexible hπf h'
    rw [flexible_iff_not_inflexibleBot_inflexibleCoe] at this
    cases this.2.false h
  · have := completeLitterMap_inflexibleBot (π := π) h'.some
    cases inflexibleBot_inflexibleCoe this h
  · exact h'

theorem completeLitterMap_inflexibleCoe_iff (hπf : π.Free) {c d : SupportCondition β}
    (hcd : (ihsAction π c d).Lawful) {A : ExtendedIndex β} {L : Litter}
    (hL : (inr L.toNearLitter, A) ∈ reflTransConstrained c d) :
    Nonempty (InflexibleCoe (π.completeLitterMap A L) A) ↔ Nonempty (InflexibleCoe L A) :=
  ⟨fun ⟨h⟩ => ⟨completeLitterMap_inflexibleCoe' hπf h⟩, fun ⟨h⟩ =>
    ⟨completeLitterMap_inflexibleCoe hπf hcd h hL⟩⟩

theorem constrainedAction_coherent' (hπf : π.Free) {γ : Iio α} (A : Path (β : TypeIndex) γ)
    (N : ExtendedIndex γ × NearLitter) (s : Set (SupportCondition β)) (hs : Small s)
    (hc : ∃ c : SupportCondition β, c ∈ s ∧ (inr N.2, A.comp N.1) ≤[α] c)
    (hπ : ((constrainedAction π s hs).comp A).Lawful) (ρ : Allowable γ)
    (h : (((constrainedAction π s hs).comp A).rc hπ).ExactlyApproximates
      (Allowable.toStructPerm ρ)) :
    completeNearLitterMap π (A.comp N.1) N.2 =
    StructPerm.derivative N.1 (Allowable.toStructPerm ρ) • N.2 := by
  revert hc
  refine'
    WellFounded.induction
      (C := fun N : ExtendedIndex γ × NearLitter => (∃ c : SupportCondition β, c ∈ s ∧
        Relation.ReflTransGen (Constrains α ↑β) (inr N.snd, Path.comp A N.fst) c) →
        completeNearLitterMap π (Path.comp A N.fst) N.snd =
        StructPerm.derivative N.fst (Allowable.toStructPerm ρ) • N.snd)
      (InvImage.wf (fun N => (inr N.2, N.1)) (WellFounded.transGen (constrains_wf α γ))) N _
  clear N
  rintro ⟨B, N⟩ ih ⟨c, hc₁, hc₂⟩
  dsimp only at *
  have hdom : ((((constrainedAction π s hs).comp A B).refine (hπ B)).litterMap N.fst).Dom :=
    ⟨c, hc₁, reflTransGen_nearLitter hc₂⟩
  suffices completeLitterMap π (A.comp B) N.fst =
      StructPerm.derivative B (Allowable.toStructPerm ρ) • N.fst by
    refine' SetLike.coe_injective _
    refine'
      Eq.trans _
        (NearLitterAction.smul_nearLitter_eq_of_preciseAt _ (h B) hdom
            (NearLitterAction.refine_precise _) this.symm).symm
    rw [completeNearLitterMap_eq' (A.comp B) N]
    simp only [StructAction.refine_apply, StructAction.refine_litterMap,
      foaHypothesis_nearLitterImage, StructPerm.ofBot_smul]
    simp only [StructAction.comp_apply, constrainedAction_litterMap, symmDiff_right_inj]
    ext a : 1
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine' ⟨a, ha, _⟩
      refine' ((h B).map_atom a _).symm.trans _
      · refine' Or.inl (Or.inl (Or.inl (Or.inl _)))
        exact ⟨c, hc₁, Relation.ReflTransGen.head (Constrains.symmDiff N a ha _) hc₂⟩
      · rw [StructAction.rc_smul_atom_eq]
        rfl
        exact ⟨c, hc₁, Relation.ReflTransGen.head (Constrains.symmDiff N a ha _) hc₂⟩
    · rintro ⟨a, ha, rfl⟩
      refine' ⟨a, ha, _⟩
      refine' Eq.trans _ ((h B).map_atom a _)
      · rw [StructAction.rc_smul_atom_eq]
        rfl
        exact ⟨c, hc₁, Relation.ReflTransGen.head (Constrains.symmDiff N a ha _) hc₂⟩
      · refine' Or.inl (Or.inl (Or.inl (Or.inl _)))
        exact ⟨c, hc₁, Relation.ReflTransGen.head (Constrains.symmDiff N a ha _) hc₂⟩
  have hc₂' := reflTransGen_nearLitter hc₂
  generalize hNL : N.fst = L
  rw [hNL] at hdom hc₂'
  obtain hL | ⟨⟨hL⟩⟩ | ⟨⟨hL⟩⟩ := flexible_cases' (γ : Iic α) L B
  · refine' Eq.trans _ ((h B).map_litter L _)
    · rw [StructAction.rc_smul_litter_eq]
      rw [NearLitterAction.flexibleLitterPerm_apply_eq]
      swap; exact hdom
      swap; exact hL
      exact (NearLitterAction.roughLitterMapOrElse_of_dom _ hdom).symm
    · refine' Or.inl (Or.inl _)
      refine' ⟨hdom, hL⟩
  · rw [completeLitterMap_eq_of_inflexibleBot (hL.comp A)]
    obtain ⟨δ, ε, hε, C, a, rfl, rfl⟩ := hL
    rw [StructPerm.derivative_cons]
    refine' Eq.trans _ (StructPerm.derivative_bot_smul _ _).symm
    rw [StructPerm.derivative_cons]
    rw [Allowable.derivative_toStructPerm (show Path ((γ : IicBot α) : TypeIndex) (δ : IicBot α) from C)]
    refine'
      Eq.trans _
        (toStructPerm_smul_fMap (δ : IicBot α) ⊥ ε (bot_lt_coe _) _ _
            (Allowable.derivative (show Path ((γ : IicBot α) : TypeIndex) (δ : IicBot α) from C) ρ) a).symm
    swap
    · intro h
      cases h
    refine' congr_arg _ _
    rw [← Allowable.derivative_cons_apply]
    refine'
      Eq.trans _
        (((h <| C.cons (bot_lt_coe _)).map_atom a
              (Or.inl
                (Or.inl
                  (Or.inl
                    (Or.inl
                      ⟨c, hc₁,
                        Relation.ReflTransGen.head (Constrains.fMap_bot hε _ _) hc₂'⟩))))).trans
          _)
    · rw [StructAction.rc_smul_atom_eq]
      rfl
      exact ⟨c, hc₁, Relation.ReflTransGen.head (Constrains.fMap_bot hε _ _) hc₂'⟩
    · have :=
        Allowable.toStructPerm_smul
          (Allowable.derivative
            (show Path ((γ : IicBot α) : TypeIndex) (⊥ : IicBot α) from C.cons (bot_lt_coe _)) ρ)
          a
      rw [← Allowable.derivative_toStructPerm] at this
      exact this
  · rw [completeLitterMap_eq_of_inflexibleCoe (hL.comp A)]
    swap
    · rw [InflexibleCoe.comp_B, ← Path.comp_cons, ← StructAction.comp_comp]
      refine' StructAction.Lawful.comp _ _
      refine' hπ.le (StructAction.le_comp (ihAction_le_constrainedAction _ _) _)
      exact ⟨c, hc₁, hc₂'⟩
    swap
    · rw [InflexibleCoe.comp_B, ← Path.comp_cons]
      exact ihAction_comp_mapFlexible hπf _ _
    obtain ⟨δ, ε, ζ, hε, hζ, hεζ, C, t, rfl, rfl⟩ := hL
    generalize_proofs -- Massively speeds up rewrites and simplifications.
    rw [StructPerm.derivative_cons]
    refine' Eq.trans _ (StructPerm.derivative_bot_smul _ _).symm
    rw [StructPerm.derivative_cons]
    rw [Allowable.derivative_toStructPerm (show Path ((γ : IicBot α) : TypeIndex) (δ : IicBot α) from C)]
    refine'
      Eq.trans _
        (toStructPerm_smul_fMap (δ : IicBot α) ε ζ (coe_lt hε) _ _
            (Allowable.derivative (show Path ((γ : IicBot α) : TypeIndex) (δ : IicBot α) from C) ρ) t).symm
    swap
    · intro h
      refine' hεζ (Subtype.ext _)
      have := congr_arg Subtype.val h
      exact coe_injective this
    refine' congr_arg _ _
    simp only [ne_eq, Path.comp_cons, InflexibleCoe.comp_δ, InflexibleCoe.comp_t]
    rw [← Allowable.derivative_cons_apply, ← inv_smul_eq_iff, smul_smul]
    refine' (designatedSupport t).supports _ _
    intro c hct
    rw [mul_smul, inv_smul_eq_iff]
    obtain ⟨a | M, D⟩ := c
    · refine' Prod.ext _ rfl
      change inl _ = inl _
      simp only [inl.injEq]
      rw [← Allowable.derivative_toStructPerm
          (show Path ((γ : IicBot α) : TypeIndex) (ε : IicBot α) from _),
        StructPerm.derivative_derivative]
      refine' Eq.trans _ ((h _).map_atom a _)
      refine'
        (((ihAction _).hypothesisedAllowable_exactlyApproximates
                    ⟨δ, ε, ζ, hε, hζ, hεζ, A.comp C, t, rfl, rfl⟩ _ _ D).map_atom
                a _).symm.trans
          _
      · refine' Or.inl (Or.inl (Or.inl (Or.inl _)))
        exact Relation.TransGen.single (Constrains.fMap hε hζ hεζ _ _ _ hct)
      · rw [StructAction.rc_smul_atom_eq, StructAction.rc_smul_atom_eq]
        · simp only [StructAction.comp_apply, ihAction_atomMap, foaHypothesis_atomImage,
            constrainedAction_atomMap]
          simp_rw [← Path.comp_cons]
          rw [Path.comp_assoc]
        · refine' ⟨c, hc₁, Relation.ReflTransGen.head _ hc₂'⟩
          exact constrains_comp (Constrains.fMap hε hζ hεζ _ _ _ hct) A
        · simp only [StructAction.comp_apply, ihAction_atomMap]
          simp_rw [← Path.comp_cons]
          rw [Path.comp_assoc]
          exact Relation.TransGen.single (constrains_comp (Constrains.fMap hε hζ hεζ _ _ _ hct) A)
      · refine' Or.inl (Or.inl (Or.inl (Or.inl _)))
        refine' ⟨c, hc₁, Relation.ReflTransGen.head _ hc₂'⟩
        exact constrains_comp (Constrains.fMap hε hζ hεζ _ _ _ hct) A
    · refine' Prod.ext _ rfl
      change inr _ = inr _
      simp only [inr.injEq]
      refine' Biexact.smul_eq_smul_nearLitter _
      constructor
      · intro E a ha
        have haN :
          (inl a, (C.cons <| coe_lt hε).comp E) <[α]
            (inr N.fst.toNearLitter, (C.cons <| coe_lt hζ).cons (bot_lt_coe _))
        · simp only [hNL]
          refine' Relation.TransGen.tail' _ (Constrains.fMap hε hζ hεζ _ _ _ hct)
          exact reflTransGen_constrains_comp ha _
        refine'
          ((StructAction.hypothesisedAllowable_exactlyApproximates _
                      ⟨δ, ε, ζ, hε, hζ, hεζ, A.comp C, t, rfl, rfl⟩ _ _ _).map_atom
                  _ _).symm.trans
            _
        · refine' Or.inl (Or.inl (Or.inl (Or.inl _)))
          change _ <[α] _
          simp only [← hNL, Path.comp_assoc, ← Path.comp_cons]
          exact transGen_constrains_comp haN _
        have := (h ?_).map_atom a ?_
        rw [StructAction.rc_smul_atom_eq] at this ⊢
        swap
        · change _ <[α] _
          simp only [← hNL, Path.comp_assoc, ← Path.comp_cons]
          exact transGen_constrains_comp haN _
        swap
        · refine' ⟨c, hc₁, _root_.trans _ hc₂⟩
          swap
          refine' Relation.ReflTransGen.trans (transGen_constrains_comp haN _).to_reflTransGen _
          exact reflTransGen_nearLitter Relation.ReflTransGen.refl
        · simp only [StructAction.comp_apply, ihAction_atomMap, foaHypothesis_atomImage,
            constrainedAction_atomMap, StructPerm.ofBot_smul] at this ⊢
          rw [← Allowable.derivative_toStructPerm
              (show Path ((γ : IicBot α) : TypeIndex) (ε : IicBot α) from _),
            StructPerm.derivative_derivative, ← this,
            ← Path.comp_assoc, Path.comp_cons]
        · refine' Or.inl (Or.inl (Or.inl (Or.inl _)))
          refine' ⟨c, hc₁, _root_.trans _ hc₂⟩
          simp only [← hNL, Path.comp_assoc, ← Path.comp_cons]
          exact reflTransGen_constrains_comp (transGen_nearLitter haN).to_reflTransGen _
      · intro E L hL₁ hL₂
        rw [← StructPerm.ofBot_smul]
        refine'
          ((StructAction.hypothesisedAllowable_exactlyApproximates _
                      ⟨δ, ε, ζ, hε, hζ, hεζ, A.comp C, t, rfl, rfl⟩ _ _ _).map_litter
                  _ _).symm.trans
            _
        · refine' Or.inl (Or.inl ⟨_, hL₂⟩)
          refine' Relation.TransGen.trans_right (reflTransGen_constrains_comp hL₁ _) _
          exact Relation.TransGen.single (Constrains.fMap hε hζ hεζ _ _ _ hct)
        have hLN :
          (inr L.toNearLitter, (C.cons <| coe_lt hε).comp E) <[α]
            (inr N.fst.toNearLitter, (C.cons <| coe_lt hζ).cons (bot_lt_coe _))
        · simp only [hNL]
          refine' Relation.TransGen.tail' _ (Constrains.fMap hε hζ hεζ _ _ _ hct)
          exact reflTransGen_constrains_comp hL₁ _
        rw [StructAction.rc_smul_litter_eq, NearLitterAction.flexibleLitterPerm_apply_eq,
          NearLitterAction.roughLitterMapOrElse_of_dom]
        simp only [StructAction.comp_apply, StructAction.refine_apply,
          NearLitterAction.refine_litterMap, ihAction_litterMap,
          foaHypothesis_nearLitterImage]
        specialize
          ih ((C.cons <| coe_lt hε).comp E, L.toNearLitter) (transGen_nearLitter hLN)
            ⟨c, hc₁,
              _root_.trans (transGen_constrains_comp (transGen_nearLitter hLN) _).to_reflTransGen hc₂⟩
        · dsimp only at ih
          rw [← Path.comp_assoc, Path.comp_cons] at ih
          rw [ih]
          simp only [StructPerm.derivative_fst, Litter.toNearLitter_fst]
          rw [← Allowable.derivative_toStructPerm
              (show Path ((γ : IicBot α) : TypeIndex) (ε : IicBot α) from _),
            StructPerm.derivative_derivative]
        · refine' transGen_nearLitter _
          simp only [← hNL, Path.comp_assoc, ← Path.comp_cons]
          exact transGen_constrains_comp hLN _
        · refine' transGen_nearLitter _
          simp only [← hNL, Path.comp_assoc, ← Path.comp_cons]
          exact transGen_constrains_comp hLN _
        · exact hL₂
      · intro E L hL₁ hL₂
        have hLN :
          (inr L.toNearLitter, (C.cons <| coe_lt hε).comp E) <[α]
            (inr N.fst.toNearLitter, (C.cons <| coe_lt hζ).cons (bot_lt_coe _))
        · simp only [hNL]
          refine' Relation.TransGen.tail' _ (Constrains.fMap hε hζ hεζ _ _ _ hct)
          exact reflTransGen_constrains_comp hL₁ _
        specialize
          ih ((C.cons <| coe_lt hε).comp E, L.toNearLitter) (transGen_nearLitter hLN)
            ⟨c, hc₁,
              _root_.trans (transGen_constrains_comp (transGen_nearLitter hLN) _).to_reflTransGen hc₂⟩
        simp only at ih
        rw [← Path.comp_assoc, Path.comp_cons] at ih
        refine'
          (NearLitterAction.smul_toNearLitter_eq_of_preciseAt _
                (StructAction.hypothesisedAllowable_exactlyApproximates (ihAction _)
                  ⟨δ, ε, ζ, hε, hζ, hεζ, A.comp C, t, rfl, rfl⟩ _ _ _)
                _ (NearLitterAction.refine_precise _) _).trans
            _
        · refine' Relation.TransGen.tail' (reflTransGen_constrains_comp hL₁ _) _
          exact Constrains.fMap hε hζ hεζ _ _ _ hct
        · refine' hL₂.trans _
          simp only [StructAction.comp_apply, StructAction.refine_apply,
            NearLitterAction.refine_litterMap, ihAction_litterMap,
            foaHypothesis_nearLitterImage]
          rw [ih,
            ← Allowable.derivative_toStructPerm
              (show Path ((γ : IicBot α) : TypeIndex) (ε : IicBot α) from _),
            StructPerm.derivative_derivative]
          rfl
        · simp only [StructAction.comp_apply, StructAction.refine_apply,
            NearLitterAction.refine_litterMap, ihAction_litterMap,
            foaHypothesis_nearLitterImage]
          rw [ih,
            ← Allowable.derivative_toStructPerm
              (show Path ((γ : IicBot α) : TypeIndex) (ε : IicBot α) from _),
            StructPerm.derivative_derivative]

/-- **Coherence lemma**: The action of the complete litter map, below a given support condition `c`,
is equal to the action of any allowable permutation that exactly approximates it.
This condition can only be applied for `γ < α` as we're dealing with lower allowable permutations.
-/
theorem constrainedAction_coherent (hπf : π.Free) {γ : Iio α} (A : Path (β : TypeIndex) γ)
    (B : ExtendedIndex γ) (N : NearLitter) (s : Set (SupportCondition β)) (hs : Small s)
    (hc : ∃ c : SupportCondition β, c ∈ s ∧ (inr N, A.comp B) ≤[α] c)
    (hπ : ((constrainedAction π s hs).comp A).Lawful) (ρ : Allowable γ)
    (h : (((constrainedAction π s hs).comp A).rc hπ).ExactlyApproximates
      (Allowable.toStructPerm ρ)) :
    completeNearLitterMap π (A.comp B) N = StructPerm.derivative B (Allowable.toStructPerm ρ) • N :=
  constrainedAction_coherent' hπf A (B, N) s hs hc hπ ρ h

/-- The coherence lemma for atoms, which is much easier to prove.
The statement is here for symmetry.
-/
theorem constrainedAction_coherent_atom {γ : Iio α}
    (A : Path (β : TypeIndex) γ) (B : ExtendedIndex γ) (a : Atom) (s : Set (SupportCondition β))
    (hs : Small s) (hc : ∃ c : SupportCondition β, c ∈ s ∧ (inl a, A.comp B) ≤[α] c)
    (hπ : ((constrainedAction π s hs).comp A).Lawful) (ρ : Allowable γ)
    (h : (((constrainedAction π s hs).comp A).rc hπ).ExactlyApproximates
      (Allowable.toStructPerm ρ)) :
    completeAtomMap π (A.comp B) a = StructPerm.derivative B (Allowable.toStructPerm ρ) • a := by
  refine' Eq.trans _ ((h B).map_atom a (Or.inl (Or.inl (Or.inl (Or.inl hc)))))
  rw [StructAction.rc_smul_atom_eq]
  rfl
  exact hc

theorem ihsAction_coherent (hπf : π.Free) {γ : Iio α} (A : Path (β : TypeIndex) γ)
    (B : ExtendedIndex γ) (N : NearLitter) (c d : SupportCondition β)
    (hc : (inr N, A.comp B) ∈ transConstrained c d) (hπ : ((ihsAction π c d).comp A).Lawful)
    (ρ : Allowable γ) (h : (((ihsAction π c d).comp A).rc hπ).ExactlyApproximates
      (Allowable.toStructPerm ρ)) :
    completeNearLitterMap π (A.comp B) N =
    StructPerm.derivative B (Allowable.toStructPerm ρ) • N := by
  simp_rw [ihsAction_eq_constrainedAction] at hπ
  refine constrainedAction_coherent hπf A B N _ _ ?_ hπ ρ ?_
  obtain hc | hc := hc
  · simp only [Relation.TransGen.tail'_iff] at hc
    obtain ⟨d, hd₁, hd₂⟩ := hc
    exact ⟨d, Or.inl hd₂, hd₁⟩
  · simp only [Relation.TransGen.tail'_iff] at hc
    obtain ⟨d, hd₁, hd₂⟩ := hc
    exact ⟨d, Or.inr hd₂, hd₁⟩
  · convert h
    rw [ihsAction_eq_constrainedAction]

theorem ihsAction_coherent_atom {γ : Iio α} (A : Path (β : TypeIndex) γ)
    (B : ExtendedIndex γ) (a : Atom) (c d : SupportCondition β) (hc : (inl a, A.comp B) <[α] c)
    (hπ : ((ihsAction π c d).comp A).Lawful) (ρ : Allowable γ)
    (h : (((ihsAction π c d).comp A).rc hπ).ExactlyApproximates (Allowable.toStructPerm ρ)) :
    completeAtomMap π (A.comp B) a = StructPerm.derivative B (Allowable.toStructPerm ρ) • a := by
  refine' Eq.trans _ ((h B).map_atom a (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hc))))))
  rw [StructAction.rc_smul_atom_eq]
  rfl
  exact Or.inl hc

theorem ihAction_coherent (hπf : π.Free) {γ : Iio α} (A : Path (β : TypeIndex) γ)
    (B : ExtendedIndex γ) (N : NearLitter) (c : SupportCondition β) (hc : (inr N, A.comp B) <[α] c)
    (hπ : ((ihAction (π.foaHypothesis : Hypothesis c)).comp A).Lawful) (ρ : Allowable γ)
    (h : (((ihAction (π.foaHypothesis : Hypothesis c)).comp A).rc hπ).ExactlyApproximates
        (Allowable.toStructPerm ρ)) :
    completeNearLitterMap π (A.comp B) N =
    StructPerm.derivative B (Allowable.toStructPerm ρ) • N := by
  refine' ihsAction_coherent hπf A B N c c (Or.inl hc) _ ρ _
  · rw [ihsAction_self]
    exact hπ
  · convert h
    rw [ihsAction_self]

theorem ihAction_coherent_atom {γ : Iio α} (A : Path (β : TypeIndex) γ)
    (B : ExtendedIndex γ) (a : Atom) (c : SupportCondition β) (hc : (inl a, A.comp B) <[α] c)
    (hπ : ((ihAction (π.foaHypothesis : Hypothesis c)).comp A).Lawful) (ρ : Allowable γ)
    (h :
      (((ihAction (π.foaHypothesis : Hypothesis c)).comp A).rc hπ).ExactlyApproximates
        (Allowable.toStructPerm ρ)) :
    completeAtomMap π (A.comp B) a = StructPerm.derivative B (Allowable.toStructPerm ρ) • a := by
  refine' ihsAction_coherent_atom A B a c c hc _ ρ _
  · rw [ihsAction_self]
    exact hπ
  · convert h
    rw [ihsAction_self]

theorem ihAction_smul_tangle' (hπf : π.Free) (c d : SupportCondition β) (A : ExtendedIndex β)
    (L : Litter) (hL₁ : (inr L.toNearLitter, A) ≤[α] c) (hL₂ : InflexibleCoe L A) (hlaw₁ hlaw₂) :
    (ihAction (π.foaHypothesis : Hypothesis (inr L.toNearLitter, A))).hypothesisedAllowable hL₂
          hlaw₁ (ihAction_comp_mapFlexible hπf _ _) •
        hL₂.t =
      (ihsAction π c d).hypothesisedAllowable hL₂ hlaw₂ (ihsAction_comp_mapFlexible hπf _ _ _) •
        hL₂.t := by
  obtain ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ := hL₂
  rw [← inv_smul_eq_iff, smul_smul]
  refine' (designatedSupport t).supports _ _
  intro e he
  rw [mul_smul, inv_smul_eq_iff]
  change (_, e.2) = (_, e.2)
  refine' Prod.ext _ rfl
  obtain ⟨a | N, C⟩ := e
  · change inl _ = inl _
    simp only [inl.injEq]
    refine'
      Eq.trans _
        (ihsAction_coherent_atom _ _ a c d _ hlaw₂ _
          ((ihsAction π c d).hypothesisedAllowable_exactlyApproximates _ _ _))
    have := ihAction_coherent_atom (π := π) (B.cons ?_) C a
        (inr (Litter.toNearLitter (fMap (coe_ne_coe.mpr <| coe_ne' hδε) t)),
          Path.cons (Path.cons B (coe_lt hε)) (bot_lt_coe _))
        ?_ hlaw₁ _
        ((ihAction π.foaHypothesis).hypothesisedAllowable_exactlyApproximates
          ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ ?_ ?_)
    exact this.symm
    · exact Relation.TransGen.single (Constrains.fMap hδ hε hδε B t _ he)
    · exact Relation.TransGen.head' (Constrains.fMap hδ hε hδε B t _ he) hL₁
  · change inr _ = inr _
    simp only [inr.injEq]
    refine'
      Eq.trans _
        (ihsAction_coherent hπf _ _ N c d _ hlaw₂ _
          ((ihsAction π c d).hypothesisedAllowable_exactlyApproximates _ _ _))
    have := ihAction_coherent hπf (B.cons ?_) C N
        (inr (Litter.toNearLitter (fMap (coe_ne_coe.mpr <| coe_ne' hδε) t)),
          Path.cons (Path.cons B (coe_lt hε)) (bot_lt_coe _))
        ?_ hlaw₁ _
        ((ihAction π.foaHypothesis).hypothesisedAllowable_exactlyApproximates
          ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ ?_ ?_)
    exact this.symm
    · exact Relation.TransGen.single (Constrains.fMap hδ hε hδε B t _ he)
    · exact Or.inl (Relation.TransGen.head' (Constrains.fMap hδ hε hδε B t _ he) hL₁)

theorem ihAction_smul_tangle (hπf : π.Free) (c d : SupportCondition β) (A : ExtendedIndex β)
    (L : Litter) (hL₁ : (inr L.toNearLitter, A) ∈ reflTransConstrained c d)
    (hL₂ : InflexibleCoe L A) (hlaw₁ hlaw₂) :
    (ihAction (π.foaHypothesis : Hypothesis (inr L.toNearLitter, A))).hypothesisedAllowable hL₂
          hlaw₁ (ihAction_comp_mapFlexible hπf _ _) •
        hL₂.t =
      (ihsAction π c d).hypothesisedAllowable hL₂ hlaw₂ (ihsAction_comp_mapFlexible hπf _ _ _) •
        hL₂.t := by
  obtain hL₁ | hL₁ := hL₁
  · exact ihAction_smul_tangle' hπf c d A L hL₁ hL₂ hlaw₁ hlaw₂
  · have := ihAction_smul_tangle' hπf d c A L hL₁ hL₂ hlaw₁ ?_
    · simp_rw [ihsAction_symm] at this
      exact this
    · rw [ihsAction_symm]
      exact hlaw₂

theorem litter_injective_extends (hπf : π.Free) {c d : SupportCondition β}
    (hcd : (ihsAction π c d).Lawful) {A : ExtendedIndex β} {L₁ L₂ : Litter}
    (h₁ : (inr L₁.toNearLitter, A) ∈ reflTransConstrained c d)
    (h₂ : (inr L₂.toNearLitter, A) ∈ reflTransConstrained c d)
    (h : completeLitterMap π A L₁ = completeLitterMap π A L₂) : L₁ = L₂ := by
  obtain h₁' | h₁' | h₁' := flexible_cases' β L₁ A
  · have h₂' : Flexible α L₂ A
    · have := completeLitterMap_flexible hπf h₁'
      rw [h] at this
      exact completeLitterMap_flexible' hπf hcd h₂ this
    rw [completeLitterMap_eq_of_flexible h₁', completeLitterMap_eq_of_flexible h₂'] at h
    refine' LocalPerm.injOn _ _ _ h
    all_goals
      rw [NearLitterApprox.flexibleCompletion_litterPerm_domain_free _ _ _ (hπf A)]
      assumption
  · obtain ⟨h₁'⟩ := h₁'
    have h₂' : InflexibleBot L₂ A
    · have := completeLitterMap_inflexibleBot (π := π) h₁'
      rw [h] at this
      exact completeLitterMap_inflexibleBot' hπf hcd h₂ this
    rw [completeLitterMap_eq_of_inflexibleBot h₁',
      completeLitterMap_eq_of_inflexibleBot h₂'] at h
    obtain ⟨γ₁, ε₁, hγε₁, B₁, a₁, rfl, rfl⟩ := h₁'
    obtain ⟨γ₂, ε₂, hγε₂, B₂, a₂, rfl, hB⟩ := h₂'
    cases Subtype.coe_injective (coe_injective (Path.obj_eq_of_cons_eq_cons hB))
    cases Subtype.coe_injective
      (coe_injective (Path.obj_eq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hB).eq))
    cases (Path.heq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hB).eq).eq
    refine' congr_arg _ ((hcd _).atomMap_injective _ _ (fMap_injective bot_ne_coe h))
    · have := Constrains.fMap_bot hγε₁ B₁ a₁
      exact transConstrained_of_reflTransConstrained_of_trans_constrains h₁
        (Relation.TransGen.single this)
    · have := Constrains.fMap_bot hγε₁ B₁ a₂
      exact transConstrained_of_reflTransConstrained_of_trans_constrains h₂
        (Relation.TransGen.single this)
  · obtain ⟨h₁'⟩ := h₁'
    have h₂' : InflexibleCoe L₂ A
    · have := completeLitterMap_inflexibleCoe hπf hcd h₁' h₁
      rw [h] at this
      exact completeLitterMap_inflexibleCoe' hπf this
    rw [completeLitterMap_eq_of_inflexibleCoe h₁'] at h
    swap
    · refine' (hcd.le _).comp _
      obtain h₁ | h₁ := h₁
      · exact (ihAction_le h₁).trans (ihAction_le_ihsAction _ _ _)
      · rw [ihsAction_symm]
        exact (ihAction_le h₁).trans (ihAction_le_ihsAction _ _ _)
    swap
    · exact ihAction_comp_mapFlexible hπf _ _
    rw [completeLitterMap_eq_of_inflexibleCoe h₂'] at h
    swap
    · refine' (hcd.le _).comp _
      obtain h₂ | h₂ := h₂
      · exact (ihAction_le h₂).trans (ihAction_le_ihsAction _ _ _)
      · rw [ihsAction_symm]
        exact (ihAction_le h₂).trans (ihAction_le_ihsAction _ _ _)
    swap
    · exact ihAction_comp_mapFlexible hπf _ _
    obtain ⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₁, rfl, rfl⟩ := h₁'
    obtain ⟨γ₂, δ₂, ε₂, hδ₂, hε₂, hδε₂, B₂, t₂, rfl, hB⟩ := h₂'
    cases Subtype.coe_injective (coe_injective (Path.obj_eq_of_cons_eq_cons hB))
    cases Subtype.coe_injective
      (coe_injective (Path.obj_eq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hB).eq))
    cases (Path.heq_of_cons_eq_cons (Path.heq_of_cons_eq_cons hB).eq).eq
    have := congr_arg Litter.β h
    cases Subtype.coe_injective (coe_injective this)
    clear this
    refine' congr_arg _ _
    have h' := fMap_injective _ h
    rw [ihAction_smul_tangle hπf c d _ _ h₁ _ _ (hcd.comp _)] at h'
    rw [ihAction_smul_tangle hπf c d _ _ h₂ _ _ (hcd.comp _)] at h'
    rw [StructAction.hypothesisedAllowable_eq t₁ t₂ rfl (hcd.comp _)
        (ihsAction_comp_mapFlexible hπf _ _ _)] at h'
    rw [smul_left_cancel_iff] at h'
    exact h'

/-- **Split relation**
Let `<` denote a relation on `α`.
The split relation `<ₛ` defined on `α × α` is defined by:

* `a < b → (a, c) <ₛ (b, c)` (left `<`)
* `b < c → (a, b) <ₛ (a, c)` (right `<`)
* `a < c → b < c → (a, b) <ₛ (c, d)` (left split)
* `a < d → b < d → (a, b) <ₛ (c, d)` (right split)

This is more granular than the standard product of relations,
which would be given by just the first two constructors.
The splitting constructors allow one to "split" either `c` or `d` into two lower values `a` and `b`.

Splitting has applications with well-founded relations; in particular, `<ₛ` is well-founded whenever
`<` is, so this relation can simplify certain inductive steps.
-/
inductive SplitLt {α : Type _} (r : α → α → Prop) : α × α → α × α → Prop
  | left_lt ⦃a b c : α⦄ : r a b → SplitLt r (a, c) (b, c)
  | right_lt ⦃a b c : α⦄ : r b c → SplitLt r (a, b) (a, c)
  | left_split ⦃a b c d : α⦄ : r a c → r b c → SplitLt r (a, b) (c, d)
  | right_split ⦃a b c d : α⦄ : r a d → r b d → SplitLt r (a, b) (c, d)

theorem le_wellOrderExtension_lt {α : Type _} {r : α → α → Prop} (hr : WellFounded r) :
    r ≤ hr.wellOrderExtension.lt := fun _ _ h => Prod.Lex.left _ _ (hr.rank_lt_of_rel h)

theorem lex_lt_of_splitLt {α : Type _} {r : α → α → Prop} (hr : WellFounded r) :
    SplitLt r ≤
      InvImage (Prod.Lex hr.wellOrderExtension.lt hr.wellOrderExtension.lt) fun a =>
        if hr.wellOrderExtension.lt a.1 a.2 then (a.2, a.1) else (a.1, a.2) := by
  intro a b h
  induction' h with a b c h a b c h a b c d ha hb a b c d ha hb
  · change Prod.Lex _ _ _ _
    simp only
    split_ifs with h₁ h₂ h₂
    · exact Prod.Lex.right _ (le_wellOrderExtension_lt hr _ _ h)
    · by_cases hcb : c = b
      · cases hcb
        exact Prod.Lex.right _ h₁
      · refine' Prod.Lex.left _ _ _
        have := (@not_lt _ hr.wellOrderExtension _ _).mp h₂
        exact @lt_of_le_of_ne _ hr.wellOrderExtension.toPartialOrder _ _ this hcb
    · cases h₁ (@lt_trans _ hr.wellOrderExtension.toPartialOrder.toPreorder _ _ _
        (le_wellOrderExtension_lt hr _ _ h) h₂)
    · exact Prod.Lex.left _ _ (le_wellOrderExtension_lt hr _ _ h)
  · change Prod.Lex _ _ _ _
    simp only
    split_ifs with h₁ h₂ h₂
    · exact Prod.Lex.left _ _ (le_wellOrderExtension_lt hr _ _ h)
    · cases h₂ (@lt_trans _ hr.wellOrderExtension.toPartialOrder.toPreorder _ _ _
        h₁ (le_wellOrderExtension_lt hr _ _ h))
    · exact Prod.Lex.left _ _ h₂
    · exact Prod.Lex.right _ (le_wellOrderExtension_lt hr _ _ h)
  · change Prod.Lex _ _ _ _
    simp only
    split_ifs with h₁ h₂ h₂
    · exact Prod.Lex.left _ _ (@lt_trans _ hr.wellOrderExtension.toPartialOrder.toPreorder _ _ _
        (le_wellOrderExtension_lt hr _ _ hb) h₂)
    · exact Prod.Lex.left _ _ (le_wellOrderExtension_lt hr _ _ hb)
    · exact Prod.Lex.left _ _ (@lt_trans _ hr.wellOrderExtension.toPartialOrder.toPreorder _ _ _
        (le_wellOrderExtension_lt hr _ _ ha)  h₂)
    · exact Prod.Lex.left _ _ (le_wellOrderExtension_lt hr _ _ ha)
  · change Prod.Lex _ _ _ _
    simp only
    split_ifs with h₁ h₂ h₂
    · exact Prod.Lex.left _ _ (le_wellOrderExtension_lt hr _ _ hb)
    · by_cases hcb : c = b
      · cases hcb
        exact Prod.Lex.right _ (le_wellOrderExtension_lt hr _ _ ha)
      · refine' Prod.Lex.left _ _ _
        have := (@not_lt _ hr.wellOrderExtension _ _).mp h₂
        exact
          @lt_of_lt_of_le _
            hr.wellOrderExtension.toPartialOrder.toPreorder _ _
            _ (le_wellOrderExtension_lt hr _ _ hb) this
    · exact Prod.Lex.left _ _ (le_wellOrderExtension_lt hr _ _ ha)
    · have := (@not_lt _ hr.wellOrderExtension _ _).mp h₂
      have :=
        @lt_of_lt_of_le _
          hr.wellOrderExtension.toPartialOrder.toPreorder _ _ _
          (le_wellOrderExtension_lt hr _ _ ha) this
      exact Prod.Lex.left _ _ this

theorem splitLt_wellFounded {α : Type _} {r : α → α → Prop} (hr : WellFounded r) :
    WellFounded (SplitLt r) := by
  refine' Subrelation.wf @(lex_lt_of_splitLt hr) _
  refine' InvImage.wf _ (InvImage.wf _ _)
  refine' WellFounded.prod_lex _ _ <;>
    exact (WellFounded.wellOrderExtension.isWellFounded_lt hr).wf

-- TODO: Clean this up. Proof comes from an old lemma.
theorem completeAtomMap_mem_completeNearLitterMap_toNearLitter' (hπf : π.Free)
    {c d : SupportCondition β} (hcd : (ihsAction π c d).Lawful) {A : ExtendedIndex β} {a : Atom}
    {L : Litter} (ha : a.1 = L) (hL : (inr L.toNearLitter, A) ∈ reflTransConstrained c d) :
    π.completeAtomMap A a ∈ π.completeNearLitterMap A L.toNearLitter := by
  subst ha
  rw [completeNearLitterMap_eq]
  by_cases ha : a ∈ (π A).atomPerm.domain
  · rw [completeAtomMap_eq_of_mem_domain ha]
    refine' Or.inl ⟨Or.inr ⟨a, ⟨rfl, ha⟩, rfl⟩, _⟩
    rintro ⟨_, ⟨b, rfl⟩, _, ⟨hb, rfl⟩, hab⟩
    simp only [foaHypothesis_atomImage, mem_singleton_iff] at hab
    rw [completeAtomMap_eq_of_not_mem_domain hb.2] at hab
    have := Sublitter.equiv_apply_mem (S := (π A).largestSublitter b.fst)
      (T := (π A).largestSublitter (completeLitterMap π A b.fst)) ⟨b, rfl, hb.2⟩
    rw [← hab] at this
    exact this.2 ((π A).atomPerm.map_domain ha)
  rw [completeAtomMap_eq_of_not_mem_domain ha]
  refine' Or.inl ⟨Or.inl _, _⟩
  · rw [SetLike.mem_coe]
    convert Sublitter.equiv_apply_mem _ using 1
    rw [nearLitterHypothesis_eq, completeLitterMap_eq]
    rfl
  · rintro ⟨_, ⟨b, rfl⟩, _, ⟨hb, rfl⟩, hab⟩
    simp only [foaHypothesis_atomImage, mem_singleton_iff] at hab
    rw [completeAtomMap_eq_of_not_mem_domain hb.2] at hab
    have := litter_injective_extends hπf hcd hL
      (fst_mem_reflTransConstrained_of_mem_symmDiff hb.1 hL) ?_
    · rw [Sublitter.equiv_congr_left (congr_arg _ this) _,
        Sublitter.equiv_congr_right (congr_arg _ (congr_arg₂ _ rfl this)) _,
        Subtype.coe_inj, EquivLike.apply_eq_iff_eq] at hab
      cases hab
      exact hb.1.elim (fun h' => h'.2 rfl) fun h' => h'.2 rfl
    exact equiv_apply_eq hab

theorem ihsAction_lawful_extends (hπf : π.Free) (c d : SupportCondition β)
    (hπ : ∀ e f, SplitLt (fun c d => c <[α] d) (e, f) (c, d) → (ihsAction π e f).Lawful) :
    (ihsAction π c d).Lawful := by
  intro A
  have litter_map_injective :
    ∀ ⦃L₁ L₂ : Litter⦄,
      (inr L₁.toNearLitter, A) ∈ transConstrained c d →
      (inr L₂.toNearLitter, A) ∈ transConstrained c d →
      ((π.completeNearLitterMap A L₁.toNearLitter : Set Atom) ∩
        (π.completeNearLitterMap A L₂.toNearLitter : Set Atom)).Nonempty →
      L₁ = L₂ := by
    intro L₁ L₂ h₁ h₂ h₁₂
    have := eq_of_completeLitterMap_inter_nonempty h₁₂
    obtain h₁ | h₁ := h₁ <;> obtain h₂ | h₂ := h₂
    · specialize hπ (inr L₁.toNearLitter, A) (inr L₂.toNearLitter, A) (SplitLt.left_split h₁ h₂)
      exact litter_injective_extends hπf hπ (Or.inl Relation.ReflTransGen.refl)
        (Or.inr Relation.ReflTransGen.refl) this
    · specialize hπ (inr L₁.toNearLitter, A) d (SplitLt.left_lt h₁)
      exact litter_injective_extends hπf hπ
        (Or.inl Relation.ReflTransGen.refl) (Or.inr h₂.to_reflTransGen) this
    · specialize hπ c (inr L₁.toNearLitter, A) (SplitLt.right_lt h₁)
      exact litter_injective_extends hπf hπ
        (Or.inr Relation.ReflTransGen.refl) (Or.inl h₂.to_reflTransGen) this
    · specialize hπ (inr L₁.toNearLitter, A) (inr L₂.toNearLitter, A) (SplitLt.right_split h₁ h₂)
      exact litter_injective_extends hπf hπ (Or.inl Relation.ReflTransGen.refl)
        (Or.inr Relation.ReflTransGen.refl) this
  constructor
  · intro a b ha hb hab
    simp only [ihsAction_atomMap] at ha hb hab
    obtain ha | ha := ha <;> obtain hb | hb := hb
    · specialize hπ (inl a, A) (inl b, A) (SplitLt.left_split ha hb)
      exact atom_injective_extends hπ (Or.inl Relation.ReflTransGen.refl)
        (Or.inr Relation.ReflTransGen.refl) hab
    · specialize hπ (inl a, A) d (SplitLt.left_lt ha)
      exact atom_injective_extends hπ
        (Or.inl Relation.ReflTransGen.refl) (Or.inr hb.to_reflTransGen) hab
    · specialize hπ c (inl a, A) (SplitLt.right_lt ha)
      exact atom_injective_extends hπ
        (Or.inr Relation.ReflTransGen.refl) (Or.inl hb.to_reflTransGen) hab
    · specialize hπ (inl a, A) (inl b, A) (SplitLt.right_split ha hb)
      exact atom_injective_extends hπ (Or.inl Relation.ReflTransGen.refl)
        (Or.inr Relation.ReflTransGen.refl) hab
  · exact litter_map_injective
  · intro a ha L hL
    simp only [ihsAction_atomMap, ihsAction_litterMap]
    have : π.completeAtomMap A a ∈ π.completeNearLitterMap A a.fst.toNearLitter :=by
      obtain ha | ha := ha <;> obtain hL | hL := hL
      · specialize hπ (inl a, A) (inr L.toNearLitter, A) (SplitLt.left_split ha hL)
        exact completeAtomMap_mem_completeNearLitterMap_toNearLitter' hπf hπ rfl
          (fst_mem_refl_trans_constrained' (Or.inl Relation.ReflTransGen.refl))
      · specialize hπ (inl a, A) d (SplitLt.left_lt ha)
        exact completeAtomMap_mem_completeNearLitterMap_toNearLitter' hπf hπ rfl
          (fst_mem_refl_trans_constrained' (Or.inl Relation.ReflTransGen.refl))
      · specialize hπ c (inl a, A) (SplitLt.right_lt ha)
        exact completeAtomMap_mem_completeNearLitterMap_toNearLitter' hπf hπ rfl
          (fst_mem_refl_trans_constrained' (Or.inr Relation.ReflTransGen.refl))
      · specialize hπ (inl a, A) (inr L.toNearLitter, A) (SplitLt.right_split ha hL)
        exact
          completeAtomMap_mem_completeNearLitterMap_toNearLitter' hπf hπ rfl
            (fst_mem_refl_trans_constrained' (Or.inl Relation.ReflTransGen.refl))
    constructor
    · rintro rfl
      exact this
    · intro h
      exact litter_map_injective (fst_mem_trans_constrained' ha) hL ⟨_, this, h⟩

/-- Every `ihs_action` is lawful. This is a consequence of all of the previous lemmas. -/
theorem ihsAction_lawful (hπf : π.Free) (c d : SupportCondition β) : (ihsAction π c d).Lawful := by
  refine WellFounded.induction (C := fun c => (ihsAction π c.1 c.2).Lawful)
    (splitLt_wellFounded (trans_constrains_wf α β)) (c, d) ?_
  rintro ⟨c, d⟩ ih
  exact ihsAction_lawful_extends hπf c d fun e f hef => ih (e, f) hef

theorem ihAction_lawful (hπf : π.Free) (c : SupportCondition β) :
    (ihAction (π.foaHypothesis : Hypothesis c)).Lawful := by
  rw [← ihsAction_self]
  exact ihsAction_lawful hπf c c

/-!
We now establish a number of key consequences of `ihs_action_lawful`, such as injectivity.
-/

/-- The complete atom map is injective. -/
theorem completeAtomMap_injective (hπf : π.Free) (A : ExtendedIndex β) :
    Injective (π.completeAtomMap A) := fun a b =>
  atom_injective_extends (ihsAction_lawful hπf (inl a, A) (inl b, A))
    (Or.inl Relation.ReflTransGen.refl) (Or.inr Relation.ReflTransGen.refl)

/-- The complete litter map is injective. -/
theorem completeLitterMap_injective (hπf : π.Free) (A : ExtendedIndex β) :
    Injective (π.completeLitterMap A) := fun L₁ L₂ =>
  litter_injective_extends hπf
    (ihsAction_lawful hπf (inr L₁.toNearLitter, A) (inr L₂.toNearLitter, A))
    (Or.inl Relation.ReflTransGen.refl) (Or.inr Relation.ReflTransGen.refl)

/-- Atoms inside litters are mapped inside the corresponding image near-litter. -/
theorem completeAtomMap_mem_completeNearLitterMap_toNearLitter (hπf : π.Free) {A : ExtendedIndex β}
    {a : Atom} {L : Litter} :
    π.completeAtomMap A a ∈ π.completeNearLitterMap A L.toNearLitter ↔ a.1 = L := by
  have := completeAtomMap_mem_completeNearLitterMap_toNearLitter' hπf
    (ihsAction_lawful hπf (inl a, A) (inl a, A)) rfl
    (fst_mem_refl_trans_constrained' (Or.inl Relation.ReflTransGen.refl))
  constructor
  · intro h
    exact completeLitterMap_injective hπf _ (eq_of_completeLitterMap_inter_nonempty ⟨_, this, h⟩)
  · rintro rfl
    exact this

theorem mem_image_iff {α β : Type _} {f : α → β} (hf : Injective f) (x : α) (s : Set α) :
    f x ∈ f '' s ↔ x ∈ s :=
  Set.InjOn.mem_image_iff (hf.injOn Set.univ) (subset_univ _) (mem_univ _)

/-- Atoms inside near litters are mapped inside the corresponding image near-litter. -/
theorem completeAtomMap_mem_completeNearLitterMap (hπf : π.Free) {A : ExtendedIndex β} {a : Atom}
    {N : NearLitter} : π.completeAtomMap A a ∈ π.completeNearLitterMap A N ↔ a ∈ N := by
  rw [← SetLike.mem_coe, completeNearLitterMap_eq', Set.symmDiff_def]
  simp only [mem_union, mem_diff, SetLike.mem_coe, not_exists, not_and,
    symmDiff_symmDiff_cancel_left]
  rw [completeAtomMap_mem_completeNearLitterMap_toNearLitter hπf]
  rw [mem_image_iff (completeAtomMap_injective hπf A)]
  simp only [← mem_litterSet, ← mem_diff, ← mem_union]
  rw [← Set.symmDiff_def, symmDiff_symmDiff_cancel_left]
  rw [SetLike.mem_coe]

/-- The complete near-litter map is injective. -/
theorem completeNearLitterMap_injective (hπf : π.Free) (A : ExtendedIndex β) :
    Injective (π.completeNearLitterMap A) := by
  intro N₁ N₂ h
  rw [← SetLike.coe_set_eq, Set.ext_iff] at h ⊢
  intro a
  specialize h (π.completeAtomMap A a)
  simp only [SetLike.mem_coe, completeAtomMap_mem_completeNearLitterMap hπf] at h ⊢
  exact h

theorem completeNearLitterMap_subset_range (A : ExtendedIndex β) (L : Litter) :
    (π.completeNearLitterMap A L.toNearLitter : Set Atom) ⊆ range (π.completeAtomMap A) := by
  rw [completeNearLitterMap_toNearLitter_eq]
  rintro a (⟨ha₁, ha₂⟩ | ⟨a, ⟨_, ha₂⟩, rfl⟩)
  · refine' ⟨(((π A).largestSublitter L).equiv ((π A).largestSublitter a.1)).symm
      ⟨a, (π A).mem_largestSublitter_of_not_mem_domain a ha₂⟩, _⟩
    rw [completeAtomMap_eq_of_not_mem_domain]
    swap
    · exact NearLitterApprox.not_mem_domain_of_mem_largestSublitter _
        (Sublitter.equiv_symm_apply_mem ⟨a, _⟩)
    · rw [mem_litterSet] at ha₁
      have : ((((π A).largestSublitter L).equiv
        ((π A).largestSublitter a.fst)).symm ⟨a, rfl, ha₂⟩ : Atom).fst =
          L :=
        Sublitter.equiv_symm_apply_fst_eq ⟨a, _⟩
      rw [Sublitter.equiv_congr_left (congr_arg _ this),
        Sublitter.equiv_congr_right (congr_arg _ (congr_arg _ this)),
        Sublitter.equiv_congr_right (congr_arg _ ha₁.symm)]
      simp only [SetLike.eta, Equiv.apply_symm_apply]
  · refine' ⟨a, _⟩
    rw [completeAtomMap_eq_of_mem_domain ha₂]

theorem completeAtomMap_surjective_extends (A : ExtendedIndex β) (a : Atom)
    (h : a.1 ∈ range (π.completeLitterMap A)) : a ∈ range (π.completeAtomMap A) := by
  obtain ⟨L, hL⟩ := h
  by_cases ha : a ∈ (π A).atomPerm.domain
  · refine' ⟨(π A).atomPerm.symm a, _⟩
    rw [completeAtomMap_eq_of_mem_domain ((π A).atomPerm.symm.map_domain ha)]
    exact (π A).atomPerm.right_inv ha
  · have := completeNearLitterMap_toNearLitter_eq (π := π) A L
    rw [hL] at this
    have := Eq.subset this.symm (Or.inl ⟨rfl, ha⟩)
    exact completeNearLitterMap_subset_range A L this

noncomputable def completeSupportConditionMap (π : StructApprox β) :
    SupportCondition β → SupportCondition β
  | (inl a, B) => (inl (π.completeAtomMap B a), B)
  | (inr N, B) => (inr (π.completeNearLitterMap B N), B)

@[simp]
theorem completeSupportConditionMap_atom_eq {π : StructApprox β} {a : Atom} {B : ExtendedIndex β} :
    π.completeSupportConditionMap (inl a, B) = (inl (π.completeAtomMap B a), B) :=
  rfl

@[simp]
theorem completeSupportConditionMap_nearLitter_eq {π : StructApprox β} {N : NearLitter}
    {B : ExtendedIndex β} :
    π.completeSupportConditionMap (inr N, B) = (inr (π.completeNearLitterMap B N), B) :=
  rfl

theorem completeSupportConditionMap_injective (hπf : π.Free) :
    Injective π.completeSupportConditionMap := by
  rintro ⟨a₁ | N₁, B₁⟩ ⟨a₂ | N₂, B₂⟩ h <;>
    rw [Prod.ext_iff] at h <;>
    simp only [completeSupportConditionMap_atom_eq,
      completeSupportConditionMap_nearLitter_eq,
      inl.injEq, inr.injEq, false_and] at h
  · cases h.2
    cases completeAtomMap_injective hπf B₁ h.1
    rfl
  · cases h.2
    cases completeNearLitterMap_injective hπf B₁ h.1
    rfl

def preimageConstrained (π : StructApprox β) (c : SupportCondition β) : Set (SupportCondition β) :=
  π.completeSupportConditionMap ⁻¹' {d | d ≺[α] c}

theorem preimageConstrained_small (hπf : π.Free) (c : SupportCondition β) :
    Small (preimageConstrained π c) :=
  Small.preimage (completeSupportConditionMap_injective hπf) (small_constrains c)

noncomputable def preimageAction (hπf : π.Free) (c : SupportCondition β) : StructAction β :=
  constrainedAction π (preimageConstrained π c) (preimageConstrained_small hπf c)

theorem preimageAction_eq_constrainedAction (hπf : π.Free) (c : SupportCondition β) :
    preimageAction hπf c =
      constrainedAction π (preimageConstrained π c) (preimageConstrained_small hπf c) :=
  rfl

-- In fact, any `constrained_action` is lawful.
theorem preimageAction_lawful (hπf : π.Free) {c : SupportCondition β} :
    (preimageAction hπf c).Lawful := by
  intro A
  constructor
  · intro a b ha hb hab
    exact completeAtomMap_injective hπf A hab
  · intro L₁ L₂ hL₁ hL₂ hL
    exact completeLitterMap_injective hπf A (eq_of_completeLitterMap_inter_nonempty hL)
  · intro a _ L _
    exact (completeAtomMap_mem_completeNearLitterMap_toNearLitter hπf).symm

theorem preimageAction_comp_mapFlexible {hπf : π.Free} {γ : Iio α} {c : SupportCondition β}
    (A : Path (β : TypeIndex) γ) : ((preimageAction hπf c).comp A).MapFlexible :=
  constrainedAction_comp_mapFlexible hπf A

theorem Relation.reflTransGen_of_eq {α : Type _} {r : α → α → Prop} {x y : α} (h : x = y) :
    Relation.ReflTransGen r x y := by
  cases h
  rfl

theorem preimageAction_coherent (hπf : π.Free) {γ : Iio α} (A : Path (β : TypeIndex) γ)
    (B : ExtendedIndex γ) (N : NearLitter) (c : SupportCondition β)
    (hc : (inr (π.completeNearLitterMap (A.comp B) N), A.comp B) ≺[α] c) (ρ : Allowable γ)
    (h : (((preimageAction hπf c).comp A).rc
      ((preimageAction_lawful hπf).comp _)).ExactlyApproximates (Allowable.toStructPerm ρ)) :
    completeNearLitterMap π (A.comp B) N =
    StructPerm.derivative B (Allowable.toStructPerm ρ) • N := by
  refine' constrainedAction_coherent hπf A B N _ _ _
    ((preimageAction_lawful hπf).comp _) ρ h
  refine' ⟨_, _, Relation.ReflTransGen.refl⟩
  exact hc

theorem preimageAction_coherent_atom (hπf : π.Free) {γ : Iio α} (A : Path (β : TypeIndex) γ)
    (B : ExtendedIndex γ) (a : Atom) (c : SupportCondition β)
    (hc : (inl (π.completeAtomMap (A.comp B) a), A.comp B) ≺[α] c) (ρ : Allowable γ)
    (h : (((preimageAction hπf c).comp A).rc
      ((preimageAction_lawful hπf).comp _)).ExactlyApproximates (Allowable.toStructPerm ρ)) :
    completeAtomMap π (A.comp B) a = StructPerm.derivative B (Allowable.toStructPerm ρ) • a := by
  refine' constrainedAction_coherent_atom A B a _ _ _ _ ρ h
  refine' ⟨_, _, Relation.ReflTransGen.refl⟩
  exact hc

theorem completeLitterMap_surjective_extends (hπf : π.Free) (A : ExtendedIndex β) (L : Litter)
    (ha : ∀ (B : ExtendedIndex β) (a : Atom),
      (inl a, B) ≺[α] (inr L.toNearLitter, A) → a ∈ range (π.completeAtomMap B))
    (hN : ∀ (B : ExtendedIndex β) (N : NearLitter),
      (inr N, B) ≺[α] (inr L.toNearLitter, A) → N ∈ range (π.completeNearLitterMap B)) :
    L ∈ range (π.completeLitterMap A) := by
  obtain h | ⟨⟨h⟩⟩ | ⟨⟨h⟩⟩ := flexible_cases' β L A
  · refine' ⟨(NearLitterApprox.flexibleCompletion α (π A) A).symm • L, _⟩
    rw [completeLitterMap_eq_of_flexible, NearLitterApprox.right_inv_litter]
    · rw [NearLitterApprox.flexibleCompletion_litterPerm_domain_free α (π A) A (hπf A)]
      exact h
    · exact NearLitterApprox.flexibleCompletion_symm_smul_flexible α (π A) A (hπf A) L h
  · obtain ⟨γ, ε, hε, C, a, rfl, rfl⟩ := h
    obtain ⟨b, rfl⟩ := ha _ a (Constrains.fMap_bot hε _ a)
    refine' ⟨fMap (show ⊥ ≠ (ε : TypeIndex) from bot_ne_coe) b, _⟩
    rw [completeLitterMap_eq_of_inflexibleBot ⟨γ, ε, hε, C, b, rfl, rfl⟩]
  · obtain ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ := h
    refine' ⟨fMap (coe_ne_coe.mpr <| coe_ne' hδε)
      (((preimageAction hπf
            (inr (fMap (coe_ne_coe.mpr <| coe_ne' hδε) t).toNearLitter,
              (B.cons (coe_lt hε)).cons (bot_lt_coe _))).hypothesisedAllowable
          ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩
          ((preimageAction_lawful hπf).comp _) (preimageAction_comp_mapFlexible _))⁻¹ • t), _⟩
    rw [completeLitterMap_eq_of_inflexibleCoe ⟨γ, δ, ε, hδ, hε, hδε, B, _, rfl, rfl⟩
        ((ihAction_lawful hπf _).comp _) (ihAction_comp_mapFlexible hπf _ _)]
    refine' congr_arg _ _
    rw [smul_smul]
    refine' (designatedSupport t).supports _ _
    intro c hc
    rw [mul_smul, smul_eq_iff_eq_inv_smul]
    change (_, c.2) = (_, c.2)
    refine' Prod.ext _ rfl
    obtain ⟨a | N, A⟩ := c
    · change inl _ = inl _
      simp only [inl.injEq]
      have hac := Constrains.fMap hδ hε hδε B t _ hc
      specialize ha _ a hac
      obtain ⟨b, ha⟩ := ha
      have : (StructPerm.derivative A
        (Allowable.toStructPerm ((preimageAction hπf
            (inr (fMap (coe_ne_coe.mpr <| coe_ne' hδε) t).toNearLitter,
              (B.cons (coe_lt hε)).cons (bot_lt_coe _))).hypothesisedAllowable
              ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ ((preimageAction_lawful hπf).comp _)
              (preimageAction_comp_mapFlexible _))))⁻¹ • a = b
      · rw [inv_smul_eq_iff, ← ha]
        rw [StructAction.hypothesisedAllowable]
        refine' preimageAction_coherent_atom hπf (B.cons <| coe_lt hδ) A b _ _ _
          (StructAction.allowable_exactlyApproximates _ _ _ _)
        rw [ha]
        exact hac
      trans b
      · rw [map_inv, map_inv, this]
      · rw [map_inv, map_inv, ← smul_eq_iff_eq_inv_smul, ← ha]
        rw [StructAction.hypothesisedAllowable]
        refine' (ihAction_coherent_atom (B.cons <| coe_lt hδ) A b _ _
          ((ihAction_lawful hπf _).comp _) _
          (StructAction.allowable_exactlyApproximates _ _ _ _)).symm
        refine' Relation.TransGen.tail' _
          (Constrains.fMap hδ hε hδε B _ _ (smul_mem_designatedSupport hc _))
        refine' Relation.reflTransGen_of_eq _
        refine' Prod.ext _ rfl
        change inl _ = inl _
        simp only [map_inv, eq_inv_smul_iff, ← this, smul_inv_smul]
    · change inr _ = inr _
      simp only [inr.injEq]
      have hNc := Constrains.fMap hδ hε hδε B t _ hc
      specialize hN _ N hNc
      obtain ⟨N', hN⟩ := hN
      have : (StructPerm.derivative A
        (Allowable.toStructPerm ((preimageAction hπf
          (inr (fMap (coe_ne_coe.mpr <| coe_ne' hδε) t).toNearLitter,
            (B.cons (coe_lt hε)).cons (bot_lt_coe _))).hypothesisedAllowable
              ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ ((preimageAction_lawful hπf).comp _)
              (preimageAction_comp_mapFlexible _))))⁻¹ • N = N'
      · rw [inv_smul_eq_iff, ← hN]
        rw [StructAction.hypothesisedAllowable]
        refine' preimageAction_coherent hπf (B.cons <| coe_lt hδ) A N' _ _ _
          (StructAction.allowable_exactlyApproximates _ _ _ _)
        rw [hN]
        exact hNc
      trans N'
      · rw [map_inv, map_inv, this]
      · rw [map_inv, map_inv, ← smul_eq_iff_eq_inv_smul, ← hN]
        rw [StructAction.hypothesisedAllowable]
        refine' (ihAction_coherent hπf (B.cons <| coe_lt hδ) A N' _ _
          ((ihAction_lawful hπf _).comp _) _
          (StructAction.allowable_exactlyApproximates _ _ _ _)).symm
        refine' Relation.TransGen.tail' _
          (Constrains.fMap hδ hε hδε B _ _ (smul_mem_designatedSupport hc _))
        refine' Relation.reflTransGen_of_eq _
        refine' Prod.ext _ rfl
        change inr _ = inr _
        simp only [map_inv, eq_inv_smul_iff, ← this, smul_inv_smul]

theorem atom_mem_range_of_mem_completeNearLitterMap (A : ExtendedIndex β) (a : Atom)
    {N : NearLitter} (h : a ∈ π.completeNearLitterMap A N) : a ∈ range (π.completeAtomMap A) := by
  rw [← SetLike.mem_coe] at h
  rw [completeNearLitterMap_eq'] at h
  obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := h
  · rw [completeNearLitterMap_toNearLitter_eq] at h₁
    obtain h₁ | h₁ := h₁
    · exact completeAtomMap_surjective_extends A a ⟨_, h₁.1.symm⟩
    · obtain ⟨b, h₁, rfl⟩ := h₁
      refine' ⟨b, _⟩
      exact completeAtomMap_eq_of_mem_domain h₁.2
  · obtain ⟨b, _, rfl⟩ := h₁
    exact ⟨b, rfl⟩

theorem completeNearLitterMap_coe (hπf : π.Free) (A : ExtendedIndex β) (N : NearLitter) :
    (π.completeNearLitterMap A N : Set Atom) = π.completeAtomMap A '' N := by
  ext a : 1
  constructor
  · intro h
    obtain ⟨b, rfl⟩ := atom_mem_range_of_mem_completeNearLitterMap A a h
    rw [SetLike.mem_coe, completeAtomMap_mem_completeNearLitterMap hπf] at h
    exact ⟨b, h, rfl⟩
  · rintro ⟨b, h, rfl⟩
    rw [SetLike.mem_coe, completeAtomMap_mem_completeNearLitterMap hπf]
    exact h

@[simp]
theorem preimage_symmDiff {α β : Type _} {s t : Set β} {f : α → β} :
    f ⁻¹' s ∆ t = (f ⁻¹' s) ∆ (f ⁻¹' t) :=
  rfl

theorem completeNearLitterMap_surjective_extends (hπf : π.Free) (A : ExtendedIndex β)
    (N : NearLitter) (hN : N.1 ∈ range (π.completeLitterMap A))
    (ha : litterSet N.1 ∆ N ⊆ range (π.completeAtomMap A)) :
    N ∈ range (π.completeNearLitterMap A) := by
  obtain ⟨L, hN⟩ := hN
  refine' ⟨⟨L, π.completeAtomMap A ⁻¹' N, _⟩, _⟩
  · suffices Small ((π.completeAtomMap A '' L.toNearLitter) ∆ N) by
      have := Small.preimage (completeAtomMap_injective hπf A) this
      rw [preimage_symmDiff, preimage_image_eq _ (completeAtomMap_injective hπf A)] at this
      exact this
    rw [← completeNearLitterMap_coe hπf]
    refine' IsNearLitter.near _ N.2.2
    simp only [NearLitter.isNearLitter, completeNearLitterMap_fst_eq]
    exact hN
  · refine' SetLike.coe_injective _
    rw [completeNearLitterMap_coe hπf]
    simp only [NearLitter.coe_mk, Subtype.coe_mk, Litter.coe_toNearLitter]
    rw [image_preimage_eq_of_subset _]
    intro a ha'
    by_cases a.1 = N.1
    · rw [← hN] at h
      exact completeAtomMap_surjective_extends A a ⟨_, h.symm⟩
    · exact ha (Or.inr ⟨ha', h⟩)

variable (π)

def CompleteMapSurjectiveAt : SupportCondition β → Prop
  | (inl a, A) => a ∈ range (π.completeAtomMap A)
  | (inr N, A) => N ∈ range (π.completeNearLitterMap A)

variable {π}

theorem completeMap_surjective_extends (hπf : π.Free) (c : SupportCondition β)
    (hc : ∀ d : SupportCondition β, d <[α] c → π.CompleteMapSurjectiveAt d) :
    π.CompleteMapSurjectiveAt c := by
  obtain ⟨a | N, A⟩ := c
  · refine' completeAtomMap_surjective_extends A a _
    obtain ⟨N, hN⟩ := hc (inr a.1.toNearLitter, A) (Relation.TransGen.single <| Constrains.atom a A)
    refine' ⟨N.1, _⟩
    apply_fun Sigma.fst at hN
    simp only [Litter.toNearLitter_fst, completeNearLitterMap_fst_eq'] at hN
    exact hN
  · refine' completeNearLitterMap_surjective_extends hπf A N _ _
    · refine' completeLitterMap_surjective_extends hπf A N.1 _ _
      · intro B a h
        exact hc (inl a, B) (transGen_nearLitter <| Relation.TransGen.single h)
      · intro B N h
        exact hc (inr N, B) (transGen_nearLitter <| Relation.TransGen.single h)
    · intro a h
      exact hc (inl a, A) (Relation.TransGen.single <| Constrains.symmDiff N a h A)

theorem completeMapSurjectiveAtAll (hπf : π.Free) (c : SupportCondition β) :
    π.CompleteMapSurjectiveAt c :=
  WellFounded.induction (trans_constrains_wf α β) c (completeMap_surjective_extends hπf)

theorem completeAtomMap_surjective (hπf : π.Free) (A : ExtendedIndex β) :
    Surjective (π.completeAtomMap A) := fun a => completeMapSurjectiveAtAll hπf (inl a, A)

theorem completeNearLitterMap_surjective (hπf : π.Free) (A : ExtendedIndex β) :
    Surjective (π.completeNearLitterMap A) := fun N => completeMapSurjectiveAtAll hπf (inr N, A)

theorem completeLitterMap_surjective (hπf : π.Free) (A : ExtendedIndex β) :
    Surjective (π.completeLitterMap A) := by
  intro L
  obtain ⟨N, hN⟩ := completeNearLitterMap_surjective hπf A L.toNearLitter
  refine' ⟨N.1, _⟩
  apply_fun Sigma.fst at hN
  simp only [completeNearLitterMap_fst_eq', Litter.toNearLitter_fst] at hN
  exact hN

theorem completeAtomMap_bijective (hπf : π.Free) (A : ExtendedIndex β) :
    Bijective (π.completeAtomMap A) :=
  ⟨completeAtomMap_injective hπf A, completeAtomMap_surjective hπf A⟩

theorem completeLitterMap_bijective (hπf : π.Free) (A : ExtendedIndex β) :
    Bijective (π.completeLitterMap A) :=
  ⟨completeLitterMap_injective hπf A, completeLitterMap_surjective hπf A⟩

theorem completeNearLitterMap_bijective (hπf : π.Free) (A : ExtendedIndex β) :
    Bijective (π.completeNearLitterMap A) :=
  ⟨completeNearLitterMap_injective hπf A, completeNearLitterMap_surjective hπf A⟩

noncomputable def completeAtomPerm (hπf : π.Free) (A : ExtendedIndex β) : Perm Atom :=
  Equiv.ofBijective _ (completeAtomMap_bijective hπf A)

noncomputable def completeLitterPerm (hπf : π.Free) (A : ExtendedIndex β) : Perm Litter :=
  Equiv.ofBijective _ (completeLitterMap_bijective hπf A)

theorem completeAtomPerm_apply (hπf : π.Free) (A : ExtendedIndex β) (a : Atom) :
    completeAtomPerm hπf A a = π.completeAtomMap A a :=
  rfl

theorem completeLitterPerm_apply (hπf : π.Free) (A : ExtendedIndex β) (L : Litter) :
    completeLitterPerm hπf A L = π.completeLitterMap A L :=
  rfl

noncomputable def completeNearLitterPerm (hπf : π.Free) (A : ExtendedIndex β) : NearLitterPerm
    where
  atomPerm := completeAtomPerm hπf A
  litterPerm := completeLitterPerm hπf A
  near := by
    intro L s hs
    have :
      (completeAtomPerm hπf A)⁻¹.toFun ⁻¹' s =
        (π.completeNearLitterMap A ⟨L, s, hs⟩ : Set Atom)
    · simp only [completeNearLitterMap_coe hπf, toFun_as_coe, Perm.preimage_inv, NearLitter.coe_mk]
      rfl
    rw [this]
    simp only [NearLitter.isNearLitter, completeNearLitterMap_fst_eq']
    rfl

theorem completeNearLitterPerm_smul_atom (hπf : π.Free) (A : ExtendedIndex β) (a : Atom) :
    completeNearLitterPerm hπf A • a = π.completeAtomMap A a :=
  rfl

theorem completeNearLitterPerm_smul_litter (hπf : π.Free) (A : ExtendedIndex β) (L : Litter) :
    completeNearLitterPerm hπf A • L = π.completeLitterMap A L :=
  rfl

theorem completeNearLitterPerm_smul_nearLitter (hπf : π.Free) (A : ExtendedIndex β)
    (N : NearLitter) : completeNearLitterPerm hπf A • N = π.completeNearLitterMap A N := by
  refine' SetLike.coe_injective _
  rw [completeNearLitterMap_coe hπf]
  rfl

def AllowableBelow (hπf : π.Free) (γ : IicBot α) (A : Path (β : TypeIndex) γ) : Prop :=
  ∃ ρ : Allowable γ,
    ∀ B : ExtendedIndex γ,
      StructPerm.ofBot (StructPerm.derivative B (Allowable.toStructPerm ρ)) =
        completeNearLitterPerm hπf (A.comp B)

@[simp]
theorem ofBot_toStructPerm (π : Allowable ⊥) : StructPerm.ofBot (Allowable.toStructPerm π) = π := by
  rfl

theorem allowableBelow_bot (hπf : π.Free) (A : ExtendedIndex β) : AllowableBelow hπf ⊥ A := by
  refine' ⟨completeNearLitterPerm hπf A, _⟩
  intro B
  obtain B | ⟨B, h⟩ := B
  · rfl
  · -- TODO: Make this a lemma.
    cases le_bot_iff.mp (le_of_path B)
    change (⊥ : TypeIndex) < ⊥ at h
    simp only [lt_self_iff_false] at h

theorem exists_nil_cons_of_path' {β γ : TypeIndex} (A : Path (β : TypeIndex) γ)
    (hA : A.length ≠ 0) :
    ∃ δ : TypeIndex,
      ∃ h : (δ : TypeIndex) < β,
        ∃ B : Path δ γ, A = ((Path.nil : Path (β : TypeIndex) β).cons h).comp B := by
  set n := A.length with hn
  clear_value n
  induction' n with n ih generalizing γ
  · cases hA rfl
  cases' A with δ _ A hδ
  · cases hn
  simp only [Path.length_cons, Nat.succ_eq_add_one, add_left_inj] at hn
  obtain _ | n := n
  · cases Path.eq_of_length_zero A hn.symm
    cases path_eq_nil A
    exact ⟨γ, hδ, Path.nil, rfl⟩
  · obtain ⟨ε, hε, B, rfl⟩ := ih A n.succ_ne_zero hn
    exact ⟨ε, hε, B.cons hδ, rfl⟩

theorem exists_nil_cons_of_path {β : Iic α} (A : ExtendedIndex β) :
    ∃ γ : IioBot α,
      ∃ h : (γ : TypeIndex) < β,
        ∃ B : ExtendedIndex γ, A = ((Path.nil : Path (β : TypeIndex) β).cons h).comp B := by
  have := exists_nil_cons_of_path' A ?_
  obtain ⟨γ, h, B, rfl⟩ := this
  · refine' ⟨⟨γ, _⟩, h, B, rfl⟩
    exact lt_of_lt_of_le h (coe_le_coe.mpr β.prop)
  · intro h
    cases Path.eq_of_length_zero A h

theorem iioBot_cases (δ : IioBot α) : δ = ⊥ ∨ ∃ ε : Iio α, δ = ε := by
  obtain ⟨_ | δ, hδ⟩ := δ
  · exact Or.inl rfl
  · exact Or.inr ⟨⟨δ, coe_lt_coe.mp hδ⟩, rfl⟩

set_option pp.proofs.withType false

-- TODO: Use this theorem in places above.
-- I think that the `change` and `obtain` calls slow down proofs severely in Lean 4.
-- TODO: Canonicalise uses of `<` to always be with respect to `TypeIndex`.
theorem supports {β : Iio α} {π π' : Allowable β} {t : Tangle β}
    (ha : ∀ a A, (inl a, A) ∈ designatedSupport t →
      StructPerm.derivative A (Allowable.toStructPerm π) • a =
      StructPerm.derivative A (Allowable.toStructPerm π') • a)
    (hN : ∀ N A, (inr N, A) ∈ designatedSupport t →
      StructPerm.derivative A (Allowable.toStructPerm π) • N =
      StructPerm.derivative A (Allowable.toStructPerm π') • N) :
    π • t = π' • t := by
  rw [← inv_smul_eq_iff, smul_smul]
  refine' (designatedSupport t).supports _ _
  intro c hc
  rw [mul_smul, inv_smul_eq_iff]
  change (_, c.2) = (_, c.2)
  refine Prod.ext ?_ rfl
  obtain ⟨a | N, A⟩ := c
  · change inl _ = inl _
    simp only [inl.injEq]
    exact ha a A hc
  · change inr _ = inr _
    simp only [inr.injEq]
    exact hN N A hc

theorem ConNF.StructApprox.extracted_1
  (hπf : π.Free) (γ : Iic α) (A : Path (β : TypeIndex) γ)
  (ρs : (δ : IioBot α) → (δ : TypeIndex) < γ → Allowable δ)
  (hρ : ∀ (δ : IioBot α) (h : (δ : TypeIndex) < γ) (B : ExtendedIndex δ),
    StructPerm.ofBot (StructPerm.derivative B (Allowable.toStructPerm (ρs δ h))) =
      completeNearLitterPerm hπf ((A.cons h).comp B))
  (ε : Iio α) (hε : (ε : TypeIndex) < γ) (a : Atom) :
  ρs ε hε • fMap (show ⊥ ≠ (ε : TypeIndex) from bot_ne_coe) a =
    fMap (show ⊥ ≠ (ε : TypeIndex) from bot_ne_coe) (ρs ⊥ (bot_lt_coe _) • a) := by
  change StructPerm.toNearLitterPerm (Allowable.toStructPerm _) • fMap _ (show Tangle ⊥ from a) = _
  have := hρ ε hε (Path.nil.cons (bot_lt_coe _))
  simp only [Path.comp_cons, Path.comp_nil] at this
  change StructPerm.toNearLitterPerm (Allowable.toStructPerm _) = _ at this
  rw [this]
  rw [completeNearLitterPerm_smul_litter]
  refine' (completeLitterMap_eq_of_inflexibleBot
    ⟨γ, ε, coe_lt_coe.mp hε, A, a, rfl, rfl⟩).trans _
  refine' congr_arg _ _
  specialize hρ ⊥ (bot_lt_coe _) Path.nil
  rw [Path.comp_nil, StructPerm.derivative_nil
    (Allowable.toStructPerm (ρs ⊥ (bot_lt_coe _)))] at hρ
  rw [(ofBot_toStructPerm (ρs ⊥ (bot_lt_coe _))).symm.trans hρ]
  rfl

theorem ConNF.StructApprox.extracted_2
  (hπf : π.Free) (γ : Iic α) (A : Path (β : TypeIndex) γ)
  (ρs : (δ : IioBot α) → (δ : TypeIndex) < γ → Allowable δ)
  (hρ : ∀ (δ : IioBot α) (h : (δ : TypeIndex) < γ) (B : ExtendedIndex δ),
    StructPerm.ofBot (StructPerm.derivative B (Allowable.toStructPerm (ρs δ h))) =
      completeNearLitterPerm hπf ((A.cons h).comp B))
  (δ : Iio α) (ε : Iio α) (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < γ)
  (hδε : δ ≠ ε) (t : Tangle ↑δ) :
  ρs ε hε • fMap (coe_ne_coe.mpr <| coe_ne' hδε) t =
    fMap (coe_ne_coe.mpr <| coe_ne' hδε) (ρs δ hδ • t) := by
  change StructPerm.toNearLitterPerm (Allowable.toStructPerm _) • fMap _ t = _
  have := hρ ε hε (Path.nil.cons (bot_lt_coe _))
  simp only [Path.comp_cons, Path.comp_nil] at this
  change StructPerm.toNearLitterPerm (Allowable.toStructPerm _) = _ at this
  rw [this]
  rw [completeNearLitterPerm_smul_litter]
  refine' (completeLitterMap_eq_of_inflexibleCoe
    ⟨γ, δ, ε, coe_lt_coe.mp hδ, coe_lt_coe.mp hε, _, A, t, rfl, rfl⟩
    ((ihAction_lawful hπf _).comp _) (ihAction_comp_mapFlexible hπf _ _)).trans _
  · rintro rfl
    cases hδε rfl
  refine' congr_arg _ _
  simp only
  refine supports (t := t) ?_ ?_
  · intros a B ha
    have := ihAction_coherent_atom (π := π) (A.cons _) B a
      (inr (fMap (show (δ : TypeIndex) ≠ ε from ?_) t).toNearLitter, _)
      (Relation.TransGen.single <| Constrains.fMap ?_ ?_ ?_ _ t _ ha)
      ((ihAction_lawful hπf _).comp _) ?_ ?_
    exact this.symm.trans (congr_arg (fun π => π • a) (hρ δ hδ B)).symm
    · intro h
      simp only [coe_inj, Subtype.coe_inj] at h
      cases hδε h
    · exact coe_lt_coe.mp hδ
    · exact coe_lt_coe.mp hε
    · rintro rfl
      cases hδε rfl
    · exact (ihAction π.foaHypothesis).hypothesisedAllowable_exactlyApproximates
        ⟨γ, δ, ε, _, _, _, _, t, rfl, rfl⟩ _ _
  · intros N B hN
    have := ihAction_coherent hπf (A.cons _) B N
      (inr (fMap (show (δ : TypeIndex) ≠ ε from ?_) t).toNearLitter, _)
      (Relation.TransGen.single <| Constrains.fMap ?_ ?_ ?_ _ t _ hN)
      ((ihAction_lawful hπf _).comp _) ?_ ?_
    rw [← completeNearLitterPerm_smul_nearLitter hπf] at this
    exact this.symm.trans (congr_arg (fun π => π • N) (hρ δ hδ B)).symm
    · exact coe_lt_coe.mp hδ
    · intro h
      simp only [coe_inj, Subtype.coe_inj] at h
      cases hδε h
    · exact coe_lt_coe.mp hε
    · rintro rfl
      cases hδε rfl
    · exact (ihAction π.foaHypothesis).hypothesisedAllowable_exactlyApproximates
        ⟨γ, δ, ε, _, _, _, _, t, rfl, rfl⟩ _ _

theorem allowableBelow_extends (hπf : π.Free) (γ : Iic α) (A : Path (β : TypeIndex) γ)
    (h : ∀ (δ : IioBot α) (h : (δ : TypeIndex) < γ), AllowableBelow hπf δ (A.cons h)) :
    AllowableBelow hπf γ A := by
  choose ρs hρ using h
  refine' ⟨allowableOfSmulFMap γ ρs _, _⟩
  · intro δ ε hδ hε hδε t
    obtain rfl | ⟨δ, rfl⟩ := iioBot_cases δ
    · exact ConNF.StructApprox.extracted_1 hπf γ A ρs hρ ε hε t
    · refine ConNF.StructApprox.extracted_2 hπf γ A ρs hρ δ ε hδ hε ?_ t
      rintro rfl
      exact hδε rfl
  · intro B
    obtain ⟨δ, hδ, B, rfl⟩ := exists_nil_cons_of_path B
    specialize hρ δ hδ B
    rw [← StructPerm.derivative_derivative]
    have := allowableOfSmulFMap_derivative_eq (πs := ρs) (h := ?_) δ hδ
    apply_fun Allowable.toStructPerm at this
    rw [← allowableDerivative_eq] at this
    rw [← this] at hρ
    rw [← Path.comp_assoc, Path.comp_cons, Path.comp_nil]
    exact hρ

theorem allowableBelow_all (hπf : π.Free) (γ : Iic α) (A : Path (β : TypeIndex) γ) :
    AllowableBelow hπf γ A := by
  obtain ⟨γ, hγ⟩ := γ
  revert hγ
  refine' WellFounded.induction
    (C := fun γ => ∀ (hγ : γ ∈ Iic α) (A : Path (β : TypeIndex) γ),
      AllowableBelow hπf ⟨γ, coe_le_coe.mpr hγ⟩ A) Λwf.wf γ _
  clear γ
  intro γ ih hγ A
  refine' allowableBelow_extends hπf ⟨γ, hγ⟩ A _
  intro δ hδ
  obtain rfl | ⟨δ, rfl⟩ := iioBot_cases δ
  · exact allowableBelow_bot hπf _
  · exact ih δ (coe_lt_coe.mp hδ) (le_of_lt (Iio.lt δ)) _

noncomputable def completeAllowable (hπf : π.Free) : Allowable β :=
  (allowableBelow_all hπf β Path.nil).choose

theorem completeAllowable_derivative (hπf : π.Free) (A : ExtendedIndex β) :
    StructPerm.ofBot (StructPerm.derivative A (Allowable.toStructPerm <| completeAllowable hπf)) =
      completeNearLitterPerm hπf A := by
  have := (allowableBelow_all hπf β Path.nil).choose_spec A
  rw [Path.nil_comp] at this
  exact this

theorem complete_exception_mem (hπf : π.Free) (A : ExtendedIndex β) (a : Atom)
    (ha : (completeNearLitterPerm hπf A).IsException a) : a ∈ (π A).atomPerm.domain := by
  unfold NearLitterPerm.IsException at ha
  simp only [mem_litterSet, completeNearLitterPerm_smul_atom,
    completeNearLitterPerm_smul_litter] at ha
  obtain ha | ha := ha
  · have := completeNearLitterMap_toNearLitter_eq (π := π) A a.1
    rw [completeNearLitterMap_coe hπf, Set.ext_iff] at this
    have := (this (π.completeAtomMap A a)).mp ⟨_, rfl, rfl⟩
    obtain ha' | ⟨b, ⟨hb₁, hb₂⟩, hb₃⟩ := this
    · cases ha ha'.1
    dsimp only at hb₃
    rw [← completeAtomMap_eq_of_mem_domain hb₂] at hb₃
    cases completeAtomMap_injective hπf A hb₃
    exact hb₂
  · obtain ⟨a, rfl⟩ := completeAtomMap_surjective hπf A a
    rw [eq_inv_smul_iff, ← completeNearLitterPerm_smul_atom hπf, inv_smul_smul] at ha
    have := completeNearLitterMap_toNearLitter_eq (π := π) A a.1
    rw [completeNearLitterMap_coe hπf, Set.ext_iff] at this
    have := (this (π.completeAtomMap A a)).mp ⟨_, rfl, rfl⟩
    obtain ha' | ⟨b, ⟨hb₁, hb₂⟩, hb₃⟩ := this
    · cases ha ha'.1.symm
    · dsimp only at hb₃
      rw [← completeAtomMap_eq_of_mem_domain hb₂] at hb₃
      cases completeAtomMap_injective hπf A hb₃
      rw [completeAtomMap_eq_of_mem_domain hb₂]
      exact (π A).atomPerm.map_domain hb₂

theorem completeAllowable_exactlyApproximates (hπf : π.Free) :
    π.ExactlyApproximates (Allowable.toStructPerm <| completeAllowable hπf) := by
  intro A
  refine' ⟨⟨_, _⟩, _⟩
  · intro a ha
    rw [completeAllowable_derivative, completeNearLitterPerm_smul_atom,
      completeAtomMap_eq_of_mem_domain ha]
  · intro L hL
    rw [completeAllowable_derivative, completeNearLitterPerm_smul_litter,
      completeLitterMap_eq_of_flexible (hπf A L hL),
      NearLitterApprox.flexibleCompletion_smul_of_mem_domain _ _ A L hL]
    rfl
  · intro a ha
    rw [completeAllowable_derivative] at ha
    exact complete_exception_mem hπf A a ha

def foa_extends : FoaIh β := fun _ hπf =>
  ⟨completeAllowable hπf, completeAllowable_exactlyApproximates hπf⟩

theorem freedom_of_action (β : Iic α) (π₀ : StructApprox β) (h : π₀.Free) :
    ∃ π : Allowable β, π₀.ExactlyApproximates (Allowable.toStructPerm π) := by
  obtain ⟨β, hβ⟩ := β
  revert hβ
  refine' WellFounded.induction
    (C := fun β => ∀ (hβ : β ∈ Iic α) (π₀ : StructApprox (⟨β, hβ⟩ : Iic α)),
      Free π₀ → ∃ π : @Allowable _ (⟨β, hβ⟩ : Iic α) Phase2Data.coreTangleData,
        ExactlyApproximates π₀ (@Allowable.toStructPerm _ _ Phase2Data.coreTangleData π)) Λwf.wf β _
  intro β ih hβ π₀ h
  have : FreedomOfActionHypothesis ⟨β, hβ⟩
  · constructor
    intro γ hγ
    exact ih γ hγ γ.prop
  exact foa_extends π₀ h

end StructApprox

end ConNF
