import Mathlib.Order.Extension.Well
import ConNF.Phase2.AtomCompletion
import ConNF.Phase2.NearLitterCompletion

#align_import phase2.complete_action

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
TODO: Rename `complete_atom_map`, `atom_completion` etc.
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
  ⟨fun B b hb => π.completeAtomMap B b, fun B N hb => π.completeNearLitterMap B N⟩

variable {π : StructApprox β}

section MapSpec

variable {A : ExtendedIndex β} {a : Atom} {L : Litter} {N : NearLitter}

theorem completeAtomMap_eq : π.completeAtomMap A a = π.atomCompletion A a π.foaHypothesis :=
  Hypothesis.fixAtom_eq _ _ _ _

theorem completeNearLitterMap_eq :
    π.completeNearLitterMap A N = π.nearLitterCompletion A N π.foaHypothesis :=
  Hypothesis.fixNearLitter_eq _ _ _ _

theorem completeLitterMap_eq : π.completeLitterMap A L = π.litterCompletion A L π.foaHypothesis :=
  by rw [complete_litter_map, complete_near_litter_map_eq] <;> rfl

theorem completeNearLitterMap_fst_eq :
    (π.completeNearLitterMap A L.toNearLitter).1 = π.completeLitterMap A L :=
  rfl

@[simp]
theorem completeNearLitterMap_fst_eq' :
    (π.completeNearLitterMap A N).1 = π.completeLitterMap A N.1 :=
  by
  rw [complete_near_litter_map_eq, near_litter_completion, complete_litter_map_eq]
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
    π.completeAtomMap A a = π A • a := by rw [complete_atom_map_eq, atom_completion, dif_pos h]

theorem completeAtomMap_eq_of_not_mem_domain {a} {A} (h : a ∉ (π A).atomPerm.domain) :
    π.completeAtomMap A a =
      ((π A).largestSublitter a.1).OrderIso ((π A).largestSublitter (π.completeLitterMap A a.1))
        ⟨a, (π A).mem_largestSublitter_of_not_mem_domain a h⟩ :=
  by rw [complete_atom_map_eq, atom_completion, dif_neg h] <;> rfl

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
          h.t) :=
  by rw [complete_litter_map_eq, litter_completion_of_inflexible_coe]

theorem completeLitterMap_eq_of_inflexible_coe' {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleCoe L A) :
    π.completeLitterMap A L =
      if h' : _ ∧ _ then
        fMap (WithBot.coe_ne_coe.mpr <| coe_ne' h.hδε)
          ((ihAction (π.foaHypothesis : Hypothesis ⟨inr L.toNearLitter, A⟩)).hypothesisedAllowable h
              h'.1 h'.2 •
            h.t)
      else L :=
  by rw [complete_litter_map_eq, litter_completion_of_inflexible_coe']

/-- A basic definition unfold. -/
theorem completeLitterMap_eq_of_inflexibleBot {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleBot L A) :
    π.completeLitterMap A L =
      fMap (show (⊥ : TypeIndex) ≠ (h.ε : Λ) from WithBot.bot_ne_coe)
        (π.completeAtomMap (h.b.cons (WithBot.bot_lt_coe _)) h.a) :=
  by rw [complete_litter_map_eq, litter_completion_of_inflexible_bot] <;> rfl

/-- A basic definition unfold. -/
theorem completeLitterMap_eq_of_flexible {A : ExtendedIndex β} {L : Litter} (h : Flexible α L A) :
    π.completeLitterMap A L = NearLitterApprox.flexibleCompletion α (π A) A • L := by
  rw [complete_litter_map_eq, litter_completion_of_flexible _ _ _ _ h]

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
    (he : e ∈ transConstrained c d) : e ∈ reflTransConstrained c d :=
  by
  cases he
  exact Or.inl he.to_refl
  exact Or.inr he.to_refl

theorem transConstrained_trans {c d e f : SupportCondition β} (he : e ∈ transConstrained c d)
    (hf : f ≤[α] e) : f ∈ transConstrained c d :=
  by
  cases he
  exact Or.inl (Relation.TransGen.trans_right hf he)
  exact Or.inr (Relation.TransGen.trans_right hf he)

theorem reflTransConstrained_trans {c d e f : SupportCondition β}
    (he : e ∈ reflTransConstrained c d) (hf : f ≤[α] e) : f ∈ reflTransConstrained c d :=
  by
  cases he
  exact Or.inl (hf.trans he)
  exact Or.inr (hf.trans he)

theorem transConstrained_of_reflTransConstrained_of_trans_constrains {c d e f : SupportCondition β}
    (he : e ∈ reflTransConstrained c d) (hf : f <[α] e) : f ∈ transConstrained c d :=
  by
  cases he
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
    (h : (inl a, A) ∈ transConstrained c d) : (inr a.fst.toNearLitter, A) ∈ transConstrained c d :=
  transConstrained_of_constrains h (Constrains.atom a A)

theorem fst_mem_transConstrained {c d : SupportCondition β} {A : ExtendedIndex β} {N : NearLitter}
    (hN : (inr N, A) ∈ transConstrained c d) : (inr N.fst.toNearLitter, A) ∈ transConstrained c d :=
  by
  cases hN
  exact Or.inl (trans_gen_near_litter' hN)
  exact Or.inr (trans_gen_near_litter' hN)

theorem fst_mem_refl_trans_constrained' {c d : SupportCondition β} {A : ExtendedIndex β} {a : Atom}
    (h : (inl a, A) ∈ reflTransConstrained c d) :
    (inr a.fst.toNearLitter, A) ∈ reflTransConstrained c d :=
  reflTransConstrained_of_constrains h (Constrains.atom a A)

theorem fst_mem_reflTransConstrained {c d : SupportCondition β} {A : ExtendedIndex β}
    {N : NearLitter} (hN : (inr N, A) ∈ reflTransConstrained c d) :
    (inr N.fst.toNearLitter, A) ∈ reflTransConstrained c d :=
  by
  cases hN
  exact Or.inl (refl_trans_gen_near_litter hN)
  exact Or.inr (refl_trans_gen_near_litter hN)

theorem fst_mem_transConstrained_of_mem_symmDiff {c d : SupportCondition β} {A : ExtendedIndex β}
    {N : NearLitter} {a : Atom} (h : a ∈ litterSet N.1 ∆ N)
    (hN : (inr N, A) ∈ transConstrained c d) : (inr a.fst.toNearLitter, A) ∈ transConstrained c d :=
  by
  obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := h
  · rw [mem_litter_set] at h₁
    rw [h₁]
    exact fst_mem_trans_constrained hN
  · cases hN
    · refine' fst_mem_trans_constrained' (Or.inl _)
      exact Relation.TransGen.head (constrains.symm_diff N a (Or.inr ⟨h₁, h₂⟩) A) hN
    · refine' fst_mem_trans_constrained' (Or.inr _)
      exact Relation.TransGen.head (constrains.symm_diff N a (Or.inr ⟨h₁, h₂⟩) A) hN

theorem fst_mem_reflTransConstrained_of_mem_symmDiff {c d : SupportCondition β}
    {A : ExtendedIndex β} {N : NearLitter} {a : Atom} (h : a ∈ litterSet N.1 ∆ N)
    (hN : (inr N, A) ∈ reflTransConstrained c d) :
    (inr a.fst.toNearLitter, A) ∈ reflTransConstrained c d :=
  by
  obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := h
  · rw [mem_litter_set] at h₁
    rw [h₁]
    exact fst_mem_refl_trans_constrained hN
  · cases hN
    · refine' fst_mem_refl_trans_constrained' (Or.inl _)
      exact Relation.ReflTransGen.head (constrains.symm_diff N a (Or.inr ⟨h₁, h₂⟩) A) hN
    · refine' fst_mem_refl_trans_constrained' (Or.inr _)
      exact Relation.ReflTransGen.head (constrains.symm_diff N a (Or.inr ⟨h₁, h₂⟩) A) hN

theorem fst_mem_transConstrained_of_mem {c d : SupportCondition β} {A : ExtendedIndex β}
    {N : NearLitter} {a : Atom} (h : a ∈ N) (hN : (inr N, A) ∈ transConstrained c d) :
    (inr a.fst.toNearLitter, A) ∈ transConstrained c d :=
  by
  by_cases ha : a.1 = N.1
  · rw [ha]
    exact fst_mem_trans_constrained hN
  · exact fst_mem_trans_constrained_of_mem_symm_diff (Or.inr ⟨h, ha⟩) hN

theorem eq_of_sublitter_bijection_apply_eq {π : NearLitterApprox} {L₁ L₂ L₃ L₄ : Litter} {a b} :
    ((π.largestSublitter L₁).OrderIso (π.largestSublitter L₂) a : Atom) =
        (π.largestSublitter L₃).OrderIso (π.largestSublitter L₄) b →
      L₁ = L₃ → L₂ = L₄ → (a : Atom) = b :=
  by
  rintro h₁ rfl rfl
  simp only [Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq] at h₁
  rw [h₁]

noncomputable def constrainedAction (π : StructApprox β) (s : Set (SupportCondition β))
    (hs : Small s) : StructAction β := fun B =>
  { atomMap := fun a =>
      ⟨∃ c : SupportCondition β, c ∈ s ∧ (inl a, B) ≤[α] c, fun h => π.completeAtomMap B a⟩
    litterMap := fun L =>
      ⟨∃ c : SupportCondition β, c ∈ s ∧ (inr L.toNearLitter, B) ≤[α] c, fun h =>
        π.completeNearLitterMap B L.toNearLitter⟩
    atomMap_dom_small :=
      by
      change
        Small
          ((fun a : atom => (inl a, B)) ⁻¹'
            {c : support_condition β | ∃ d : support_condition β, d ∈ s ∧ c ≤[α] d})
      simp_rw [← exists_prop]
      refine' small.preimage _ (reduction_small' α hs)
      intro a b h
      cases h
      rfl
    litterMap_dom_small :=
      by
      change
        Small
          ((fun L : litter => (inr L.toNearLitter, B)) ⁻¹'
            {c : support_condition β | ∃ d : support_condition β, d ∈ s ∧ c ≤[α] d})
      simp_rw [← exists_prop]
      refine' small.preimage _ (reduction_small' α hs)
      intro a b h
      cases h
      rfl }

/-- An object like `ih_action` that can take two support conditions. -/
noncomputable def ihsAction (π : StructApprox β) (c d : SupportCondition β) : StructAction β :=
  fun B =>
  { atomMap := fun a => ⟨(inl a, B) ∈ transConstrained c d, fun h => π.completeAtomMap B a⟩
    litterMap := fun L =>
      ⟨(inr L.toNearLitter, B) ∈ transConstrained c d, fun h =>
        π.completeNearLitterMap B L.toNearLitter⟩
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
      ⟨∃ c : SupportCondition β, c ∈ s ∧ (inl a, B) ≤[α] c, fun h => completeAtomMap π B a⟩ :=
  rfl

@[simp]
theorem constrainedAction_litterMap {π : StructApprox β} {s : Set (SupportCondition β)}
    {hs : Small s} {B : ExtendedIndex β} {L : Litter} :
    (constrainedAction π s hs B).litterMap L =
      ⟨∃ c : SupportCondition β, c ∈ s ∧ (inr L.toNearLitter, B) ≤[α] c, fun h =>
        π.completeNearLitterMap B L.toNearLitter⟩ :=
  rfl

@[simp]
theorem ihsAction_atomMap {π : StructApprox β} {c d : SupportCondition β} {B : ExtendedIndex β}
    {a : Atom} :
    (ihsAction π c d B).atomMap a =
      ⟨(inl a, B) ∈ transConstrained c d, fun h => completeAtomMap π B a⟩ :=
  rfl

@[simp]
theorem ihsAction_litterMap {π : StructApprox β} {c d : SupportCondition β} {B : ExtendedIndex β}
    {L : Litter} :
    (ihsAction π c d B).litterMap L =
      ⟨(inr L.toNearLitter, B) ∈ transConstrained c d, fun h =>
        π.completeNearLitterMap B L.toNearLitter⟩ :=
  rfl

theorem ihsAction_symm (π : StructApprox β) (c d : SupportCondition β) :
    ihsAction π c d = ihsAction π d c := by
  ext
  rw [ihs_action_atom_map, ihs_action_atom_map, trans_constrained_symm]
  rw [ihs_action_litter_map, ihs_action_litter_map, trans_constrained_symm]

@[simp]
theorem ihsAction_self (π : StructApprox β) (c : SupportCondition β) :
    ihsAction π c c = ihAction (π.foaHypothesis : Hypothesis c) :=
  by
  ext
  · rw [ihs_action_atom_map, ih_action_atom_map, trans_constrained_self]
    rfl
  · rw [ihs_action_litter_map, ih_action_litter_map, trans_constrained_self]
    rfl

theorem constrainedAction_mono {π : StructApprox β} {s t : Set (SupportCondition β)} {hs : Small s}
    {ht : Small t} (h : s ⊆ t) : constrainedAction π s hs ≤ constrainedAction π t ht := fun B =>
  ⟨⟨fun a ha => ⟨ha.some, h ha.choose_spec.1, ha.choose_spec.2⟩, fun a h => rfl⟩,
    ⟨fun L hL => ⟨hL.some, h hL.choose_spec.1, hL.choose_spec.2⟩, fun L h => rfl⟩⟩

theorem ihAction_le_constrainedAction {π : StructApprox β} {s : Set (SupportCondition β)}
    {hs : Small s} (c : SupportCondition β) (hc : ∃ d : SupportCondition β, d ∈ s ∧ c ≤[α] d) :
    ihAction (π.foaHypothesis : Hypothesis c) ≤ constrainedAction π s hs := fun B =>
  ⟨⟨fun a ha => ⟨hc.some, hc.choose_spec.1, trans ha.to_reflTransGen hc.choose_spec.2⟩, fun a h =>
      rfl⟩,
    ⟨fun L hL => ⟨hc.some, hc.choose_spec.1, trans hL.to_reflTransGen hc.choose_spec.2⟩, fun L h =>
      rfl⟩⟩

theorem ihAction_eq_constrainedAction (π : StructApprox β) (c : SupportCondition β) :
    ihAction (π.foaHypothesis : Hypothesis c) =
      constrainedAction π {d | d ≺[α] c} (small_constrains c) :=
  by
  ext
  · simp only [ih_action_atom_map, foa_hypothesis_atom_image, Part.mem_mk_iff, exists_prop,
      mem_set_of_eq, constrained_action_atom_map, and_congr_left_iff, Relation.TransGen.tail'_iff]
    intro h
    simp_rw [and_comm']
    rfl
  · simp only [ih_action_litter_map, Part.mem_mk_iff, exists_prop, mem_set_of_eq,
      and_congr_left_iff, Relation.TransGen.tail'_iff, foa_hypothesis_near_litter_image,
      constrained_action_litter_map]
    intro h
    simp_rw [and_comm']
    rfl

theorem ihsAction_eq_constrainedAction (π : StructApprox β) (c d : SupportCondition β) :
    ihsAction π c d =
      constrainedAction π ({e | e ≺[α] c} ∪ {e | e ≺[α] d})
        ((small_constrains c).union (small_constrains d)) :=
  by
  ext
  · simp only [Relation.TransGen.tail'_iff, trans_constrained, mem_union, ihs_action_atom_map,
      Part.mem_mk_iff, exists_prop, mem_set_of_eq, constrained_action_atom_map, and_congr_left_iff]
    intro h
    constructor
    · rintro (⟨b, hb₁, hb₂⟩ | ⟨b, hb₁, hb₂⟩)
      · exact ⟨b, Or.inl hb₂, hb₁⟩
      · exact ⟨b, Or.inr hb₂, hb₁⟩
    · rintro ⟨b, hb₁ | hb₁, hb₂⟩
      · exact Or.inl ⟨b, hb₂, hb₁⟩
      · exact Or.inr ⟨b, hb₂, hb₁⟩
  · simp only [Relation.TransGen.tail'_iff, trans_constrained, mem_union, Part.mem_mk_iff,
      exists_prop, mem_set_of_eq, and_congr_left_iff, ihs_action_litter_map,
      constrained_action_litter_map]
    intro h
    constructor
    · rintro (⟨b, hb₁, hb₂⟩ | ⟨b, hb₁, hb₂⟩)
      · exact ⟨b, Or.inl hb₂, hb₁⟩
      · exact ⟨b, Or.inr hb₂, hb₁⟩
    · rintro ⟨b, hb₁ | hb₁, hb₂⟩
      · exact Or.inl ⟨b, hb₂, hb₁⟩
      · exact Or.inr ⟨b, hb₂, hb₁⟩

theorem ihAction_le_ihsAction (π : StructApprox β) (c d : SupportCondition β) :
    ihAction (π.foaHypothesis : Hypothesis c) ≤ ihsAction π c d := fun B =>
  ⟨⟨fun a => Or.inl, fun a h => rfl⟩, ⟨fun L => Or.inl, fun L h => rfl⟩⟩

theorem ihAction_le {π : StructApprox β} {c d : SupportCondition β} (h : c ≤[α] d) :
    ihAction (π.foaHypothesis : Hypothesis c) ≤ ihAction (π.foaHypothesis : Hypothesis d) :=
  by
  refine' fun B => ⟨⟨_, fun a h => rfl⟩, ⟨_, fun L h => rfl⟩⟩
  · intro a ha
    exact Relation.TransGen.trans_left ha h
  · intro a ha
    exact Relation.TransGen.trans_left ha h

theorem ihActionSupports {A : ExtendedIndex β} {L : Litter} (h : InflexibleCoe L A) :
    ((ihAction (π.foaHypothesis : Hypothesis ⟨inr L.toNearLitter, A⟩)).comp
          (h.b.cons (coe_lt h.hδ))).Supports
      h.t :=
  { atom_mem := by
      intro a B ha
      simp only [struct_action.comp_apply, ih_action_atom_map]
      have := mem_reduction_designated_support α h.hδ h.hε h.hδε h.B h.t _ ha
      rw [← h.hL, ← h.hA] at this
      exact this
    litter_mem := by
      intro L B hL
      simp only [struct_action.comp_apply, ih_action_litter_map]
      have := mem_reduction_designated_support α h.hδ h.hε h.hδε h.B h.t _ hL
      rw [← h.hL, ← h.hA] at this
      exact this }

theorem transGen_constrains_of_mem_designatedSupport {A : ExtendedIndex β} {L : Litter}
    {h : InflexibleCoe L A} {γ : Iic α} {δ ε : Iio α} {hδ : (δ : Λ) < γ} {hε : (ε : Λ) < γ}
    (hδε : δ ≠ ε) {C : Path (h.δ : TypeIndex) γ} {t : Tangle δ} {d : SupportCondition h.δ}
    (hd₂ :
      (inr (fMap (Subtype.coe_injective.Ne (Iio.coe_injective.Ne hδε)) t).toNearLitter,
          (C.cons (coe_lt hε)).cons (bot_lt_coe _)) ≤[α]
        d)
    (hd : (d.fst, (h.b.cons (coe_lt h.hδ)).comp d.snd) ≺[α] (inr L.toNearLitter, A))
    {B : ExtendedIndex δ} {a : Atom} (hc : (inl a, B) ∈ (designatedSupport t).carrier) :
    (inl a, (h.b.cons (coe_lt h.hδ)).comp ((C.cons (coe_lt hδ)).comp B)) <[α]
      (inr L.toNearLitter, A) :=
  by
  refine' Relation.TransGen.tail' _ hd
  refine' @refl_trans_gen_constrains_comp _ _ _ _ _ _ (inl a, _) d _ (h.B.cons <| coe_lt h.hδ)
  refine' Relation.ReflTransGen.trans _ hd₂
  exact Relation.ReflTransGen.single (constrains.f_map hδ hε hδε C t _ hc)

-- TODO: move to struct_perm
@[simp]
theorem ConNF.StructPerm.derivative_fst {α β : TypeIndex} (π : StructPerm α) (A : Path α β)
    (N : NearLitter) : (StructPerm.derivative A π • N).fst = StructPerm.derivative A π • N.fst :=
  rfl

theorem toStructPerm_bot :
    (Allowable.toStructPerm : Allowable ⊥ → StructPerm ⊥) = StructPerm.toBotIso.toMonoidHom :=
  rfl

/-- I think it's quite a big deal that this isn't a defeq.
We should probably refactor structural permutations to be like structural approximations,
a function from extended indices to near-litter permutations. -/
@[simp]
theorem toStructPerm_toNearLitterPerm (π : Allowable ⊥) : π.toStructPerm.toNearLitterPerm = π :=
  by
  ext a : 2
  rw [to_struct_perm_bot, struct_perm.coe_to_near_litter_perm]
  simp only [MulEquiv.coe_toMonoidHom, struct_perm.coe_to_bot_iso, struct_perm.of_bot_to_bot]

-- TODO: move earlier and use
theorem completeNearLitterMap_eq' (A : ExtendedIndex β) (N : NearLitter) :
    (π.completeNearLitterMap A N : Set Atom) =
      π.completeNearLitterMap A N.fst.toNearLitter ∆
        (π.completeAtomMap A '' litterSet N.fst ∆ ↑N) :=
  by
  simp only [complete_near_litter_map_eq, near_litter_completion, near_litter_completion_map,
    near_litter_hypothesis_eq, near_litter_approx.coe_largest_sublitter, mem_diff,
    foa_hypothesis_atom_image, near_litter.coe_mk, Subtype.coe_mk, litter.coe_to_near_litter,
    litter.to_near_litter_fst, symmDiff_self, bot_eq_empty, mem_empty_iff_false, false_and_iff,
    Union_neg', not_false_iff, Union_empty, symm_diff_empty]
  ext a : 1
  constructor
  · rintro (⟨ha₁ | ⟨a, ha₁, rfl⟩, ha₂⟩ | ⟨⟨_, ⟨b, rfl⟩, _, ⟨⟨hb₁, hb₂⟩, rfl⟩, ha⟩, ha₂⟩)
    · refine' Or.inl ⟨Or.inl ha₁, _⟩
      simp only [mem_image, not_exists, not_and]
      intro b hb
      by_cases b ∈ (π A).atomPerm.domain
      · rw [complete_atom_map_eq_of_mem_domain h]
        rintro rfl
        exact ha₁.2 ((π A).atomPerm.map_domain h)
      · simp only [mem_Union, mem_singleton_iff, not_exists, and_imp] at ha₂
        exact Ne.symm (ha₂ b hb h)
    · by_cases a ∈ litter_set N.fst
      · refine' Or.inl ⟨Or.inr ⟨a, ⟨h, ha₁.2⟩, rfl⟩, _⟩
        simp only [mem_image, not_exists, not_and]
        intro b hb
        by_cases hb' : b ∈ (π A).atomPerm.domain
        · rw [complete_atom_map_eq_of_mem_domain hb']
          intro hab
          cases (π A).atomPerm.InjOn hb' ha₁.2 hab
          cases hb
          exact hb.2 ha₁.1
          exact hb.2 h
        · simp only [mem_Union, mem_singleton_iff, not_exists, and_imp] at ha₂
          exact Ne.symm (ha₂ b hb hb')
      · refine' Or.inr ⟨⟨a, Or.inr ⟨ha₁.1, h⟩, _⟩, _⟩
        · simp only [complete_atom_map_eq_of_mem_domain ha₁.2]
        rintro (ha | ⟨b, hb₁, hb₂⟩)
        · exact ha.2 ((π A).atomPerm.map_domain ha₁.2)
        · cases (π A).atomPerm.InjOn hb₁.2 ha₁.2 hb₂
          exact h hb₁.1
    · simp only [mem_singleton_iff] at ha
      subst ha
      refine' Or.inr ⟨⟨b, hb₁, rfl⟩, _⟩
      contrapose! ha₂
      cases ha₂
      · exact Or.inl ha₂
      obtain ⟨a, ha₁, ha₂⟩ := ha₂
      by_cases a ∈ N
      · rw [← ha₂]
        exact Or.inr ⟨a, ⟨h, ha₁.2⟩, rfl⟩
      rw [complete_atom_map_eq_of_not_mem_domain hb₂]
      simp only [mem_union, mem_diff, mem_litter_set, sublitter.order_iso_apply_fst_eq,
        near_litter_approx.largest_sublitter_litter]
      refine' Or.inl ⟨_, _⟩
      · suffices b ∈ litter_set N.fst by
          rw [mem_litter_set] at this
          rw [this, complete_litter_map_eq]
        cases hb₁
        · exact hb₁.1
        exfalso
        rw [complete_atom_map_eq_of_not_mem_domain hb₂] at ha₂
        have : π A • a ∈ _ := (π A).atomPerm.map_domain ha₁.2
        rw [ha₂] at this
        exact
          near_litter_approx.not_mem_domain_of_mem_largest_sublitter _
            (sublitter.order_iso_apply_mem _) this
      ·
        exact
          near_litter_approx.not_mem_domain_of_mem_largest_sublitter _
            (sublitter.order_iso_apply_mem _)
  · rintro (⟨ha₁ | ⟨a, ha₁, rfl⟩, ha₂⟩ | ⟨⟨a, ha₁, rfl⟩, ha₂⟩)
    · refine' Or.inl ⟨Or.inl ha₁, _⟩
      simp only [mem_Union, mem_singleton_iff, not_exists, and_imp]
      rintro b hb₁ hb₂ rfl
      exact ha₂ ⟨b, hb₁, rfl⟩
    · refine' Or.inl ⟨_, _⟩
      · by_cases a ∈ N
        · exact Or.inr ⟨a, ⟨h, ha₁.2⟩, rfl⟩
        · simp only [mem_image, not_exists, not_and] at ha₂
          have := ha₂ a (Or.inl ⟨ha₁.1, h⟩)
          rw [complete_atom_map_eq_of_mem_domain ha₁.2] at this
          cases this rfl
      · contrapose! ha₂
        obtain ⟨_, ⟨b, rfl⟩, _, ⟨hb, rfl⟩, ha₂⟩ := ha₂
        simp only [mem_singleton_iff] at ha₂
        rw [ha₂]
        exact ⟨b, hb.1, rfl⟩
    · rw [mem_union, not_or] at ha₂
      by_cases ha : a ∈ litter_set N.fst
      · have : a ∉ (π A).atomPerm.domain := by
          intro h
          refine' ha₂.2 ⟨a, ⟨ha, h⟩, _⟩
          simp only [complete_atom_map_eq_of_mem_domain h]
        refine' Or.inr ⟨_, _⟩
        · exact ⟨_, ⟨a, rfl⟩, _, ⟨⟨ha₁, this⟩, rfl⟩, rfl⟩
        · rintro (h | ⟨b, hb₁, hb₂⟩)
          · exact ha₂.1 h
          simp only [complete_atom_map_eq_of_not_mem_domain this] at hb₂
          have : π A • b ∈ _ := (π A).atomPerm.map_domain hb₁.2
          rw [hb₂] at this
          exact
            near_litter_approx.not_mem_domain_of_mem_largest_sublitter _
              (sublitter.order_iso_apply_mem _) this
      · by_cases a ∈ (π A).atomPerm.domain
        · refine' Or.inl ⟨_, _⟩
          · simp only [complete_atom_map_eq_of_mem_domain h]
            refine' Or.inr ⟨a, ⟨_, h⟩, rfl⟩
            cases ha₁
            cases ha ha₁.1
            exact ha₁.1
          · simp only [mem_Union, mem_singleton_iff, not_exists, and_imp]
            intro b hb₁ hb₂ hab
            rw [complete_atom_map_eq_of_mem_domain h, complete_atom_map_eq_of_not_mem_domain hb₂] at
              hab
            have : π A • a ∈ _ := (π A).atomPerm.map_domain h
            rw [hab] at this
            exact
              near_litter_approx.not_mem_domain_of_mem_largest_sublitter _
                (sublitter.order_iso_apply_mem _) this
        · refine' Or.inr ⟨_, _⟩
          · exact ⟨_, ⟨a, rfl⟩, _, ⟨⟨ha₁, h⟩, rfl⟩, rfl⟩
          rintro (h' | ⟨b, hb₁, hb₂⟩)
          · exact ha₂.1 h'
          simp only [complete_atom_map_eq_of_not_mem_domain h] at hb₂
          have : π A • b ∈ _ := (π A).atomPerm.map_domain hb₁.2
          rw [hb₂] at this
          exact
            near_litter_approx.not_mem_domain_of_mem_largest_sublitter _
              (sublitter.order_iso_apply_mem _) this

theorem completeNearLitterMap_toNearLitter_eq (A : ExtendedIndex β) (L : Litter) :
    (completeNearLitterMap π A L.toNearLitter : Set Atom) =
      litterSet (completeLitterMap π A L) \ (π A).atomPerm.domain ∪
        π A • (litterSet L ∩ (π A).atomPerm.domain) :=
  by
  rw [complete_near_litter_map_eq, near_litter_completion, near_litter.coe_mk, Subtype.coe_mk,
    near_litter_completion_map]
  simp only [near_litter_hypothesis_eq, near_litter_approx.coe_largest_sublitter,
    litter.coe_to_near_litter, mem_diff, litter.to_near_litter_fst, symmDiff_self, bot_eq_empty,
    mem_empty_iff_false, false_and_iff, Union_neg', not_false_iff, Union_empty, symm_diff_empty]
  rw [complete_litter_map_eq]
  rfl

theorem eq_of_mem_completeNearLitterMap {L₁ L₂ : Litter} {A : ExtendedIndex β} (a : Atom)
    (ha₁ : a ∈ π.completeNearLitterMap A L₁.toNearLitter)
    (ha₂ : a ∈ π.completeNearLitterMap A L₂.toNearLitter) :
    π.completeLitterMap A L₁ = π.completeLitterMap A L₂ :=
  by
  rw [← SetLike.mem_coe, complete_near_litter_map_to_near_litter_eq] at ha₁ ha₂
  obtain ⟨ha₁, ha₁'⟩ | ha₁ := ha₁ <;> obtain ⟨ha₂, ha₂'⟩ | ha₂ := ha₂
  · exact eq_of_mem_litter_set_of_mem_litter_set ha₁ ha₂
  · obtain ⟨b, hb, rfl⟩ := ha₂
    cases ha₁' ((π A).atomPerm.map_domain hb.2)
  · obtain ⟨b, hb, rfl⟩ := ha₁
    cases ha₂' ((π A).atomPerm.map_domain hb.2)
  · obtain ⟨b, hb, rfl⟩ := ha₁
    obtain ⟨c, hc, hc'⟩ := ha₂
    cases (π A).atomPerm.InjOn hc.2 hb.2 hc'
    rw [eq_of_mem_litter_set_of_mem_litter_set hb.1 hc.1]

theorem eq_of_completeLitterMap_inter_nonempty {L₁ L₂ : Litter} {A : ExtendedIndex β}
    (h :
      ((π.completeNearLitterMap A L₁.toNearLitter : Set Atom) ∩
          π.completeNearLitterMap A L₂.toNearLitter).Nonempty) :
    π.completeLitterMap A L₁ = π.completeLitterMap A L₂ :=
  by
  obtain ⟨a, ha₁, ha₂⟩ := h
  exact eq_of_mem_complete_near_litter_map a ha₁ ha₂

theorem atom_injective_extends {c d : SupportCondition β} (hcd : (ihsAction π c d).Lawful)
    {a b : Atom} {A : ExtendedIndex β} (hac : (inl a, A) ∈ reflTransConstrained c d)
    (hbc : (inl b, A) ∈ reflTransConstrained c d)
    (h : π.completeAtomMap A a = π.completeAtomMap A b) : a = b :=
  by
  by_cases ha : a ∈ (π A).atomPerm.domain <;> by_cases hb : b ∈ (π A).atomPerm.domain
  · rw [complete_atom_map_eq_of_mem_domain ha, complete_atom_map_eq_of_mem_domain hb] at h
    exact (π A).atomPerm.InjOn ha hb h
  · rw [complete_atom_map_eq_of_mem_domain ha, complete_atom_map_eq_of_not_mem_domain hb] at h
    cases
      (π A).not_mem_domain_of_mem_largestSublitter (subtype.coe_eq_iff.mp h.symm).some
        ((π A).atomPerm.map_domain ha)
  · rw [complete_atom_map_eq_of_not_mem_domain ha, complete_atom_map_eq_of_mem_domain hb] at h
    cases
      (π A).not_mem_domain_of_mem_largestSublitter (subtype.coe_eq_iff.mp h).some
        ((π A).atomPerm.map_domain hb)
  · rw [complete_atom_map_eq_of_not_mem_domain ha, complete_atom_map_eq_of_not_mem_domain hb] at h
    have h₁ := (subtype.coe_eq_iff.mp h).some.1
    have h₂ :=
      (((π A).largestSublitter b.1).OrderIso ((π A).largestSublitter (π.complete_litter_map A b.1))
            ⟨b, (π A).mem_largestSublitter_of_not_mem_domain b hb⟩).Prop.1
    have := (hcd A).litterMap_injective (fst_trans_constrained hac) (fst_trans_constrained hbc) _
    · have := eq_of_sublitter_bijection_apply_eq h this (by rw [this])
      rw [SetLike.coe_mk, SetLike.coe_mk] at this
      exact this
    · refine' near_litter.inter_nonempty_of_fst_eq_fst _
      simp only [ihs_action_litter_map, complete_near_litter_map_fst_eq]
      exact eq_of_mem_litter_set_of_mem_litter_set h₁ h₂

def InOut (π : NearLitterPerm) (a : Atom) (L : Litter) : Prop :=
  Xor' (a.1 = L) ((π • a).1 = π • L)

theorem inOut_def {π : NearLitterPerm} {a : Atom} {L : Litter} :
    InOut π a L ↔ Xor' (a.1 = L) ((π • a).1 = π • L) :=
  Iff.rfl

structure ConNF.NearLitterPerm.Biexact (π π' : NearLitterPerm) (atoms : Set Atom)
    (litters : Set Litter) : Prop where
  smul_eq_smul_atom : ∀ a ∈ atoms, π • a = π' • a
  smul_eq_smul_litter : ∀ L ∈ litters, π • L = π' • L
  left_exact : ∀ L ∈ litters, ∀ a, InOut π a L → π • a = π' • a
  right_exact : ∀ L ∈ litters, ∀ a, InOut π' a L → π • a = π' • a

@[simp]
theorem xor'_elim_left {a b : Prop} (h : a) : Xor' a b ↔ ¬b := by unfold Xor' <;> tauto

@[simp]
theorem xor'_elim_right {a b : Prop} (h : b) : Xor' a b ↔ ¬a := by unfold Xor' <;> tauto

@[simp]
theorem xor'_elim_not_left {a b : Prop} (h : ¬a) : Xor' a b ↔ b := by unfold Xor' <;> tauto

@[simp]
theorem xor'_elim_not_right {a b : Prop} (h : ¬b) : Xor' a b ↔ a := by unfold Xor' <;> tauto

theorem ConNF.NearLitterPerm.Biexact.atoms {π π' : NearLitterPerm} (s : Set Atom)
    (hs : ∀ a ∈ s, π • a = π' • a) : NearLitterPerm.Biexact π π' s ∅ :=
  ⟨hs, fun L => False.elim, fun L => False.elim, fun L => False.elim⟩

theorem ConNF.NearLitterPerm.Biexact.litter {π π' : NearLitterPerm} (L : Litter)
    (hL : π • L = π' • L) (hL₁ : ∀ a, InOut π a L → π • a = π' • a)
    (hL₂ : ∀ a, InOut π' a L → π • a = π' • a) : NearLitterPerm.Biexact π π' ∅ {L} :=
  ⟨fun a ha => ha.elim, fun L' hL' => by cases hL' <;> exact hL, fun L' hL' => by
    cases hL' <;> exact hL₁, fun L' hL' => by cases hL' <;> exact hL₂⟩

theorem ConNF.NearLitterPerm.Biexact.symm {π π' : NearLitterPerm} {atoms : Set Atom}
    {litters : Set Litter} (h : NearLitterPerm.Biexact π π' atoms litters) :
    NearLitterPerm.Biexact π' π atoms litters :=
  ⟨fun a ha => (h.smul_eq_smul_atom a ha).symm, fun L hL => (h.smul_eq_smul_litter L hL).symm,
    fun L hL a ha => (h.right_exact L hL a ha).symm, fun L hL a ha => (h.left_exact L hL a ha).symm⟩

theorem ConNF.NearLitterPerm.Biexact.union {π π' : NearLitterPerm} {s₁ s₂ : Set Atom}
    {t₁ t₂ : Set Litter} (h₁ : NearLitterPerm.Biexact π π' s₁ t₁)
    (h₂ : NearLitterPerm.Biexact π π' s₂ t₂) : NearLitterPerm.Biexact π π' (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  ⟨fun a ha => ha.elim (h₁.smul_eq_smul_atom a) (h₂.smul_eq_smul_atom a), fun L hL =>
    hL.elim (h₁.smul_eq_smul_litter L) (h₂.smul_eq_smul_litter L), fun L hL =>
    hL.elim (h₁.left_exact L) (h₂.left_exact L), fun L hL =>
    hL.elim (h₁.right_exact L) (h₂.right_exact L)⟩

theorem ConNF.NearLitterPerm.Biexact.smul_litter_subset {π π' : NearLitterPerm} {atoms : Set Atom}
    {litters : Set Litter} (h : NearLitterPerm.Biexact π π' atoms litters) (L : Litter)
    (hL : L ∈ litters) : (π • L.toNearLitter : Set Atom) ⊆ π' • L.toNearLitter :=
  by
  rintro _ ⟨a, ha, rfl⟩
  simp only [litter.coe_to_near_litter, mem_litter_set] at ha
  by_cases h' : (π • a).1 = π • L
  by_cases h'' : (π'⁻¹ • π • a).1 = L
  · refine' ⟨_, h'', _⟩
    rw [smul_inv_smul]
  · have := h.right_exact L hL _ (Or.inr ⟨_, h''⟩)
    · rw [smul_inv_smul, smul_left_cancel_iff, inv_smul_eq_iff] at this
      rw [this]
      exact ⟨a, ha, rfl⟩
    · rw [smul_inv_smul, h', h.smul_eq_smul_litter L hL]
  · rw [h.left_exact L hL a (Or.inl ⟨ha, h'⟩)]
    simp only [litter.coe_to_near_litter, smul_mem_smul_set_iff, mem_litter_set]
    exact ha

theorem ConNF.NearLitterPerm.Biexact.smul_litter {π π' : NearLitterPerm} {atoms : Set Atom}
    {litters : Set Litter} (h : NearLitterPerm.Biexact π π' atoms litters) (L : Litter)
    (hL : L ∈ litters) : π • L.toNearLitter = π' • L.toNearLitter :=
  by
  refine' SetLike.coe_injective _
  refine' subset_antisymm _ _
  exact h.smul_litter_subset L hL
  exact h.symm.smul_litter_subset L hL

theorem ConNF.NearLitterPerm.Biexact.smul_nearLitter {π π' : NearLitterPerm} {atoms : Set Atom}
    {litters : Set Litter} (h : NearLitterPerm.Biexact π π' atoms litters) (N : NearLitter)
    (hN : N.1 ∈ litters) (hN' : litterSet N.1 ∆ N ⊆ atoms) : π • N = π' • N :=
  by
  refine' SetLike.coe_injective _
  change _ • _ = _ • _
  conv_lhs => rw [near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul]
  conv_rhs => rw [near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul]
  refine' congr_arg₂ _ (congr_arg SetLike.coe (h.smul_litter N.1 hN)) _
  ext a : 1
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [h.smul_eq_smul_atom b (hN' hb)]
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    rw [← h.smul_eq_smul_atom b (hN' hb)]
    exact ⟨b, hb, rfl⟩

/- `in_out` is just another way to quantify exceptions, focusing on a slightly different litter.
Basically `in_out` looks only at images not preimages. -/
theorem isException_of_inOut {π : NearLitterPerm} {a : Atom} {L : Litter} :
    InOut π a L → π.IsException a ∨ π.IsException (π • a) :=
  by
  rintro (⟨rfl, ha⟩ | ha)
  · refine' Or.inr (Or.inr _)
    intro h
    rw [mem_litter_set, eq_inv_smul_iff] at h
    rw [← h, inv_smul_smul] at ha
    exact ha rfl
  · refine' Or.inl (Or.inl _)
    rw [mem_litter_set, ha.1, smul_left_cancel_iff]
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
    (h : Biexact π.toStructPerm π'.toStructPerm c) : π • c = π' • c :=
  by
  revert h
  refine' WellFounded.induction (constrains_wf α β) c _
  clear c
  intro c ih h
  obtain ⟨a | N, A⟩ := c <;> refine' Prod.ext _ rfl
  · change inl _ = inl _
    simp only
    exact h.smul_eq_smul_atom A a Relation.ReflTransGen.refl
  change inr _ = inr _
  simp only
  by_cases hL : N.is_litter
  swap
  · have :=
      ih _ (constrains.near_litter N (near_litter.not_is_litter hL) A)
        (h.constrains (refl_trans_gen_near_litter Relation.ReflTransGen.refl))
    change (inr _, _) = (inr _, _) at this
    simp only [Prod.mk.inj_iff, eq_self_iff_true, and_true_iff] at this
    refine' SetLike.coe_injective _
    refine' (near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul _ _).trans _
    refine' Eq.trans _ (near_litter_perm.smul_near_litter_eq_smul_symm_diff_smul _ _).symm
    refine' congr_arg₂ _ (congr_arg SetLike.coe this) _
    ext a : 1
    constructor
    · rintro ⟨b, hb, rfl⟩
      have : (inl _, _) = (inl _, _) :=
        ih _ (constrains.symm_diff N b hb A)
          (h.constrains (Relation.ReflTransGen.single <| constrains.symm_diff N b hb A))
      simp only [Prod.mk.inj_iff, eq_self_iff_true, and_true_iff] at this
      exact ⟨b, hb, this.symm⟩
    · rintro ⟨b, hb, rfl⟩
      have : (inl _, _) = (inl _, _) :=
        ih _ (constrains.symm_diff N b hb A)
          (h.constrains (Relation.ReflTransGen.single <| constrains.symm_diff N b hb A))
      simp only [Prod.mk.inj_iff, eq_self_iff_true, and_true_iff] at this
      exact ⟨b, hb, this⟩
  obtain ⟨L, rfl⟩ := hL.exists_litter_eq
  suffices
    struct_perm.derivative A π.to_struct_perm • L = struct_perm.derivative A π'.to_struct_perm • L
    by exact h.exact _ _ Relation.ReflTransGen.refl this
  obtain hL | hL := flexible_cases α L A
  swap
  · exact h.smul_eq_smul_litter A L Relation.ReflTransGen.refl hL
  induction' hL with γ δ ε hδ hε hδε B t γ ε hε B a
  · rw [struct_perm.derivative_cons, struct_perm.derivative_bot_smul, struct_perm.derivative_cons]
    rw [allowable.derivative_to_struct_perm (show Path (β : type_index) (γ : Iic_index α) from _)]
    refine'
      (to_struct_perm_smul_f_map (γ : Iic_index α) δ ε (coe_lt hδ) (coe_lt hε)
            (Iio.coe_injective.ne hδε) _ _).trans
        _
    rw [struct_perm.derivative_cons, struct_perm.derivative_bot_smul, struct_perm.derivative_cons]
    rw [allowable.derivative_to_struct_perm (show Path (β : type_index) (γ : Iic_index α) from _)]
    refine'
      Eq.trans _
        (to_struct_perm_smul_f_map (γ : Iic_index α) δ ε (coe_lt hδ) (coe_lt hε)
            (Iio.coe_injective.ne hδε) _ _).symm
    refine' congr_arg _ _
    rw [← inv_smul_eq_iff, smul_smul]
    refine' (designated_support t).Supports _ _
    intro c hc
    rw [mul_smul, inv_smul_eq_iff]
    rw [← allowable.to_struct_perm_smul, ← allowable.to_struct_perm_smul, ←
      allowable.derivative_cons_apply, ← allowable.derivative_cons_apply, ←
      allowable.derivative_to_struct_perm, ← allowable.derivative_to_struct_perm]
    have := ih (c.fst, (B.cons <| coe_lt hδ).comp c.snd) _ _
    · refine' Prod.ext _ rfl
      apply_fun Prod.fst at this
      change _ • _ = _ • _
      rw [struct_perm.derivative_derivative, struct_perm.derivative_derivative]
      exact this
    · exact constrains.f_map _ _ _ _ _ _ hc
    · refine' h.constrains (Relation.ReflTransGen.single _)
      exact constrains.f_map _ _ _ _ _ _ hc
  · rw [struct_perm.derivative_cons, struct_perm.derivative_bot_smul, struct_perm.derivative_cons]
    rw [allowable.derivative_to_struct_perm (show Path (β : type_index) (γ : Iic_index α) from _)]
    refine'
      (to_struct_perm_smul_f_map (γ : Iic_index α) ⊥ ε (bot_lt_coe _) (coe_lt hε)
            Iio_index.bot_ne_coe _ _).trans
        _
    rw [struct_perm.derivative_cons, struct_perm.derivative_bot_smul, struct_perm.derivative_cons]
    rw [allowable.derivative_to_struct_perm (show Path (β : type_index) (γ : Iic_index α) from _)]
    refine'
      Eq.trans _
        (to_struct_perm_smul_f_map (γ : Iic_index α) ⊥ ε (bot_lt_coe _) (coe_lt hε)
            Iio_index.bot_ne_coe _ _).symm
    refine' congr_arg _ _
    rw [← allowable.derivative_cons_apply, ← allowable.derivative_cons_apply]
    have := ih (inl a, B.cons <| bot_lt_coe _) _ _
    · change (inl _, _) = (inl _, _) at this
      simp only [Prod.mk.inj_iff, eq_self_iff_true, and_true_iff] at this
      rw [allowable.derivative_to_struct_perm
          (show Path (β : type_index) (⊥ : Iic_index α) from _)] at
        this
      rw [allowable.derivative_to_struct_perm
          (show Path (β : type_index) (⊥ : Iic_index α) from _)] at
        this
      rw [allowable.to_struct_perm_smul] at this
      rw [allowable.to_struct_perm_smul] at this
      dsimp only
      convert this using 2 <;> · rw [to_struct_perm_to_near_litter_perm]; rfl
    · exact constrains.f_map_bot _ _ _
    · refine' h.constrains (Relation.ReflTransGen.single _)
      exact constrains.f_map_bot _ _ _

theorem Biexact.smul_eq_smul_nearLitter {β : Iio α} {π π' : Allowable β} {A : ExtendedIndex β}
    {N : NearLitter} (h : Biexact π.toStructPerm π'.toStructPerm (inr N, A)) :
    StructPerm.derivative A π.toStructPerm • N = StructPerm.derivative A π'.toStructPerm • N :=
  by
  have : (inr _, _) = (inr _, _) := h.smul_eq_smul
  rw [Prod.mk.inj_iff] at this
  exact inr_injective this.1

theorem mem_dom_of_exactlyApproximates {β : Iio α} {π₀ : StructApprox β} {π : StructPerm β}
    (hπ : π₀.ExactlyApproximates π) {A : ExtendedIndex β} {a : Atom} {L : Litter}
    (h : InOut (StructPerm.ofBot <| StructPerm.derivative A π) a L) : a ∈ (π₀ A).atomPerm.domain :=
  by
  obtain h | h := is_exception_of_in_out h
  · exact (hπ A).exception_mem _ h
  · have h₁ := (hπ A).exception_mem _ h
    have := (hπ A).symm_map_atom _ h₁
    rw [inv_smul_smul] at this
    rw [← this]
    exact (π₀ A).atomPerm.symm.map_domain h₁

/--
We can prove that `map_flexible` holds at any `constrained_action` without any `lawful` hypothesis.
-/
theorem constrainedActionCompMapFlexible (hπf : π.Free) {γ : Iio α} {s : Set (SupportCondition β)}
    {hs : Small s} (A : Path (β : TypeIndex) γ) : ((constrainedAction π s hs).comp A).MapFlexible :=
  by
  rintro L B ⟨c, hc, hL₁⟩ hL₂
  simp only [struct_action.comp_apply, constrained_action_litter_map,
    foa_hypothesis_near_litter_image]
  rw [complete_near_litter_map_fst_eq]
  obtain hL₃ | (⟨⟨hL₃⟩⟩ | ⟨⟨hL₃⟩⟩) := flexible_cases' _ L (A.comp B)
  · rw [complete_litter_map_eq_of_flexible hL₃]
    refine' near_litter_approx.flexible_completion_smul_flexible _ _ _ _ _ hL₂
    intro L' hL'
    exact flexible_of_comp_flexible (hπf (A.comp B) L' hL')
  · rw [complete_litter_map_eq_of_inflexible_bot hL₃]
    obtain ⟨δ, ε, hε, C, a, rfl, hC⟩ := hL₃
    contrapose hL₂
    rw [not_flexible_iff] at hL₂ ⊢
    rw [inflexible_iff] at hL₂
    obtain ⟨δ', ε', ζ', hε', hζ', hεζ', C', t', h', rfl⟩ | ⟨δ', ε', hε', C', a', h', rfl⟩ := hL₂
    · have := congr_arg litter.β h'
      simpa only [f_map_β, bot_ne_coe] using this
    · rw [path.comp_cons, path.comp_cons] at hC
      cases Subtype.coe_injective (coe_eq_coe.mp (path.obj_eq_of_cons_eq_cons hC))
      exact inflexible.mk_bot _ _ _
  · rw [complete_litter_map_eq_of_inflexible_coe' hL₃]
    split_ifs
    swap
    · exact hL₂
    obtain ⟨δ, ε, ζ, hε, hζ, hεζ, C, t, rfl, hC⟩ := hL₃
    contrapose hL₂
    rw [not_flexible_iff] at hL₂ ⊢
    rw [inflexible_iff] at hL₂
    obtain ⟨δ', ε', ζ', hε', hζ', hεζ', C', t', h', rfl⟩ | ⟨δ', ε', hε', C', a', h', rfl⟩ := hL₂
    · rw [path.comp_cons, path.comp_cons] at hC
      cases Subtype.coe_injective (coe_eq_coe.mp (path.obj_eq_of_cons_eq_cons hC))
      have hC := (path.heq_of_cons_eq_cons hC).Eq
      cases Subtype.coe_injective (coe_eq_coe.mp (path.obj_eq_of_cons_eq_cons hC))
      refine' inflexible.mk_coe hε _ _ _ _
    · have := congr_arg litter.β h'
      simpa only [f_map_β, bot_ne_coe] using this

theorem ihActionCompMapFlexible (hπf : π.Free) {γ : Iio α} (c : SupportCondition β)
    (A : Path (β : TypeIndex) γ) :
    ((ihAction (π.foaHypothesis : Hypothesis c)).comp A).MapFlexible :=
  by
  rw [ih_action_eq_constrained_action]
  exact constrained_action_comp_map_flexible hπf A

theorem ihsActionCompMapFlexible (hπf : π.Free) {γ : Iio α} (c d : SupportCondition β)
    (A : Path (β : TypeIndex) γ) : ((ihsAction π c d).comp A).MapFlexible :=
  by
  rw [ihs_action_eq_constrained_action]
  exact constrained_action_comp_map_flexible hπf A

theorem completeLitterMapFlexible (hπf : π.Free) {A : ExtendedIndex β} {L : Litter}
    (h : Flexible α L A) : Flexible α (π.completeLitterMap A L) A :=
  by
  rw [complete_litter_map_eq_of_flexible h]
  exact near_litter_approx.flexible_completion_smul_flexible _ _ _ (hπf A) _ h

noncomputable theorem completeLitterMapInflexibleBot {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleBot L A) : InflexibleBot (π.completeLitterMap A L) A :=
  by
  rw [complete_litter_map_eq_of_inflexible_bot h]
  obtain ⟨γ, ε, hγε, B, a, rfl, rfl⟩ := h
  exact ⟨_, _, _, _, _, rfl, rfl⟩

noncomputable theorem completeLitterMapInflexibleCoe (hπf : π.Free) {c d : SupportCondition β}
    (hcd : (ihsAction π c d).Lawful) {A : ExtendedIndex β} {L : Litter} (h : InflexibleCoe L A)
    (hL : (inr L.toNearLitter, A) ∈ reflTransConstrained c d) :
    InflexibleCoe (π.completeLitterMap A L) A :=
  by
  rw [complete_litter_map_eq_of_inflexible_coe h]
  obtain ⟨γ, δ, ε, hδ, hε, hδε, B, a, rfl, rfl⟩ := h
  exact ⟨_, _, _, hδ, hε, hδε, _, _, rfl, rfl⟩
  · refine' (hcd.le _).comp _
    cases hL
    · exact (ih_action_le hL).trans (ih_action_le_ihs_action _ _ _)
    · rw [ihs_action_symm]
      exact (ih_action_le hL).trans (ih_action_le_ihs_action _ _ _)
  · exact ih_action_comp_map_flexible hπf _ _

theorem completeLitterMapFlexible' (hπf : π.Free) {c d : SupportCondition β}
    (hcd : (ihsAction π c d).Lawful) {A : ExtendedIndex β} {L : Litter}
    (hL : (inr L.toNearLitter, A) ∈ reflTransConstrained c d)
    (h : Flexible α (π.completeLitterMap A L) A) : Flexible α L A :=
  by
  obtain h' | h' | h' := flexible_cases' β L A
  · exact h'
  · have := complete_litter_map_inflexible_bot h'.some
    rw [flexible_iff_not_inflexible_bot_coe] at h
    cases h.1.False this
  · have := complete_litter_map_inflexible_coe hπf hcd h'.some hL
    rw [flexible_iff_not_inflexible_bot_coe] at h
    cases h.2.False this

theorem completeLitterMap_flexible_iff (hπf : π.Free) {c d : SupportCondition β}
    (hcd : (ihsAction π c d).Lawful) {A : ExtendedIndex β} {L : Litter}
    (hL : (inr L.toNearLitter, A) ∈ reflTransConstrained c d) :
    Flexible α (π.completeLitterMap A L) A ↔ Flexible α L A :=
  ⟨completeLitterMapFlexible' hπf hcd hL, completeLitterMapFlexible hπf⟩

noncomputable theorem completeLitterMapInflexibleBot' (hπf : π.Free) {c d : SupportCondition β}
    (hcd : (ihsAction π c d).Lawful) {A : ExtendedIndex β} {L : Litter}
    (hL : (inr L.toNearLitter, A) ∈ reflTransConstrained c d)
    (h : InflexibleBot (π.completeLitterMap A L) A) : InflexibleBot L A :=
  by
  refine' Nonempty.some _
  obtain h' | h' | h' := flexible_cases' β L A
  · have := complete_litter_map_flexible hπf h'
    rw [flexible_iff_not_inflexible_bot_coe] at this
    cases this.1.False h
  · exact h'
  · have := complete_litter_map_inflexible_coe hπf hcd h'.some hL
    cases inflexible_bot_inflexible_coe h this

theorem completeLitterMap_inflexibleBot_iff (hπf : π.Free) {c d : SupportCondition β}
    (hcd : (ihsAction π c d).Lawful) {A : ExtendedIndex β} {L : Litter}
    (hL : (inr L.toNearLitter, A) ∈ reflTransConstrained c d) :
    Nonempty (InflexibleBot (π.completeLitterMap A L) A) ↔ Nonempty (InflexibleBot L A) :=
  ⟨fun ⟨h⟩ => ⟨completeLitterMapInflexibleBot' hπf hcd hL h⟩, fun ⟨h⟩ =>
    ⟨completeLitterMapInflexibleBot h⟩⟩

noncomputable theorem completeLitterMapInflexibleCoe' (hπf : π.Free) {c d : SupportCondition β}
    (hcd : (ihsAction π c d).Lawful) {A : ExtendedIndex β} {L : Litter}
    (hL : (inr L.toNearLitter, A) ∈ reflTransConstrained c d)
    (h : InflexibleCoe (π.completeLitterMap A L) A) : InflexibleCoe L A :=
  by
  refine' Nonempty.some _
  obtain h' | h' | h' := flexible_cases' β L A
  · have := complete_litter_map_flexible hπf h'
    rw [flexible_iff_not_inflexible_bot_coe] at this
    cases this.2.False h
  · have := complete_litter_map_inflexible_bot h'.some
    cases inflexible_bot_inflexible_coe this h
  · exact h'

theorem completeLitterMap_inflexibleCoe_iff (hπf : π.Free) {c d : SupportCondition β}
    (hcd : (ihsAction π c d).Lawful) {A : ExtendedIndex β} {L : Litter}
    (hL : (inr L.toNearLitter, A) ∈ reflTransConstrained c d) :
    Nonempty (InflexibleCoe (π.completeLitterMap A L) A) ↔ Nonempty (InflexibleCoe L A) :=
  ⟨fun ⟨h⟩ => ⟨completeLitterMapInflexibleCoe' hπf hcd hL h⟩, fun ⟨h⟩ =>
    ⟨completeLitterMapInflexibleCoe hπf hcd h hL⟩⟩

theorem constrainedAction_coherent_precise' (hπf : π.Free) {γ : Iio α} (A : Path (β : TypeIndex) γ)
    (N : ExtendedIndex γ × NearLitter) (s : Set (SupportCondition β)) (hs : Small s)
    (hc : ∃ c : SupportCondition β, c ∈ s ∧ (inr N.2, A.comp N.1) ≤[α] c)
    (hπ : ((constrainedAction π s hs).comp A).Lawful) (ρ : Allowable γ)
    (h : (((constrainedAction π s hs).comp A).rc hπ).ExactlyApproximates ρ.toStructPerm) :
    completeNearLitterMap π (A.comp N.1) N.2 = StructPerm.derivative N.1 ρ.toStructPerm • N.2 :=
  by
  revert hc
  refine'
    WellFounded.induction (InvImage.wf _ (Relation.TransGen.isWellFounded (constrains α γ)).wf) N _
  exact fun N : extended_index γ × near_litter => (inr N.2, N.1)
  clear N
  rintro ⟨B, N⟩ ih ⟨c, hc₁, hc₂⟩
  dsimp only at *
  have hdom : ((((constrained_action π s hs).comp A B).refine (hπ B)).litterMap N.fst).Dom :=
    ⟨c, hc₁, refl_trans_gen_near_litter hc₂⟩
  suffices
    complete_litter_map π (A.comp B) N.fst = struct_perm.derivative B ρ.to_struct_perm • N.fst
    by
    refine' SetLike.coe_injective _
    refine'
      Eq.trans _
        (near_litter_action.smul_near_litter_eq_of_precise_at _ (h B) hdom
            (near_litter_action.refine_precise _) this.symm).symm
    rw [complete_near_litter_map_eq' (A.comp B) N]
    simp only [struct_action.refine_apply, struct_action.refine_litter_map,
      foa_hypothesis_near_litter_image, struct_perm.of_bot_smul]
    simp only [struct_action.comp_apply, constrained_action_litter_map, symmDiff_right_inj]
    ext a : 1
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine' ⟨a, ha, _⟩
      refine' ((h B).map_atom a _).symm.trans _
      · refine' Or.inl (Or.inl (Or.inl (Or.inl _)))
        exact ⟨c, hc₁, Relation.ReflTransGen.head (constrains.symm_diff N a ha _) hc₂⟩
      · rw [struct_action.rc_smul_atom_eq]
        rfl
        exact ⟨c, hc₁, Relation.ReflTransGen.head (constrains.symm_diff N a ha _) hc₂⟩
    · rintro ⟨a, ha, rfl⟩
      refine' ⟨a, ha, _⟩
      refine' Eq.trans _ ((h B).map_atom a _)
      · rw [struct_action.rc_smul_atom_eq]
        rfl
        exact ⟨c, hc₁, Relation.ReflTransGen.head (constrains.symm_diff N a ha _) hc₂⟩
      · refine' Or.inl (Or.inl (Or.inl (Or.inl _)))
        exact ⟨c, hc₁, Relation.ReflTransGen.head (constrains.symm_diff N a ha _) hc₂⟩
  have hc₂' := refl_trans_gen_near_litter hc₂
  generalize hNL : N.fst = L
  rw [hNL] at hdom hc₂'
  obtain hL | ⟨⟨hL⟩⟩ | ⟨⟨hL⟩⟩ := flexible_cases' (γ : Iic α) L B
  · refine' Eq.trans _ ((h B).map_litter L _)
    · rw [struct_action.rc_smul_litter_eq]
      rw [near_litter_action.flexible_litter_perm_apply_eq]
      swap; exact hdom
      swap; exact hL
      exact (near_litter_action.rough_litter_map_or_else_of_dom _ hdom).symm
    · refine' Or.inl (Or.inl _)
      refine' ⟨hdom, hL⟩
  · rw [complete_litter_map_eq_of_inflexible_bot (hL.comp A)]
    obtain ⟨δ, ε, hε, C, a, rfl, rfl⟩ := hL
    rw [struct_perm.derivative_cons]
    refine' Eq.trans _ (struct_perm.derivative_bot_smul _ _).symm
    rw [struct_perm.derivative_cons]
    rw [allowable.derivative_to_struct_perm (show Path (γ : type_index) (δ : Iic_index α) from C)]
    refine'
      Eq.trans _
        (to_struct_perm_smul_f_map (δ : Iic_index α) ⊥ ε (bot_lt_coe _) _ _
            (allowable.derivative (show Path (γ : type_index) (δ : Iic_index α) from _) ρ) a).symm
    · intro h; cases h
    refine' congr_arg _ _
    rw [← allowable.derivative_cons_apply]
    refine'
      Eq.trans _
        (((h <| C.cons (bot_lt_coe _)).map_atom a
              (Or.inl
                (Or.inl
                  (Or.inl
                    (Or.inl
                      ⟨c, hc₁,
                        Relation.ReflTransGen.head (constrains.f_map_bot hε _ _) hc₂'⟩))))).trans
          _)
    · rw [struct_action.rc_smul_atom_eq]
      rfl
      exact ⟨c, hc₁, Relation.ReflTransGen.head (constrains.f_map_bot hε _ _) hc₂'⟩
    · have :=
        allowable.to_struct_perm_smul
          (allowable.derivative
            (show Path (γ : type_index) (⊥ : Iic_index α) from C.cons (bot_lt_coe _)) ρ)
          a
      rw [← allowable.derivative_to_struct_perm] at this
      refine' this.trans _
      congr
      ext π a : 4
      change π.to_struct_perm.to_near_litter_perm.atom_perm a = π.atom_perm a
      rw [to_struct_perm_to_near_litter_perm]
  · rw [complete_litter_map_eq_of_inflexible_coe (hL.comp A)]
    swap
    · rw [inflexible_coe.comp_B, ← path.comp_cons, ← struct_action.comp_comp]
      refine' struct_action.lawful.comp _ _
      refine' hπ.le (struct_action.le_comp (ih_action_le_constrained_action _ _) _)
      exact ⟨c, hc₁, hc₂'⟩
    swap
    · rw [inflexible_coe.comp_B, ← path.comp_cons]
      exact ih_action_comp_map_flexible hπf _ _
    obtain ⟨δ, ε, ζ, hε, hζ, hεζ, C, t, rfl, rfl⟩ := hL
    rw [struct_perm.derivative_cons]
    refine' Eq.trans _ (struct_perm.derivative_bot_smul _ _).symm
    rw [struct_perm.derivative_cons]
    rw [allowable.derivative_to_struct_perm (show Path (γ : type_index) (δ : Iic_index α) from C)]
    refine'
      Eq.trans _
        (to_struct_perm_smul_f_map (δ : Iic_index α) ε ζ (coe_lt hε) _ _
            (allowable.derivative (show Path (γ : type_index) (δ : Iic_index α) from C) ρ) t).symm
    · intro h
      refine' hεζ (Subtype.ext _)
      have := congr_arg Subtype.val h
      exact coe_injective this
    refine' congr_arg _ _
    rw [← allowable.derivative_cons_apply, ← inv_smul_eq_iff, smul_smul]
    refine' (designated_support t).Supports _ _
    intro c hct
    rw [mul_smul, inv_smul_eq_iff]
    obtain ⟨a | M, D⟩ := c
    · refine' Prod.ext _ rfl
      change inl _ = inl _
      simp only
      rw [← allowable.derivative_to_struct_perm, struct_perm.derivative_derivative]
      refine' Eq.trans _ ((h _).map_atom a _)
      refine'
        (((ih_action _).hypothesisedAllowable_exactlyApproximates
                    ⟨δ, ε, ζ, hε, hζ, hεζ, A.comp C, t, rfl, rfl⟩ _ _ D).map_atom
                a _).symm.trans
          _
      · refine' Or.inl (Or.inl (Or.inl (Or.inl _)))
        exact Relation.TransGen.single (constrains.f_map _ _ _ _ _ _ hct)
      · rw [struct_action.rc_smul_atom_eq, struct_action.rc_smul_atom_eq]
        · simp only [struct_action.comp_apply, ih_action_atom_map, foa_hypothesis_atom_image,
            constrained_action_atom_map]
          simp_rw [← path.comp_cons]
          rw [path.comp_assoc]
        · refine' ⟨c, hc₁, Relation.ReflTransGen.head _ hc₂'⟩
          exact constrains_comp (constrains.f_map _ _ _ _ _ _ hct) A
        · simp only [struct_action.comp_apply, ih_action_atom_map]
          simp_rw [← path.comp_cons]
          rw [path.comp_assoc]
          exact Relation.TransGen.single (constrains_comp (constrains.f_map _ _ _ _ _ _ hct) A)
      · refine' Or.inl (Or.inl (Or.inl (Or.inl _)))
        refine' ⟨c, hc₁, Relation.ReflTransGen.head _ hc₂'⟩
        exact constrains_comp (constrains.f_map _ _ _ _ _ _ hct) A
    · refine' Prod.ext _ rfl
      change inr _ = inr _
      simp only
      refine' biexact.smul_eq_smul_near_litter _
      constructor
      · intro E a ha
        have haN :
          (inl a, (C.cons <| coe_lt hε).comp E) <[α]
            (inr N.fst.to_near_litter, (C.cons <| coe_lt hζ).cons (bot_lt_coe _)) :=
          by
          simp only [hNL]
          refine' Relation.TransGen.tail' _ (constrains.f_map hε _ _ _ _ _ hct)
          exact refl_trans_gen_constrains_comp ha _
        refine'
          ((struct_action.hypothesised_allowable_exactly_approximates _
                      ⟨δ, ε, ζ, hε, hζ, hεζ, A.comp C, t, rfl, rfl⟩ _ _ _).map_atom
                  _ _).symm.trans
            _
        · refine' Or.inl (Or.inl (Or.inl (Or.inl _)))
          change _ <[α] _
          simp only [← hNL, path.comp_assoc, ← path.comp_cons]
          exact trans_gen_constrains_comp haN _
        have := (h _).map_atom a _
        rw [struct_action.rc_smul_atom_eq] at this ⊢
        swap
        · change _ <[α] _
          simp only [← hNL, path.comp_assoc, ← path.comp_cons]
          exact trans_gen_constrains_comp haN _
        swap
        · refine' ⟨c, hc₁, trans _ hc₂⟩
          swap
          refine' Relation.ReflTransGen.trans (trans_gen_constrains_comp haN _).to_reflTransGen _
          exact refl_trans_gen_near_litter Relation.ReflTransGen.refl
        · simp only [struct_action.comp_apply, ih_action_atom_map, foa_hypothesis_atom_image,
            constrained_action_atom_map, struct_perm.of_bot_smul] at this ⊢
          rw [← allowable.derivative_to_struct_perm, struct_perm.derivative_derivative, ← this, ←
            path.comp_assoc, path.comp_cons]
        · refine' Or.inl (Or.inl (Or.inl (Or.inl _)))
          refine' ⟨c, hc₁, trans _ hc₂⟩
          simp only [← hNL, path.comp_assoc, ← path.comp_cons]
          exact refl_trans_gen_constrains_comp (trans_gen_near_litter haN).to_reflTransGen _
      · intro E L hL₁ hL₂
        rw [← struct_perm.of_bot_smul]
        refine'
          ((struct_action.hypothesised_allowable_exactly_approximates _
                      ⟨δ, ε, ζ, hε, hζ, hεζ, A.comp C, t, rfl, rfl⟩ _ _ _).map_litter
                  _ _).symm.trans
            _
        · refine' Or.inl (Or.inl ⟨_, hL₂⟩)
          refine' Relation.TransGen.trans_right (refl_trans_gen_constrains_comp hL₁ _) _
          exact Relation.TransGen.single (constrains.f_map _ _ _ _ _ _ hct)
        have hLN :
          (inr L.to_near_litter, (C.cons <| coe_lt hε).comp E) <[α]
            (inr N.fst.to_near_litter, (C.cons <| coe_lt hζ).cons (bot_lt_coe _)) :=
          by
          simp only [hNL]
          refine' Relation.TransGen.tail' _ (constrains.f_map hε _ _ _ _ _ hct)
          exact refl_trans_gen_constrains_comp hL₁ _
        rw [struct_action.rc_smul_litter_eq, near_litter_action.flexible_litter_perm_apply_eq,
          near_litter_action.rough_litter_map_or_else_of_dom]
        simp only [struct_action.comp_apply, struct_action.refine_apply,
          near_litter_action.refine_litter_map, ih_action_litter_map,
          foa_hypothesis_near_litter_image]
        specialize
          ih ((C.cons <| coe_lt hε).comp E, L.to_near_litter) (trans_gen_near_litter hLN)
            ⟨c, hc₁,
              trans (trans_gen_constrains_comp (trans_gen_near_litter hLN) _).to_reflTransGen hc₂⟩
        · dsimp only at ih
          rw [← path.comp_assoc, path.comp_cons] at ih
          rw [ih]
          simp only [struct_perm.derivative_fst, litter.to_near_litter_fst]
          rw [← allowable.derivative_to_struct_perm, struct_perm.derivative_derivative]
        · refine' trans_gen_near_litter _
          simp only [← hNL, path.comp_assoc, ← path.comp_cons]
          exact trans_gen_constrains_comp hLN _
        · refine' trans_gen_near_litter _
          simp only [← hNL, path.comp_assoc, ← path.comp_cons]
          exact trans_gen_constrains_comp hLN _
        · exact hL₂
      · intro E L hL₁ hL₂
        have hLN :
          (inr L.to_near_litter, (C.cons <| coe_lt hε).comp E) <[α]
            (inr N.fst.to_near_litter, (C.cons <| coe_lt hζ).cons (bot_lt_coe _)) :=
          by
          simp only [hNL]
          refine' Relation.TransGen.tail' _ (constrains.f_map hε _ _ _ _ _ hct)
          exact refl_trans_gen_constrains_comp hL₁ _
        specialize
          ih ((C.cons <| coe_lt hε).comp E, L.to_near_litter) (trans_gen_near_litter hLN)
            ⟨c, hc₁,
              trans (trans_gen_constrains_comp (trans_gen_near_litter hLN) _).to_reflTransGen hc₂⟩
        simp only at ih
        rw [← path.comp_assoc, path.comp_cons] at ih
        refine'
          (near_litter_action.smul_to_near_litter_eq_of_precise_at _
                (struct_action.hypothesised_allowable_exactly_approximates (ih_action _)
                  ⟨δ, ε, ζ, hε, hζ, hεζ, A.comp C, t, rfl, rfl⟩ _ _ _)
                _ (near_litter_action.refine_precise _) _).trans
            _
        · refine' Relation.TransGen.tail' (refl_trans_gen_constrains_comp hL₁ _) _
          exact constrains.f_map _ _ _ _ _ _ hct
        · refine' hL₂.trans _
          simp only [struct_action.comp_apply, struct_action.refine_apply,
            near_litter_action.refine_litter_map, ih_action_litter_map,
            foa_hypothesis_near_litter_image]
          rw [ih, ← allowable.derivative_to_struct_perm, struct_perm.derivative_derivative]
          rfl
        · simp only [struct_action.comp_apply, struct_action.refine_apply,
            near_litter_action.refine_litter_map, ih_action_litter_map,
            foa_hypothesis_near_litter_image]
          rw [ih, ← allowable.derivative_to_struct_perm, struct_perm.derivative_derivative]

/-- **Coherence lemma**: The action of the complete litter map, below a given support condition `c`,
is equal to the action of any allowable permutation that exactly approximates it.
This condition can only be applied for `γ < α` as we're dealing with lower allowable permutations.
-/
theorem constrainedAction_coherent_precise (hπf : π.Free) {γ : Iio α} (A : Path (β : TypeIndex) γ)
    (B : ExtendedIndex γ) (N : NearLitter) (s : Set (SupportCondition β)) (hs : Small s)
    (hc : ∃ c : SupportCondition β, c ∈ s ∧ (inr N, A.comp B) ≤[α] c)
    (hπ : ((constrainedAction π s hs).comp A).Lawful) (ρ : Allowable γ)
    (h : (((constrainedAction π s hs).comp A).rc hπ).ExactlyApproximates ρ.toStructPerm) :
    completeNearLitterMap π (A.comp B) N = StructPerm.derivative B ρ.toStructPerm • N :=
  constrainedAction_coherent_precise' hπf A (B, N) s hs hc hπ ρ h

/-- The coherence lemma for atoms, which is much easier to prove.
The statement is here for symmetry.
-/
theorem constrainedAction_coherent_precise_atom (hπf : π.Free) {γ : Iio α}
    (A : Path (β : TypeIndex) γ) (B : ExtendedIndex γ) (a : Atom) (s : Set (SupportCondition β))
    (hs : Small s) (hc : ∃ c : SupportCondition β, c ∈ s ∧ (inl a, A.comp B) ≤[α] c)
    (hπ : ((constrainedAction π s hs).comp A).Lawful) (ρ : Allowable γ)
    (h : (((constrainedAction π s hs).comp A).rc hπ).ExactlyApproximates ρ.toStructPerm) :
    completeAtomMap π (A.comp B) a = StructPerm.derivative B ρ.toStructPerm • a :=
  by
  refine' Eq.trans _ ((h B).map_atom a (Or.inl (Or.inl (Or.inl (Or.inl hc)))))
  rw [struct_action.rc_smul_atom_eq]
  rfl
  exact hc

theorem ihsAction_coherent_precise (hπf : π.Free) {γ : Iio α} (A : Path (β : TypeIndex) γ)
    (B : ExtendedIndex γ) (N : NearLitter) (c d : SupportCondition β)
    (hc : (inr N, A.comp B) ∈ transConstrained c d) (hπ : ((ihsAction π c d).comp A).Lawful)
    (ρ : Allowable γ) (h : (((ihsAction π c d).comp A).rc hπ).ExactlyApproximates ρ.toStructPerm) :
    completeNearLitterMap π (A.comp B) N = StructPerm.derivative B ρ.toStructPerm • N :=
  by
  simp_rw [ihs_action_eq_constrained_action] at hπ h
  refine' constrained_action_coherent_precise hπf A B N _ _ _ hπ ρ h
  cases hc
  · simp only [Relation.TransGen.tail'_iff, mem_set_of_eq] at hc
    obtain ⟨d, hd₁, hd₂⟩ := hc
    exact ⟨d, Or.inl hd₂, hd₁⟩
  · simp only [Relation.TransGen.tail'_iff, mem_set_of_eq] at hc
    obtain ⟨d, hd₁, hd₂⟩ := hc
    exact ⟨d, Or.inr hd₂, hd₁⟩

theorem ihsAction_coherent_precise_atom (hπf : π.Free) {γ : Iio α} (A : Path (β : TypeIndex) γ)
    (B : ExtendedIndex γ) (a : Atom) (c d : SupportCondition β) (hc : (inl a, A.comp B) <[α] c)
    (hπ : ((ihsAction π c d).comp A).Lawful) (ρ : Allowable γ)
    (h : (((ihsAction π c d).comp A).rc hπ).ExactlyApproximates ρ.toStructPerm) :
    completeAtomMap π (A.comp B) a = StructPerm.derivative B ρ.toStructPerm • a :=
  by
  refine' Eq.trans _ ((h B).map_atom a (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hc))))))
  rw [struct_action.rc_smul_atom_eq]
  rfl
  exact Or.inl hc

theorem ihAction_coherent_precise (hπf : π.Free) {γ : Iio α} (A : Path (β : TypeIndex) γ)
    (B : ExtendedIndex γ) (N : NearLitter) (c : SupportCondition β) (hc : (inr N, A.comp B) <[α] c)
    (hπ : ((ihAction (π.foaHypothesis : Hypothesis c)).comp A).Lawful) (ρ : Allowable γ)
    (h :
      (((ihAction (π.foaHypothesis : Hypothesis c)).comp A).rc hπ).ExactlyApproximates
        ρ.toStructPerm) :
    completeNearLitterMap π (A.comp B) N = StructPerm.derivative B ρ.toStructPerm • N :=
  by
  refine' ihs_action_coherent_precise hπf A B N c c (Or.inl hc) _ ρ _
  · rw [ihs_action_self]
    exact hπ
  · simp_rw [ihs_action_self]
    exact h

theorem ihAction_coherent_precise_atom (hπf : π.Free) {γ : Iio α} (A : Path (β : TypeIndex) γ)
    (B : ExtendedIndex γ) (a : Atom) (c : SupportCondition β) (hc : (inl a, A.comp B) <[α] c)
    (hπ : ((ihAction (π.foaHypothesis : Hypothesis c)).comp A).Lawful) (ρ : Allowable γ)
    (h :
      (((ihAction (π.foaHypothesis : Hypothesis c)).comp A).rc hπ).ExactlyApproximates
        ρ.toStructPerm) :
    completeAtomMap π (A.comp B) a = StructPerm.derivative B ρ.toStructPerm • a :=
  by
  refine' ihs_action_coherent_precise_atom hπf A B a c c hc _ ρ _
  · rw [ihs_action_self]
    exact hπ
  · simp_rw [ihs_action_self]
    exact h

theorem ihAction_smul_tangle' (hπf : π.Free) (c d : SupportCondition β) (A : ExtendedIndex β)
    (L : Litter) (hL₁ : (inr L.toNearLitter, A) ≤[α] c) (hL₂ : InflexibleCoe L A) (hlaw₁ hlaw₂) :
    (ihAction (π.foaHypothesis : Hypothesis (inr L.toNearLitter, A))).hypothesisedAllowable hL₂
          hlaw₁ (ihActionCompMapFlexible hπf _ _) •
        hL₂.t =
      (ihsAction π c d).hypothesisedAllowable hL₂ hlaw₂ (ihsActionCompMapFlexible hπf _ _ _) •
        hL₂.t :=
  by
  obtain ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ := hL₂
  rw [← inv_smul_eq_iff, smul_smul]
  refine' (designated_support t).Supports _ _
  intro e he
  rw [mul_smul, inv_smul_eq_iff]
  obtain ⟨a | N, C⟩ := e
  · refine' Prod.ext _ rfl
    change inl _ = inl _
    simp only
    refine'
      Eq.trans _
        (ihs_action_coherent_precise_atom hπf _ _ a c d _ hlaw₂ _
          ((ihs_action π c d).hypothesisedAllowable_exactlyApproximates _ _ _))
    simp_rw [← ihs_action_self]
    refine'
      (ihs_action_coherent_precise_atom hπf _ _ a _ _ _ _ _
          ((ihs_action π _ _).hypothesisedAllowable_exactlyApproximates
            ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ _ _)).symm
    · exact Relation.TransGen.single (constrains.f_map _ _ _ _ _ _ he)
    · exact Relation.TransGen.head' (constrains.f_map hδ _ _ _ _ _ he) hL₁
  · refine' Prod.ext _ rfl
    change inr _ = inr _
    simp only
    refine'
      Eq.trans _
        (ihs_action_coherent_precise hπf _ _ N c d _ hlaw₂ _
          ((ihs_action π c d).hypothesisedAllowable_exactlyApproximates _ _ _))
    simp_rw [← ihs_action_self]
    refine'
      (ihs_action_coherent_precise hπf _ _ N _ _ _ _ _
          ((ihs_action π _ _).hypothesisedAllowable_exactlyApproximates
            ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ _ _)).symm
    · exact Or.inl (Relation.TransGen.single (constrains.f_map _ _ _ _ _ _ he))
    · exact Or.inl (Relation.TransGen.head' (constrains.f_map hδ _ _ _ _ _ he) hL₁)

theorem ihAction_smul_tangle (hπf : π.Free) (c d : SupportCondition β) (A : ExtendedIndex β)
    (L : Litter) (hL₁ : (inr L.toNearLitter, A) ∈ reflTransConstrained c d)
    (hL₂ : InflexibleCoe L A) (hlaw₁ hlaw₂) :
    (ihAction (π.foaHypothesis : Hypothesis (inr L.toNearLitter, A))).hypothesisedAllowable hL₂
          hlaw₁ (ihActionCompMapFlexible hπf _ _) •
        hL₂.t =
      (ihsAction π c d).hypothesisedAllowable hL₂ hlaw₂ (ihsActionCompMapFlexible hπf _ _ _) •
        hL₂.t :=
  by
  cases hL₁
  · exact ih_action_smul_tangle' hπf c d A L hL₁ hL₂ hlaw₁ hlaw₂
  · have := ih_action_smul_tangle' hπf d c A L hL₁ hL₂ hlaw₁ _
    · simp_rw [ihs_action_symm] at this
      exact this
    · rw [ihs_action_symm]
      exact hlaw₂

theorem litter_injective_extends (hπf : π.Free) {c d : SupportCondition β}
    (hcd : (ihsAction π c d).Lawful) {A : ExtendedIndex β} {L₁ L₂ : Litter}
    (h₁ : (inr L₁.toNearLitter, A) ∈ reflTransConstrained c d)
    (h₂ : (inr L₂.toNearLitter, A) ∈ reflTransConstrained c d)
    (h : completeLitterMap π A L₁ = completeLitterMap π A L₂) : L₁ = L₂ :=
  by
  obtain h₁' | h₁' | h₁' := flexible_cases' β L₁ A
  · have h₂' : flexible α L₂ A :=
      by
      have := complete_litter_map_flexible hπf h₁'
      rw [h] at this
      exact complete_litter_map_flexible' hπf hcd h₂ this
    rw [complete_litter_map_eq_of_flexible h₁', complete_litter_map_eq_of_flexible h₂'] at h
    refine' LocalPerm.injOn _ _ _ h
    all_goals
      rw [near_litter_approx.flexible_completion_litter_perm_domain_free _ _ _ (hπf A)]
      assumption
  · obtain ⟨h₁'⟩ := h₁'
    have h₂' : inflexible_bot L₂ A :=
      by
      have := complete_litter_map_inflexible_bot h₁'
      rw [h] at this
      exact complete_litter_map_inflexible_bot' hπf hcd h₂ this
    rw [complete_litter_map_eq_of_inflexible_bot h₁',
      complete_litter_map_eq_of_inflexible_bot h₂'] at h
    obtain ⟨γ₁, ε₁, hγε₁, B₁, a₁, rfl, rfl⟩ := h₁'
    obtain ⟨γ₂, ε₂, hγε₂, B₂, a₂, rfl, hB⟩ := h₂'
    cases Subtype.coe_injective (coe_injective (path.obj_eq_of_cons_eq_cons hB))
    cases
      Subtype.coe_injective
        (coe_injective (path.obj_eq_of_cons_eq_cons (path.heq_of_cons_eq_cons hB).Eq))
    cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons hB).Eq).Eq
    refine' congr_arg _ ((hcd _).atomMap_injective _ _ (f_map_injective bot_ne_coe h))
    · have := constrains.f_map_bot hγε₁ B₁ a₁
      exact
        trans_constrained_of_refl_trans_constrained_of_trans_constrains h₁
          (Relation.TransGen.single this)
    · have := constrains.f_map_bot hγε₁ B₁ a₂
      exact
        trans_constrained_of_refl_trans_constrained_of_trans_constrains h₂
          (Relation.TransGen.single this)
  · obtain ⟨h₁'⟩ := h₁'
    have h₂' : inflexible_coe L₂ A :=
      by
      have := complete_litter_map_inflexible_coe hπf hcd h₁' h₁
      rw [h] at this
      exact complete_litter_map_inflexible_coe' hπf hcd h₂ this
    rw [complete_litter_map_eq_of_inflexible_coe h₁'] at h
    swap
    · refine' (hcd.le _).comp _
      cases h₁
      · exact (ih_action_le h₁).trans (ih_action_le_ihs_action _ _ _)
      · rw [ihs_action_symm]
        exact (ih_action_le h₁).trans (ih_action_le_ihs_action _ _ _)
    swap
    · exact ih_action_comp_map_flexible hπf _ _
    rw [complete_litter_map_eq_of_inflexible_coe h₂'] at h
    swap
    · refine' (hcd.le _).comp _
      cases h₂
      · exact (ih_action_le h₂).trans (ih_action_le_ihs_action _ _ _)
      · rw [ihs_action_symm]
        exact (ih_action_le h₂).trans (ih_action_le_ihs_action _ _ _)
    swap
    · exact ih_action_comp_map_flexible hπf _ _
    obtain ⟨γ₁, δ₁, ε₁, hδ₁, hε₁, hδε₁, B₁, t₁, rfl, rfl⟩ := h₁'
    obtain ⟨γ₂, δ₂, ε₂, hδ₂, hε₂, hδε₂, B₂, t₂, rfl, hB⟩ := h₂'
    cases Subtype.coe_injective (coe_injective (path.obj_eq_of_cons_eq_cons hB))
    cases
      Subtype.coe_injective
        (coe_injective (path.obj_eq_of_cons_eq_cons (path.heq_of_cons_eq_cons hB).Eq))
    cases (path.heq_of_cons_eq_cons (path.heq_of_cons_eq_cons hB).Eq).Eq
    have := congr_arg litter.β h
    cases Subtype.coe_injective (coe_injective this)
    clear this
    refine' congr_arg _ _
    have h' := f_map_injective _ h
    rw [ih_action_smul_tangle hπf c d _ _ h₁ _ _ (hcd.comp _)] at h'
    rw [ih_action_smul_tangle hπf c d _ _ h₂ _ _ (hcd.comp _)] at h'
    rw [struct_action.hypothesised_allowable_eq t₁ t₂ rfl (hcd.comp _)
        (ihs_action_comp_map_flexible hπf _ _ _)] at
      h'
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
  | left_lt ⦃a b c : α⦄ : r a b → split_lt (a, c) (b, c)
  | right_lt ⦃a b c : α⦄ : r b c → split_lt (a, b) (a, c)
  | left_split ⦃a b c d : α⦄ : r a c → r b c → split_lt (a, b) (c, d)
  | right_split ⦃a b c d : α⦄ : r a d → r b d → split_lt (a, b) (c, d)

theorem le_wellOrderExtension_lt {α : Type _} {r : α → α → Prop} (hr : WellFounded r) :
    r ≤ hr.wellOrderExtension.lt := fun a b h => Prod.Lex.left _ _ (hr.rank_lt_of_rel h)

theorem to_lex_lt_of_splitLt {α : Type _} {r : α → α → Prop} {hr : WellFounded r} :
    SplitLt r ≤
      InvImage (Prod.Lex hr.wellOrderExtension.lt hr.wellOrderExtension.lt) fun a =>
        if hr.wellOrderExtension.lt a.1 a.2 then (a.2, a.1) else (a.1, a.2) :=
  by
  intro a b h
  induction' h with a b c h a b c h a b c d ha hb a b c d ha hb
  · change Prod.Lex _ _ _ _
    simp only
    split_ifs with h₁ h₂ h₂
    · exact Prod.Lex.right _ (le_well_order_extension_lt hr _ _ h)
    · by_cases hcb : c = b
      · cases hcb
        exact Prod.Lex.right _ h₁
      · refine' Prod.Lex.left _ _ _
        have := (@not_lt _ hr.well_order_extension _ _).mp h₂
        exact @lt_of_le_of_ne _ (@LinearOrder.toPartialOrder _ hr.well_order_extension) _ _ this hcb
    · cases h₁ ((le_well_order_extension_lt hr _ _ h).trans h₂)
    · exact Prod.Lex.left _ _ (le_well_order_extension_lt hr _ _ h)
  · change Prod.Lex _ _ _ _
    simp only
    split_ifs with h₁ h₂ h₂
    · exact Prod.Lex.left _ _ (le_well_order_extension_lt hr _ _ h)
    · cases h₂ (h₁.trans (le_well_order_extension_lt hr _ _ h))
    · exact Prod.Lex.left _ _ h₂
    · exact Prod.Lex.right _ (le_well_order_extension_lt hr _ _ h)
  · change Prod.Lex _ _ _ _
    simp only
    split_ifs with h₁ h₂ h₂
    · exact Prod.Lex.left _ _ ((le_well_order_extension_lt hr _ _ hb).trans h₂)
    · exact Prod.Lex.left _ _ (le_well_order_extension_lt hr _ _ hb)
    · exact Prod.Lex.left _ _ ((le_well_order_extension_lt hr _ _ ha).trans h₂)
    · exact Prod.Lex.left _ _ (le_well_order_extension_lt hr _ _ ha)
  · change Prod.Lex _ _ _ _
    simp only
    split_ifs with h₁ h₂ h₂
    · exact Prod.Lex.left _ _ (le_well_order_extension_lt hr _ _ hb)
    · by_cases hcb : c = b
      · cases hcb
        exact Prod.Lex.right _ (le_well_order_extension_lt hr _ _ ha)
      · refine' Prod.Lex.left _ _ _
        have := (@not_lt _ hr.well_order_extension _ _).mp h₂
        exact
          @lt_of_lt_of_le _
            (@PartialOrder.toPreorder _ (@LinearOrder.toPartialOrder _ hr.well_order_extension)) _ _
            _ (le_well_order_extension_lt hr _ _ hb) this
    · exact Prod.Lex.left _ _ (le_well_order_extension_lt hr _ _ ha)
    · have := (@not_lt _ hr.well_order_extension _ _).mp h₂
      have :=
        @lt_of_lt_of_le _
          (@PartialOrder.toPreorder _ (@LinearOrder.toPartialOrder _ hr.well_order_extension)) _ _ _
          (le_well_order_extension_lt hr _ _ ha) this
      exact Prod.Lex.left _ _ this

theorem splitLt_wellFounded {α : Type _} {r : α → α → Prop} (hr : WellFounded r) :
    WellFounded (SplitLt r) :=
  by
  refine' Subrelation.wf to_lex_lt_of_split_lt _
  · exact hr
  · refine' InvImage.wf _ (InvImage.wf _ _)
    refine' WellFounded.prod_lex _ _ <;>
      exact
        InvImage.wf _
          (WellFounded.prod_lex ordinal.well_founded_lt.wf well_ordering_rel.is_well_order.wf)

-- TODO: Clean this up. Proof comes from an old lemma.
theorem completeAtomMap_mem_completeNearLitterMap_to_near_litter' (hπf : π.Free)
    {c d : SupportCondition β} (hcd : (ihsAction π c d).Lawful) {A : ExtendedIndex β} {a : Atom}
    {L : Litter} (ha : a.1 = L) (hL : (inr L.toNearLitter, A) ∈ reflTransConstrained c d) :
    π.completeAtomMap A a ∈ π.completeNearLitterMap A L.toNearLitter :=
  by
  subst ha
  rw [complete_near_litter_map_eq]
  by_cases ha : a ∈ (π A).atomPerm.domain
  · rw [complete_atom_map_eq_of_mem_domain ha]
    refine' Or.inl ⟨Or.inr ⟨a, ⟨rfl, ha⟩, rfl⟩, _⟩
    rintro ⟨_, ⟨b, rfl⟩, _, ⟨hb, rfl⟩, hab⟩
    simp only [foa_hypothesis_atom_image, mem_singleton_iff] at hab
    rw [complete_atom_map_eq_of_not_mem_domain hb.2] at hab
    have := sublitter.order_iso_apply_mem _
    rw [← hab] at this
    exact this.2 ((π A).atomPerm.map_domain ha)
  rw [complete_atom_map_eq_of_not_mem_domain ha]
  refine' Or.inl ⟨Or.inl _, _⟩
  · rw [SetLike.mem_coe]
    convert sublitter.order_iso_apply_mem _ using 1
    rw [near_litter_hypothesis_eq, complete_litter_map_eq]
    rfl
  · rintro ⟨_, ⟨b, rfl⟩, _, ⟨hb, rfl⟩, hab⟩
    simp only [foa_hypothesis_atom_image, mem_singleton_iff] at hab
    rw [complete_atom_map_eq_of_not_mem_domain hb.2] at hab
    have :=
      litter_injective_extends hπf hcd hL (fst_mem_refl_trans_constrained_of_mem_symm_diff hb.1 hL)
        _
    · rw [sublitter.order_iso_congr_left (congr_arg _ this) _,
        sublitter.order_iso_congr_right (congr_arg _ (congr_arg₂ _ rfl this)) _, Subtype.coe_inj,
        EquivLike.apply_eq_iff_eq] at hab
      simp only [SetLike.coe_mk] at hab
      cases hab
      exact hb.1.elim (fun h' => h'.2 rfl) fun h' => h'.2 rfl
    exact order_iso_apply_eq hab

theorem ihsAction_lawful_extends (hπf : π.Free) (c d : SupportCondition β)
    (hπ : ∀ e f, SplitLt (fun c d => c <[α] d) (e, f) (c, d) → (ihsAction π e f).Lawful) :
    (ihsAction π c d).Lawful := by
  intro A
  have litter_map_injective :
    ∀ ⦃L₁ L₂ : litter⦄ (hL₁ : (inr L₁.toNearLitter, A) ∈ trans_constrained c d)
      (hL₁ : (inr L₂.toNearLitter, A) ∈ trans_constrained c d),
      ((π.complete_near_litter_map A L₁.toNearLitter : Set atom) ∩
            (π.complete_near_litter_map A L₂.toNearLitter : Set atom)).Nonempty →
        L₁ = L₂ :=
    by
    intro L₁ L₂ h₁ h₂ h₁₂
    have := eq_of_complete_litter_map_inter_nonempty h₁₂
    cases h₁ <;> cases h₂
    · specialize
        hπ (inr L₁.to_near_litter, A) (inr L₂.to_near_litter, A) (split_lt.left_split h₁ h₂)
      exact
        litter_injective_extends hπf hπ (Or.inl Relation.ReflTransGen.refl)
          (Or.inr Relation.ReflTransGen.refl) this
    · specialize hπ (inr L₁.to_near_litter, A) d (split_lt.left_lt h₁)
      exact
        litter_injective_extends hπf hπ (Or.inl Relation.ReflTransGen.refl) (Or.inr h₂.to_refl) this
    · specialize hπ c (inr L₁.to_near_litter, A) (split_lt.right_lt h₁)
      exact
        litter_injective_extends hπf hπ (Or.inr Relation.ReflTransGen.refl) (Or.inl h₂.to_refl) this
    · specialize
        hπ (inr L₁.to_near_litter, A) (inr L₂.to_near_litter, A) (split_lt.right_split h₁ h₂)
      exact
        litter_injective_extends hπf hπ (Or.inl Relation.ReflTransGen.refl)
          (Or.inr Relation.ReflTransGen.refl) this
  constructor
  · intro a b ha hb hab
    simp only [ihs_action_atom_map] at ha hb hab
    cases ha <;> cases hb
    · specialize hπ (inl a, A) (inl b, A) (split_lt.left_split ha hb)
      exact
        atom_injective_extends hπ (Or.inl Relation.ReflTransGen.refl)
          (Or.inr Relation.ReflTransGen.refl) hab
    · specialize hπ (inl a, A) d (split_lt.left_lt ha)
      exact atom_injective_extends hπ (Or.inl Relation.ReflTransGen.refl) (Or.inr hb.to_refl) hab
    · specialize hπ c (inl a, A) (split_lt.right_lt ha)
      exact atom_injective_extends hπ (Or.inr Relation.ReflTransGen.refl) (Or.inl hb.to_refl) hab
    · specialize hπ (inl a, A) (inl b, A) (split_lt.right_split ha hb)
      exact
        atom_injective_extends hπ (Or.inl Relation.ReflTransGen.refl)
          (Or.inr Relation.ReflTransGen.refl) hab
  · exact litter_map_injective
  · intro a ha L hL
    simp only [ihs_action_atom_map, ihs_action_litter_map]
    have : π.complete_atom_map A a ∈ π.complete_near_litter_map A a.fst.to_near_litter :=
      by
      cases ha <;> cases hL
      · specialize hπ (inl a, A) (inr L.to_near_litter, A) (split_lt.left_split ha hL)
        exact
          complete_atom_map_mem_complete_near_litter_map_to_near_litter' hπf hπ rfl
            (fst_mem_refl_trans_constrained' (Or.inl Relation.ReflTransGen.refl))
      · specialize hπ (inl a, A) d (split_lt.left_lt ha)
        exact
          complete_atom_map_mem_complete_near_litter_map_to_near_litter' hπf hπ rfl
            (fst_mem_refl_trans_constrained' (Or.inl Relation.ReflTransGen.refl))
      · specialize hπ c (inl a, A) (split_lt.right_lt ha)
        exact
          complete_atom_map_mem_complete_near_litter_map_to_near_litter' hπf hπ rfl
            (fst_mem_refl_trans_constrained' (Or.inr Relation.ReflTransGen.refl))
      · specialize hπ (inl a, A) (inr L.to_near_litter, A) (split_lt.right_split ha hL)
        exact
          complete_atom_map_mem_complete_near_litter_map_to_near_litter' hπf hπ rfl
            (fst_mem_refl_trans_constrained' (Or.inl Relation.ReflTransGen.refl))
    constructor
    · rintro rfl
      exact this
    · intro h
      exact litter_map_injective (fst_mem_trans_constrained' ha) hL ⟨_, this, h⟩

/-- Every `ihs_action` is lawful. This is a consequence of all of the previous lemmas. -/
theorem ihsAction_lawful (hπf : π.Free) (c d : SupportCondition β) : (ihsAction π c d).Lawful :=
  by
  suffices ∀ c : support_condition β × support_condition β, (ihs_action π c.1 c.2).Lawful by
    exact this (c, d)
  intro c
  -- Satisfy the elaborator by splitting this line into two.
  have := WellFounded.induction (split_lt_well_founded (trans_constrains_wf α β)) c _
  exact this
  rintro ⟨c, d⟩ ih
  exact ihs_action_lawful_extends hπf c d fun e f hef => ih (e, f) hef

theorem ihAction_lawful (hπf : π.Free) (c : SupportCondition β) :
    (ihAction (π.foaHypothesis : Hypothesis c)).Lawful := by
  rw [← ihs_action_self] <;> exact ihs_action_lawful hπf c c

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
    π.completeAtomMap A a ∈ π.completeNearLitterMap A L.toNearLitter ↔ a.1 = L :=
  by
  have :=
    complete_atom_map_mem_complete_near_litter_map_to_near_litter' hπf
      (ihs_action_lawful hπf (inl a, A) (inl a, A)) rfl
      (fst_mem_refl_trans_constrained' (Or.inl Relation.ReflTransGen.refl))
  constructor
  · intro h
    exact
      complete_litter_map_injective hπf _ (eq_of_complete_litter_map_inter_nonempty ⟨_, this, h⟩)
  · rintro rfl
    exact this

theorem mem_image_iff {α β : Type _} {f : α → β} (hf : Injective f) (x : α) (s : Set α) :
    f x ∈ f '' s ↔ x ∈ s :=
  Set.InjOn.mem_image_iff (hf.InjOn Set.univ) (subset_univ _) (mem_univ _)

/-- Atoms inside near litters are mapped inside the corresponding image near-litter. -/
theorem completeAtomMap_mem_completeNearLitterMap (hπf : π.Free) {A : ExtendedIndex β} {a : Atom}
    {N : NearLitter} : π.completeAtomMap A a ∈ π.completeNearLitterMap A N ↔ a ∈ N :=
  by
  rw [← SetLike.mem_coe, complete_near_litter_map_eq', Set.symmDiff_def]
  simp only [mem_union, mem_diff, SetLike.mem_coe, not_exists, not_and,
    symmDiff_symmDiff_cancel_left]
  rw [complete_atom_map_mem_complete_near_litter_map_to_near_litter hπf]
  rw [mem_image_iff (complete_atom_map_injective hπf A)]
  simp only [← mem_litter_set, ← mem_diff, ← mem_union]
  rw [← Set.symmDiff_def, symmDiff_symmDiff_cancel_left]
  rw [SetLike.mem_coe]

/-- The complete near-litter map is injective. -/
theorem completeNearLitterMap_injective (hπf : π.Free) (A : ExtendedIndex β) :
    Injective (π.completeNearLitterMap A) :=
  by
  intro N₁ N₂ h
  rw [← SetLike.coe_set_eq, Set.ext_iff] at h ⊢
  intro a
  specialize h (π.complete_atom_map A a)
  simp only [SetLike.mem_coe, complete_atom_map_mem_complete_near_litter_map hπf] at h ⊢
  exact h

theorem completeNearLitterMap_subset_range (hπf : π.Free) (A : ExtendedIndex β) (L : Litter) :
    (π.completeNearLitterMap A L.toNearLitter : Set Atom) ⊆ range (π.completeAtomMap A) :=
  by
  rw [complete_near_litter_map_to_near_litter_eq]
  rintro a (⟨ha₁, ha₂⟩ | ⟨a, ⟨ha₁, ha₂⟩, rfl⟩)
  · refine'
      ⟨(((π A).largestSublitter L).OrderIso ((π A).largestSublitter a.1)).symm
          ⟨a, (π A).mem_largestSublitter_of_not_mem_domain a ha₂⟩,
        _⟩
    rw [complete_atom_map_eq_of_not_mem_domain]
    swap
    ·
      exact
        near_litter_approx.not_mem_domain_of_mem_largest_sublitter _
          (sublitter.order_iso_symm_apply_mem ⟨a, _⟩)
    · rw [mem_litter_set] at ha₁
      have :
        ((((π A).largestSublitter L).OrderIso ((π A).largestSublitter a.fst)).symm ⟨a, _⟩ :
              atom).fst =
          L :=
        sublitter.order_iso_symm_apply_fst_eq ⟨a, _⟩
      rw [sublitter.order_iso_congr_left (congr_arg _ this),
        sublitter.order_iso_congr_right (congr_arg _ (congr_arg _ this)),
        sublitter.order_iso_congr_right (congr_arg _ ha₁.symm)]
      simp only [SetLike.coe_mk, SetLike.eta, OrderIso.apply_symm_apply]
  · refine' ⟨a, _⟩
    rw [complete_atom_map_eq_of_mem_domain ha₂]

theorem completeAtomMap_surjective_extends (hπf : π.Free) (A : ExtendedIndex β) (a : Atom)
    (h : a.1 ∈ range (π.completeLitterMap A)) : a ∈ range (π.completeAtomMap A) :=
  by
  obtain ⟨L, hL⟩ := h
  by_cases ha : a ∈ (π A).atomPerm.domain
  · refine' ⟨(π A).atomPerm.symm a, _⟩
    rw [complete_atom_map_eq_of_mem_domain ((π A).atomPerm.symm.map_domain ha)]
    exact (π A).atomPerm.right_inv ha
  · have := complete_near_litter_map_to_near_litter_eq A L
    rw [hL] at this
    have := Eq.subset this.symm (Or.inl ⟨rfl, ha⟩)
    exact complete_near_litter_map_subset_range hπf A L this

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
    Injective π.completeSupportConditionMap :=
  by
  rintro ⟨a₁ | N₁, B₁⟩ ⟨a₂ | N₂, B₂⟩ h <;>
    simp only [complete_support_condition_map_atom_eq,
      complete_support_condition_map_near_litter_eq, Prod.mk.inj_iff] at h
  · cases h.2
    cases complete_atom_map_injective hπf B₁ h.1
    rfl
  · cases h.1
  · cases h.1
  · cases h.2
    cases complete_near_litter_map_injective hπf B₁ h.1
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
theorem preimageAction_lawful {hπf : π.Free} {c : SupportCondition β} :
    (preimageAction hπf c).Lawful := by
  intro A
  constructor
  · intro a b ha hb hab
    exact complete_atom_map_injective hπf A hab
  · intro L₁ L₂ hL₁ hL₂ hL
    exact complete_litter_map_injective hπf A (eq_of_complete_litter_map_inter_nonempty hL)
  · intro a ha L hL
    exact (complete_atom_map_mem_complete_near_litter_map_to_near_litter hπf).symm

theorem preimageActionCompMapFlexible {hπf : π.Free} {γ : Iio α} {c : SupportCondition β}
    (A : Path (β : TypeIndex) γ) : ((preimageAction hπf c).comp A).MapFlexible :=
  constrainedActionCompMapFlexible hπf A

theorem Relation.reflTransGen_of_eq {α : Type _} {r : α → α → Prop} {x y : α} (h : x = y) :
    Relation.ReflTransGen r x y := by cases h <;> rfl

theorem preimageAction_coherent_precise (hπf : π.Free) {γ : Iio α} (A : Path (β : TypeIndex) γ)
    (B : ExtendedIndex γ) (N : NearLitter) (c : SupportCondition β)
    (hc : (inr (π.completeNearLitterMap (A.comp B) N), A.comp B) ≺[α] c) (ρ : Allowable γ)
    (h :
      (((preimageAction hπf c).comp A).rc (preimageAction_lawful.comp _)).ExactlyApproximates
        ρ.toStructPerm) :
    completeNearLitterMap π (A.comp B) N = StructPerm.derivative B ρ.toStructPerm • N :=
  by
  refine' constrained_action_coherent_precise hπf A B N _ _ _ (preimage_action_lawful.comp _) ρ h
  refine' ⟨_, _, Relation.ReflTransGen.refl⟩
  exact hc

theorem preimageAction_coherent_precise_atom (hπf : π.Free) {γ : Iio α} (A : Path (β : TypeIndex) γ)
    (B : ExtendedIndex γ) (a : Atom) (c : SupportCondition β)
    (hc : (inl (π.completeAtomMap (A.comp B) a), A.comp B) ≺[α] c) (ρ : Allowable γ)
    (h :
      (((preimageAction hπf c).comp A).rc (preimageAction_lawful.comp _)).ExactlyApproximates
        ρ.toStructPerm) :
    completeAtomMap π (A.comp B) a = StructPerm.derivative B ρ.toStructPerm • a :=
  by
  refine' constrained_action_coherent_precise_atom hπf A B a _ _ _ _ ρ h
  refine' ⟨_, _, Relation.ReflTransGen.refl⟩
  exact hc

theorem completeLitterMap_surjective_extends (hπf : π.Free) (A : ExtendedIndex β) (L : Litter)
    (ha :
      ∀ (B : ExtendedIndex β) (a : Atom),
        (inl a, B) ≺[α] (inr L.toNearLitter, A) → a ∈ range (π.completeAtomMap B))
    (hN :
      ∀ (B : ExtendedIndex β) (N : NearLitter),
        (inr N, B) ≺[α] (inr L.toNearLitter, A) → N ∈ range (π.completeNearLitterMap B)) :
    L ∈ range (π.completeLitterMap A) :=
  by
  obtain h | ⟨⟨h⟩⟩ | ⟨⟨h⟩⟩ := flexible_cases' β L A
  · refine' ⟨(near_litter_approx.flexible_completion α (π A) A).symm • L, _⟩
    rw [complete_litter_map_eq_of_flexible, near_litter_approx.right_inv_litter]
    · rw [near_litter_approx.flexible_completion_litter_perm_domain_free α (π A) A (hπf A)]
      exact h
    · exact near_litter_approx.flexible_completion_symm_smul_flexible α (π A) A (hπf A) L h
  · obtain ⟨γ, ε, hε, C, a, rfl, rfl⟩ := h
    obtain ⟨b, rfl⟩ := ha _ a (constrains.f_map_bot hε _ a)
    refine' ⟨f_map (show ⊥ ≠ (ε : type_index) from bot_ne_coe) b, _⟩
    rw [complete_litter_map_eq_of_inflexible_bot ⟨γ, ε, hε, C, b, rfl, rfl⟩]
  · obtain ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ := h
    refine'
      ⟨f_map (coe_ne_coe.mpr <| coe_ne' hδε)
          (((preimage_action hπf
                    (inr (f_map (coe_ne_coe.mpr <| coe_ne' hδε) t).toNearLitter,
                      (B.cons (coe_lt hε)).cons (bot_lt_coe _))).hypothesisedAllowable
                ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ (preimage_action_lawful.comp _)
                (preimage_action_comp_map_flexible _))⁻¹ •
            t),
        _⟩
    rw [complete_litter_map_eq_of_inflexible_coe ⟨γ, δ, ε, hδ, hε, hδε, B, _, rfl, rfl⟩
        ((ih_action_lawful hπf _).comp _) (ih_action_comp_map_flexible hπf _ _)]
    refine' congr_arg _ _
    rw [smul_smul]
    refine' (designated_support t).Supports _ _
    intro c hc
    rw [mul_smul, smul_eq_iff_eq_inv_smul]
    obtain ⟨a | N, A⟩ := c
    · refine' Prod.ext _ rfl
      change inl _ = inl _
      simp only
      have hac := constrains.f_map hδ _ _ _ _ _ hc
      specialize ha _ a hac
      obtain ⟨b, ha⟩ := ha
      have :
        (struct_perm.derivative A
                ((preimage_action hπf
                        (inr (f_map (coe_ne_coe.mpr <| coe_ne' hδε) t).toNearLitter,
                          (B.cons (coe_lt hε)).cons (bot_lt_coe _))).hypothesisedAllowable
                    ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ (preimage_action_lawful.comp _)
                    (preimage_action_comp_map_flexible _)).toStructPerm)⁻¹ •
            a =
          b :=
        by
        rw [inv_smul_eq_iff, ← ha]
        rw [struct_action.hypothesised_allowable]
        refine'
          preimage_action_coherent_precise_atom hπf (B.cons <| coe_lt hδ) A b _ _ _
            (struct_action.allowable_exactly_approximates _ _ _ _)
        rw [ha]
        exact hac
      trans b
      · rw [map_inv, map_inv, this]
      · rw [map_inv, map_inv, ← smul_eq_iff_eq_inv_smul, ← ha]
        rw [struct_action.hypothesised_allowable]
        refine'
          (ih_action_coherent_precise_atom hπf (B.cons <| coe_lt hδ) A b _ _
              ((ih_action_lawful hπf _).comp _) _
              (struct_action.allowable_exactly_approximates _ _ _ _)).symm
        refine'
          Relation.TransGen.tail' _
            (constrains.f_map hδ _ _ _ _ _ (smul_mem_designated_support hc _))
        refine' Relation.reflTransGen_of_eq _
        refine' Prod.ext _ rfl
        change inl _ = inl _
        simp only [map_inv, eq_inv_smul_iff, ← this, smul_inv_smul]
    · refine' Prod.ext _ rfl
      change inr _ = inr _
      simp only
      have hNc := constrains.f_map hδ _ _ _ _ _ hc
      specialize hN _ N hNc
      obtain ⟨N', hN⟩ := hN
      have :
        (struct_perm.derivative A
                ((preimage_action hπf
                        (inr (f_map (coe_ne_coe.mpr <| coe_ne' hδε) t).toNearLitter,
                          (B.cons (coe_lt hε)).cons (bot_lt_coe _))).hypothesisedAllowable
                    ⟨γ, δ, ε, hδ, hε, hδε, B, t, rfl, rfl⟩ (preimage_action_lawful.comp _)
                    (preimage_action_comp_map_flexible _)).toStructPerm)⁻¹ •
            N =
          N' :=
        by
        rw [inv_smul_eq_iff, ← hN]
        rw [struct_action.hypothesised_allowable]
        refine'
          preimage_action_coherent_precise hπf (B.cons <| coe_lt hδ) A N' _ _ _
            (struct_action.allowable_exactly_approximates _ _ _ _)
        rw [hN]
        exact hNc
      trans N'
      · rw [map_inv, map_inv, this]
      · rw [map_inv, map_inv, ← smul_eq_iff_eq_inv_smul, ← hN]
        rw [struct_action.hypothesised_allowable]
        refine'
          (ih_action_coherent_precise hπf (B.cons <| coe_lt hδ) A N' _ _
              ((ih_action_lawful hπf _).comp _) _
              (struct_action.allowable_exactly_approximates _ _ _ _)).symm
        refine'
          Relation.TransGen.tail' _
            (constrains.f_map hδ _ _ _ _ _ (smul_mem_designated_support hc _))
        refine' Relation.reflTransGen_of_eq _
        refine' Prod.ext _ rfl
        change inr _ = inr _
        simp only [map_inv, eq_inv_smul_iff, ← this, smul_inv_smul]

theorem atom_mem_range_of_mem_completeNearLitterMap (hπf : π.Free) (A : ExtendedIndex β) (a : Atom)
    {N : NearLitter} (h : a ∈ π.completeNearLitterMap A N) : a ∈ range (π.completeAtomMap A) :=
  by
  rw [← SetLike.mem_coe] at h
  rw [complete_near_litter_map_eq'] at h
  obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := h
  · rw [complete_near_litter_map_to_near_litter_eq] at h₁
    cases h₁
    · exact complete_atom_map_surjective_extends hπf A a ⟨_, h₁.1.symm⟩
    · obtain ⟨b, h₁, rfl⟩ := h₁
      refine' ⟨b, _⟩
      exact complete_atom_map_eq_of_mem_domain h₁.2
  · obtain ⟨b, h₁, rfl⟩ := h₁
    exact ⟨b, rfl⟩

theorem completeNearLitterMap_coe (hπf : π.Free) (A : ExtendedIndex β) (N : NearLitter) :
    (π.completeNearLitterMap A N : Set Atom) = π.completeAtomMap A '' N :=
  by
  ext a : 1
  constructor
  · intro h
    obtain ⟨b, rfl⟩ := atom_mem_range_of_mem_complete_near_litter_map hπf A a h
    rw [SetLike.mem_coe, complete_atom_map_mem_complete_near_litter_map hπf] at h
    exact ⟨b, h, rfl⟩
  · rintro ⟨b, h, rfl⟩
    rw [SetLike.mem_coe, complete_atom_map_mem_complete_near_litter_map hπf]
    exact h

@[simp]
theorem preimage_symmDiff {α β : Type _} {s t : Set β} {f : α → β} :
    f ⁻¹' s ∆ t = (f ⁻¹' s) ∆ (f ⁻¹' t) :=
  rfl

theorem completeNearLitterMap_surjective_extends (hπf : π.Free) (A : ExtendedIndex β)
    (N : NearLitter) (hN : N.1 ∈ range (π.completeLitterMap A))
    (ha : litterSet N.1 ∆ N ⊆ range (π.completeAtomMap A)) :
    N ∈ range (π.completeNearLitterMap A) :=
  by
  obtain ⟨L, hN⟩ := hN
  refine' ⟨⟨L, π.complete_atom_map A ⁻¹' N, _⟩, _⟩
  · suffices Small ((π.complete_atom_map A '' L.to_near_litter) ∆ N)
      by
      have := small.preimage (complete_atom_map_injective hπf A) this
      rw [preimage_symm_diff, preimage_image_eq _ (complete_atom_map_injective hπf A)] at this
      exact this
    rw [← complete_near_litter_map_coe hπf]
    refine' is_near_litter.near _ N.2.2
    simp only [near_litter.is_near_litter, complete_near_litter_map_fst_eq]
    exact hN
  · refine' SetLike.coe_injective _
    rw [complete_near_litter_map_coe hπf]
    simp only [near_litter.coe_mk, Subtype.coe_mk, litter.coe_to_near_litter]
    rw [image_preimage_eq_of_subset _]
    intro a ha'
    by_cases a.1 = N.1
    · rw [← hN] at h
      exact complete_atom_map_surjective_extends hπf A a ⟨_, h.symm⟩
    · exact ha (Or.inr ⟨ha', h⟩)

variable (π)

def CompleteMapSurjectiveAt : SupportCondition β → Prop
  | (inl a, A) => a ∈ range (π.completeAtomMap A)
  | (inr N, A) => N ∈ range (π.completeNearLitterMap A)

variable {π}

theorem completeMapSurjectiveExtends (hπf : π.Free) (c : SupportCondition β)
    (hc : ∀ d : SupportCondition β, d <[α] c → π.CompleteMapSurjectiveAt d) :
    π.CompleteMapSurjectiveAt c := by
  obtain ⟨a | N, A⟩ := c
  · refine' complete_atom_map_surjective_extends hπf A a _
    obtain ⟨N, hN⟩ := hc (inr a.1.toNearLitter, A) (Relation.TransGen.single <| constrains.atom a A)
    refine' ⟨N.1, _⟩
    apply_fun Sigma.fst at hN
    simp only [litter.to_near_litter_fst, complete_near_litter_map_fst_eq'] at hN
    exact hN
  · refine' complete_near_litter_map_surjective_extends hπf A N _ _
    · refine' complete_litter_map_surjective_extends hπf A N.1 _ _
      · intro B a h
        exact hc (inl a, B) (trans_gen_near_litter <| Relation.TransGen.single h)
      · intro B N h
        exact hc (inr N, B) (trans_gen_near_litter <| Relation.TransGen.single h)
    · intro a h
      exact hc (inl a, A) (Relation.TransGen.single <| constrains.symm_diff N a h A)

theorem completeMapSurjectiveAtAll (hπf : π.Free) (c : SupportCondition β) :
    π.CompleteMapSurjectiveAt c :=
  WellFounded.induction (trans_constrains_wf α β) c (completeMapSurjectiveExtends hπf)

theorem completeAtomMap_surjective (hπf : π.Free) (A : ExtendedIndex β) :
    Surjective (π.completeAtomMap A) := fun a => completeMapSurjectiveAtAll hπf (inl a, A)

theorem completeNearLitterMap_surjective (hπf : π.Free) (A : ExtendedIndex β) :
    Surjective (π.completeNearLitterMap A) := fun N => completeMapSurjectiveAtAll hπf (inr N, A)

theorem completeLitterMap_surjective (hπf : π.Free) (A : ExtendedIndex β) :
    Surjective (π.completeLitterMap A) := by
  intro L
  obtain ⟨N, hN⟩ := complete_near_litter_map_surjective hπf A L.to_near_litter
  refine' ⟨N.1, _⟩
  apply_fun Sigma.fst at hN
  simp only [complete_near_litter_map_fst_eq', litter.to_near_litter_fst] at hN
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
      ⇑(complete_atom_perm hπf A)⁻¹ ⁻¹' s = (π.complete_near_litter_map A ⟨L, s, hs⟩ : Set atom) :=
      by
      rw [complete_near_litter_map_coe hπf, perm.preimage_inv]
      rfl
    rw [this]
    simp only [near_litter.is_near_litter, complete_near_litter_map_fst_eq']
    rfl

theorem completeNearLitterPerm_smul_atom (hπf : π.Free) (A : ExtendedIndex β) (a : Atom) :
    completeNearLitterPerm hπf A • a = π.completeAtomMap A a :=
  rfl

theorem completeNearLitterPerm_smul_litter (hπf : π.Free) (A : ExtendedIndex β) (L : Litter) :
    completeNearLitterPerm hπf A • L = π.completeLitterMap A L :=
  rfl

theorem completeNearLitterPerm_smul_nearLitter (hπf : π.Free) (A : ExtendedIndex β)
    (N : NearLitter) : completeNearLitterPerm hπf A • N = π.completeNearLitterMap A N :=
  by
  refine' SetLike.coe_injective _
  rw [complete_near_litter_map_coe hπf]
  rfl

def AllowableBelow (hπf : π.Free) (γ : iicIndex α) (A : Path (β : TypeIndex) γ) : Prop :=
  ∃ ρ : Allowable γ,
    ∀ B : ExtendedIndex γ,
      StructPerm.ofBot (StructPerm.derivative B ρ.toStructPerm) =
        completeNearLitterPerm hπf (A.comp B)

@[simp]
theorem ofBot_toStructPerm (π : Allowable ⊥) : StructPerm.ofBot π.toStructPerm = π :=
  by
  ext a : 2
  rw [to_struct_perm_bot]
  simp only [MulEquiv.coe_toMonoidHom, struct_perm.coe_to_bot_iso, struct_perm.of_bot_to_bot]

theorem allowableBelowBot (hπf : π.Free) (A : ExtendedIndex β) : AllowableBelow hπf ⊥ A :=
  by
  refine' ⟨complete_near_litter_perm hπf A, _⟩
  intro B
  obtain B | ⟨B, h⟩ := B
  · simp only [struct_perm.derivative_nil, path.comp_nil, of_bot_to_struct_perm]
  · -- TODO: Make this a lemma.
    cases le_bot_iff.mp (le_of_path B)
    cases bot_le.not_lt h

theorem exists_nil_cons_of_path' {β γ : TypeIndex} (A : Path (β : TypeIndex) γ)
    (hA : A.length ≠ 0) :
    ∃ δ : TypeIndex,
      ∃ h : (δ : TypeIndex) < β,
        ∃ B : Path δ γ, A = ((Path.nil : Path (β : TypeIndex) β).cons h).comp B :=
  by
  set n := A.length with hn
  clear_value n
  induction' n with n ih generalizing γ
  · cases hA rfl
  cases' A with δ _ A hδ
  · cases hn
  simp only [path.length_cons, Nat.succ_eq_add_one, add_left_inj] at hn
  cases n
  · cases path.eq_of_length_zero A hn.symm
    cases path_eq_nil A
    exact ⟨γ, hδ, path.nil, rfl⟩
  · obtain ⟨ε, hε, B, rfl⟩ := ih n.succ_ne_zero A hn
    exact ⟨ε, hε, B.cons hδ, rfl⟩

theorem exists_nil_cons_of_path {β : Iic α} (A : ExtendedIndex β) :
    ∃ γ : iioIndex α,
      ∃ h : (γ : TypeIndex) < β,
        ∃ B : ExtendedIndex γ, A = ((Path.nil : Path (β : TypeIndex) β).cons h).comp B :=
  by
  obtain ⟨γ, h, B, rfl⟩ := exists_nil_cons_of_path' A _
  · refine' ⟨⟨γ, _⟩, h, B, rfl⟩
    exact lt_of_lt_of_le h (coe_le_coe.mpr β.prop)
  · intro h
    cases path.eq_of_length_zero A h

theorem iioIndex_cases (δ : iioIndex α) : δ = ⊥ ∨ ∃ ε : Iio α, δ = ε :=
  by
  obtain ⟨_ | δ, hδ⟩ := δ
  · exact Or.inl rfl
  · exact Or.inr ⟨⟨δ, coe_lt_coe.mp hδ⟩, rfl⟩

theorem allowableBelowExtends (hπf : π.Free) (γ : Iic α) (A : Path (β : TypeIndex) γ)
    (h : ∀ (δ : iioIndex α) (h : (δ : TypeIndex) < γ), AllowableBelow hπf δ (A.cons h)) :
    AllowableBelow hπf γ A := by
  choose ρs hρ using h
  refine' ⟨allowable_of_smul_f_map γ ρs _, _⟩
  · intro δ ε hδ hε hδε t
    change struct_perm.to_near_litter_perm _ • _ = _
    have := hρ ε hε (path.nil.cons (bot_lt_coe _))
    simp only [path.comp_cons, path.comp_nil] at this
    change struct_perm.to_near_litter_perm (ρs ε hε).toStructPerm = _ at this
    rw [this]
    rw [complete_near_litter_perm_smul_litter]
    obtain rfl | ⟨δ, rfl⟩ := Iio_index_cases δ
    · refine'
        (complete_litter_map_eq_of_inflexible_bot ⟨γ, ε, coe_lt_coe.mp hε, A, t, rfl, rfl⟩).trans _
      refine' congr_arg _ _
      specialize hρ ⊥ hδ path.nil
      simp only [struct_perm.derivative_nil, of_bot_to_struct_perm, path.comp_nil] at hρ
      rw [hρ]
      rfl
    · refine'
        (complete_litter_map_eq_of_inflexible_coe
              ⟨γ, δ, ε, coe_lt_coe.mp hδ, coe_lt_coe.mp hε, _, A, t, rfl, rfl⟩
              ((ih_action_lawful hπf _).comp _) (ih_action_comp_map_flexible hπf _ _)).trans
          _
      · rintro rfl
        cases hδε rfl
      refine' congr_arg _ _
      rw [← inv_smul_eq_iff, smul_smul]
      refine' (designated_support t).Supports _ _
      intro c hc
      rw [mul_smul, inv_smul_eq_iff]
      obtain ⟨a | N, B⟩ := c
      · refine' Prod.ext _ rfl
        change inl _ = inl _
        simp only
        rw [←
          ih_action_coherent_precise_atom hπf _ B a _
            (Relation.TransGen.single <| constrains.f_map _ _ _ _ _ _ hc) _ _
            (struct_action.hypothesised_allowable_exactly_approximates _
              ⟨γ, δ, ε, _, _, _, _, t, rfl, rfl⟩ _ _)]
        exact (congr_arg (fun π => π • a) (hρ δ hδ B)).symm
      · refine' Prod.ext _ rfl
        change inr _ = inr _
        simp only
        rw [←
          ih_action_coherent_precise hπf _ B N _
            (Relation.TransGen.single <| constrains.f_map _ _ _ _ _ _ hc) _ _
            (struct_action.hypothesised_allowable_exactly_approximates _
              ⟨γ, δ, ε, _, _, _, _, t, rfl, rfl⟩ _ _)]
        rw [← complete_near_litter_perm_smul_near_litter hπf]
        exact (congr_arg (fun π => π • N) (hρ δ hδ B)).symm
  · intro B
    obtain ⟨δ, hδ, B, rfl⟩ := exists_nil_cons_of_path B
    specialize hρ δ hδ B
    rw [← struct_perm.derivative_derivative]
    have := allowable_of_smul_f_map_derivative_eq δ hδ
    apply_fun allowable.to_struct_perm at this
    rw [← allowable_derivative_eq] at this
    rw [← this] at hρ
    rw [← path.comp_assoc, path.comp_cons, path.comp_nil]
    exact hρ

theorem allowableBelowAll (hπf : π.Free) (γ : Iic α) (A : Path (β : TypeIndex) γ) :
    AllowableBelow hπf γ A := by
  obtain ⟨γ, hγ⟩ := γ
  revert hγ
  refine' WellFounded.induction Λwf.wf γ _
  intro γ ih hγ A
  refine' allowable_below_extends hπf ⟨γ, hγ⟩ A _
  intro δ hδ
  obtain rfl | ⟨δ, rfl⟩ := Iio_index_cases δ
  · exact allowable_below_bot hπf _
  · exact ih δ (coe_lt_coe.mp hδ) (le_of_lt δ.prop) _

noncomputable def completeAllowable (hπf : π.Free) : Allowable β :=
  (allowableBelowAll hπf β Path.nil).some

theorem completeAllowable_derivative (hπf : π.Free) (A : ExtendedIndex β) :
    StructPerm.ofBot (StructPerm.derivative A (completeAllowable hπf).toStructPerm) =
      completeNearLitterPerm hπf A :=
  by
  have := (allowable_below_all hπf β path.nil).choose_spec A
  rw [path.nil_comp] at this
  exact this

theorem complete_exception_mem (hπf : π.Free) (A : ExtendedIndex β) (a : Atom)
    (ha : (completeNearLitterPerm hπf A).IsException a) : a ∈ (π A).atomPerm.domain :=
  by
  unfold near_litter_perm.is_exception at ha
  simp only [mem_litter_set, complete_near_litter_perm_smul_atom,
    complete_near_litter_perm_smul_litter] at ha
  cases ha
  · have := complete_near_litter_map_to_near_litter_eq A a.1
    rw [complete_near_litter_map_coe hπf, Set.ext_iff] at this
    have := (this (π.complete_atom_map A a)).mp ⟨_, rfl, rfl⟩
    obtain ha' | ⟨b, ⟨hb₁, hb₂⟩, hb₃⟩ := this
    · cases ha ha'.1
    rw [← complete_atom_map_eq_of_mem_domain hb₂] at hb₃
    cases complete_atom_map_injective hπf A hb₃
    exact hb₂
  · obtain ⟨a, rfl⟩ := complete_atom_map_surjective hπf A a
    rw [eq_inv_smul_iff, ← complete_near_litter_perm_smul_atom hπf, inv_smul_smul] at ha
    have := complete_near_litter_map_to_near_litter_eq A a.1
    rw [complete_near_litter_map_coe hπf, Set.ext_iff] at this
    have := (this (π.complete_atom_map A a)).mp ⟨_, rfl, rfl⟩
    obtain ha' | ⟨b, ⟨hb₁, hb₂⟩, hb₃⟩ := this
    · cases ha ha'.1.symm
    · rw [← complete_atom_map_eq_of_mem_domain hb₂] at hb₃
      cases complete_atom_map_injective hπf A hb₃
      rw [complete_atom_map_eq_of_mem_domain hb₂]
      exact (π A).atomPerm.map_domain hb₂

theorem completeAllowable_exactlyApproximates (hπf : π.Free) :
    π.ExactlyApproximates (completeAllowable hπf).toStructPerm :=
  by
  intro A
  refine' ⟨⟨_, _⟩, _⟩
  · intro a ha
    rw [complete_allowable_derivative, complete_near_litter_perm_smul_atom,
      complete_atom_map_eq_of_mem_domain ha]
  · intro L hL
    rw [complete_allowable_derivative, complete_near_litter_perm_smul_litter,
      complete_litter_map_eq_of_flexible (hπf A L hL),
      near_litter_approx.flexible_completion_smul_of_mem_domain _ _ A L hL]
    rfl
  · intro a ha
    rw [complete_allowable_derivative] at ha
    exact complete_exception_mem hπf A a ha

def foaExtends : FoaIh β := fun π hπf =>
  ⟨completeAllowable hπf, completeAllowable_exactlyApproximates hπf⟩

theorem freedom_of_action (β : Iic α) (π₀ : StructApprox β) (h : π₀.Free) :
    ∃ π : Allowable β, π₀.ExactlyApproximates π.toStructPerm :=
  by
  obtain ⟨β, hβ⟩ := β
  revert hβ
  refine' WellFounded.induction Λwf.wf β _
  intro β ih hβ π₀ h
  have : freedom_of_action_hypothesis ⟨β, hβ⟩ :=
    by
    constructor
    intro γ hγ
    exact ih γ hγ γ.prop
  exact foa_extends π₀ h

end StructApprox

end ConNF
