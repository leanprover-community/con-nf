import ConNF.Foa.Complete

open Equiv Function Quiver Set Sum WithBot

open scoped Classical Pointwise

universe u

namespace ConNF

namespace StructApprox

variable [Params.{u}] {α : Λ} [BasePositions] [Phase2Assumptions α] {β : Iic α}
  [FreedomOfActionHypothesis β]

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

theorem ihActionSupports {π : StructApprox β} {A : ExtendedIndex β} {L : Litter}
    (h : InflexibleCoe L A) :
    ((ihAction (π.foaHypothesis : Hypothesis (inr L.toNearLitter, A))).comp
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
      (inr (fuzz (Subtype.coe_injective.ne (Iio.coe_injective.ne hδε)) t).toNearLitter,
          (C.cons (coe_lt hε)).cons (bot_lt_coe _)) ≤[α]
        d)
    (hd : (d.fst, (h.B.cons (coe_lt h.hδ)).comp d.snd) ≺[α] (inr L.toNearLitter, A))
    {B : ExtendedIndex δ} {a : Atom} (hc : (inl a, B) ∈ (designatedSupport t).carrier) :
    (inl a, (h.B.cons (coe_lt h.hδ)).comp ((C.cons (coe_lt hδ)).comp B)) <[α]
      (inr L.toNearLitter, A) := by
  refine' Relation.TransGen.tail' _ hd
  refine' reflTransGen_constrains_comp (c := (inl a, _)) (d := d) _ (h.B.cons <| coe_lt h.hδ)
  refine' Relation.ReflTransGen.trans _ hd₂
  exact Relation.ReflTransGen.single (Constrains.fuzz hδ hε hδε C t _ hc)

end StructApprox

end ConNF
