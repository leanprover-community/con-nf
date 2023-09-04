import ConNF.Foa.Basic.Flexible
import ConNF.Counting.CodingFunction

/-!
# Specifications
-/

open Quiver Set Sum WithBot

open scoped Classical

universe u

namespace ConNF

variable [Params.{u}] {α : Λ} [BasePositions] [FoaAssumptions α] {β : Iic α}

def Time (β : Iic α) : Type u :=
  μ ×ₗ ExtendedIndex β

inductive SpecCondition (β : Iic α)
  | atom (A : ExtendedIndex β) (i : Time β)
  | flexible (A : ExtendedIndex β)
  | inflexibleCoe (A : ExtendedIndex β) (h : InflexibleCoePath A)
      (χ : CodingFunction (h.δ : Iic α))
  | inflexibleBot (A : ExtendedIndex β) (h : InflexibleBotPath A)
      (i : Time β)

structure Spec (β : Iic α) where
  /-- `cond i` describes the condition inserted at time `i` in the construction of an ordered
  support. -/
  cond : Time β →. SpecCondition β
  dom_small : Small cond.Dom

/-- A specification `σ` specifies an ordered support `S` if `dom σ = ran S`, and each support
condition in `S` is described in a sensible way by `σ`. -/
structure Specifies (σ : Spec β) (S : OrdSupport β) : Prop where
  cpos_dom (c : SupportCondition β) (hc : c ∈ S) : (σ.cond ⟨(S.cpos c).get hc, c.path⟩).Dom
  exists_mem_of_dom (i : Time β) : (σ.cond i).Dom →
    ∃ c, ∃ (hc : c ∈ S), c.path = i.snd ∧ (S.cpos c).get hc = i.fst
  atom_spec (A : ExtendedIndex β) (a : Atom) (N : NearLitter)
    (ha : ⟨A, inl a⟩ ∈ S) (hN : ⟨A, inr N⟩ ∈ S) : a ∈ N →
    (σ.cond ⟨(S.cpos _).get ha, A⟩).get (cpos_dom ⟨A, inl a⟩ ha) =
    SpecCondition.atom A ⟨(S.cpos _).get hN, A⟩
  flexible_spec (A : ExtendedIndex β) (N : NearLitter) (hN : ⟨A, inr N⟩ ∈ S) : Flexible α A N.fst →
    (σ.cond ⟨(S.cpos _).get hN, A⟩).get (cpos_dom ⟨A, inr N⟩ hN) = SpecCondition.flexible A
  inflexibleCoe_spec (A : ExtendedIndex β) (N : NearLitter) (hN : ⟨A, inr N⟩ ∈ S)
    (h : InflexibleCoe A N.1) :
    ∃ χ : CodingFunction h.path.δ,
    ∃ h' : (S.before ((S.cpos _).get hN)).comp h.path.δ (h.path.B.cons h.path.hδ) ∈ χ,
    (χ.decode _).get h' = h.t ∧
    (σ.cond ⟨(S.cpos _).get hN, A⟩).get (cpos_dom ⟨A, inr N⟩ hN) =
    SpecCondition.inflexibleCoe A h.path χ
  inflexibleBot_spec (A : ExtendedIndex β) (N : NearLitter) (hN : ⟨A, inr N⟩ ∈ S)
    (h : InflexibleBot A N.1) (ha : ⟨h.path.B.cons (bot_lt_coe _), inl h.a⟩ ∈ S) :
    (σ.cond ⟨(S.cpos _).get hN, A⟩).get (cpos_dom ⟨A, inr N⟩ hN) =
    SpecCondition.inflexibleBot A h.path ⟨(S.cpos _).get ha, h.path.B.cons (bot_lt_coe _)⟩

theorem before_comp_supports {S : OrdSupport β} (hS : S.Strong)
    {A : ExtendedIndex β} {N : NearLitter} (h : InflexibleCoe A N.1) (hN : ⟨A, inr N⟩ ∈ S) :
    MulAction.Supports (Allowable h.path.δ)
      {c | c ∈ (S.before ((S.cpos _).get hN)).comp h.path.δ (h.path.B.cons h.path.hδ)} h.t := by
  intro ρ hρ
  refine (reducedSupport α h.t).supports ?_ ?_
  intros c hc
  refine hρ ?_
  rw [mem_setOf, OrdSupport.mem_comp (h.path.δ : Iic α), OrdSupport.mem_before]
  refine ⟨?_, ?_⟩
  · refine hS.transConstrains_mem _ ⟨A, inr N⟩ ?_ ?_ hN
    · exact hc.2.comp _
    · obtain ⟨d, hd₁, hd₂⟩ := hc.1
      refine Relation.TransGen.trans_right (reflTransConstrains_comp hd₂ _) ?_
      refine transConstrains_nearLitter ?_
      have := Constrains.fuzz h.path.hδ h.path.hε h.path.hδε h.path.B h.t d hd₁
      rw [← h.path.hA, ← h.hL] at this
      exact Relation.TransGen.single this
  · simp only [hS.cpos_get_eq, pos_atomNearLitter_inr]
    refine lt_of_lt_of_le ?_ (litter_le_nearLitter N)
    simp only [h.hL]
    exact pos_lt_of_mem_reducedSupport α h.path.hδ h.path.hε h.path.hδε h.path.B h.t c hc

noncomputable def codeBefore {S : OrdSupport β} (hS : S.Strong)
    {A : ExtendedIndex β} {N : NearLitter} (h : InflexibleCoe A N.1) (hN : ⟨A, inr N⟩ ∈ S) :
    CodingFunction (h.path.δ : Iic α) :=
  CodingFunction.code ((S.before ((S.cpos _).get hN)).comp h.path.δ (h.path.B.cons h.path.hδ)) h.t
    (before_comp_supports hS h hN)

noncomputable def specConditionAt {S : OrdSupport β} (hS : S.Strong) :
    (c : SupportCondition β) → c ∈ S → SpecCondition β
  | ⟨A, Sum.inl a⟩ => fun _ => SpecCondition.atom A ⟨pos a.1, A⟩
  | ⟨A, Sum.inr N⟩ => fun hN =>
      if h : Nonempty (InflexibleCoe A N.1) then
        SpecCondition.inflexibleCoe A h.some.path (codeBefore hS h.some hN)
      else if h : Nonempty (InflexibleBot A N.1) then
        SpecCondition.inflexibleBot A h.some.path ⟨pos h.some.a, h.some.path.B.cons (bot_lt_coe _)⟩
      else
        SpecCondition.flexible A

theorem specConditionAt_congr {S : OrdSupport β} {hS : S.Strong} {c d : SupportCondition β}
    {hc : c ∈ S} {hd : d ∈ S} (h : c = d) :
    specConditionAt hS c hc = specConditionAt hS d hd := by
  subst h
  rfl

@[simp]
theorem specConditionAt_atom {S : OrdSupport β} {hS : S.Strong}
    (A : ExtendedIndex β) (a : Atom) (h : ⟨A, inl a⟩ ∈ S) :
    specConditionAt hS ⟨A, inl a⟩ h = SpecCondition.atom A ⟨pos a.1, A⟩ :=
  rfl

theorem specConditionAt_inflexibleCoe {S : OrdSupport β} {hS : S.Strong}
    (A : ExtendedIndex β) (N : NearLitter) (hNS : ⟨A, inr N⟩ ∈ S) (hN : InflexibleCoe A N.1) :
    specConditionAt hS ⟨A, inr N⟩ hNS =
    SpecCondition.inflexibleCoe A hN.path (codeBefore hS hN hNS) := by
  rw [specConditionAt]
  dsimp only
  rw [dif_pos ⟨hN⟩]
  have : hN = Nonempty.some ⟨hN⟩ := Subsingleton.elim _ _
  rw [this]

theorem specConditionAt_inflexibleBot {S : OrdSupport β} {hS : S.Strong}
    (A : ExtendedIndex β) (N : NearLitter) (hNS : ⟨A, inr N⟩ ∈ S) (hN : InflexibleBot A N.1) :
    specConditionAt hS ⟨A, inr N⟩ hNS =
    SpecCondition.inflexibleBot A hN.path ⟨pos hN.a, hN.path.B.cons (bot_lt_coe _)⟩ := by
  rw [specConditionAt]
  dsimp only
  rw [dif_neg, dif_pos ⟨hN⟩]
  · have : hN = Nonempty.some ⟨hN⟩ := Subsingleton.elim _ _
    rw [this]
  · rintro ⟨hN'⟩
    exact inflexibleBot_inflexibleCoe hN hN'

theorem specConditionAt_flexible {S : OrdSupport β} {hS : S.Strong}
    (A : ExtendedIndex β) (N : NearLitter) (hNS : ⟨A, inr N⟩ ∈ S) (hN : Flexible α A N.1) :
    specConditionAt hS ⟨A, inr N⟩ hNS = SpecCondition.flexible A := by
  rw [specConditionAt]
  dsimp only
  rw [flexible_iff_not_inflexibleBot_inflexibleCoe] at hN
  rw [dif_neg, dif_neg]
  · exact not_nonempty_iff.mpr hN.1
  · exact not_nonempty_iff.mpr hN.2

noncomputable def spec (S : OrdSupport β) (hS : S.Strong) : Spec β where
  cond i := ⟨∃ c ∈ S, i = ⟨pos c.value, c.path⟩,
    fun h => specConditionAt hS h.choose h.choose_spec.1⟩
  dom_small := by
    simp only [PFun.dom_mk]
    refine lt_of_le_of_lt ?_ S.dom_small
    refine ⟨⟨fun i => ⟨i.prop.choose, i.prop.choose_spec.1⟩, ?_⟩⟩
    intros i j h
    refine Subtype.coe_injective ?_
    refine (i.prop.choose_spec.2).trans (Eq.trans ?_ j.prop.choose_spec.2.symm)
    simp only [coe_setOf, mem_setOf_eq, Subtype.mk.injEq] at h
    rw [h]

theorem spec_cond_get {S : OrdSupport β} {hS : S.Strong}
    (c : SupportCondition β) (hc : c ∈ S) :
    ((spec S hS).cond ⟨pos c.value, c.path⟩).get ⟨c, hc, rfl⟩ = specConditionAt hS c hc := by
  unfold spec
  refine specConditionAt_congr ?_
  suffices : ∀ h : (∃ c' ∈ S, (⟨pos c.value, c.path⟩ : Time β) = ⟨pos c'.value, c'.path⟩),
    h.choose = c
  · rw [this]
  intro h
  have := h.choose_spec.2.symm
  refine SupportCondition.ext _ _ ?_ ?_
  · exact congr_arg Prod.snd this
  · exact pos_injective (congr_arg Prod.fst this)

theorem spec_cond_mk_get {S : OrdSupport β} {hS : S.Strong}
    (A : ExtendedIndex β) (x : Atom ⊕ NearLitter) (hc : ⟨A, x⟩ ∈ S) :
    ((spec S hS).cond ⟨pos x, A⟩).get ⟨⟨A, x⟩, hc, rfl⟩ = specConditionAt hS ⟨A, x⟩ hc :=
  spec_cond_get ⟨A, x⟩ hc

/-- Every strong support has a specification, described by `spec`. -/
theorem spec_specifies {S : OrdSupport β} (hS : S.Strong) :
    Specifies (spec S hS) S := by
  constructor
  case cpos_dom =>
    intro c hc
    refine ⟨c, hc, ?_⟩
    rw [hS.cpos_get_eq]
  case exists_mem_of_dom =>
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨c, hc, rfl, ?_⟩
    rw [hS.cpos_get_eq]
  case atom_spec =>
    intro A a N ha hN haN
    simp_rw [hS.cpos_get_eq]
    rw [spec_cond_mk_get A (inl a) ha]
    simp only [specConditionAt_atom, pos_atomNearLitter_inr, SpecCondition.atom.injEq, true_and]
    suffices : N = a.1.toNearLitter
    · cases this
      rfl
    have := hS.reduced_of_mem _ hN
    cases this
    cases haN
    rfl
  case flexible_spec =>
    intro A N hN₁ hN₂
    simp_rw [hS.cpos_get_eq]
    rw [spec_cond_mk_get A (inr N) hN₁, specConditionAt_flexible A N hN₁ hN₂]
  case inflexibleCoe_spec =>
    intro A N hN₁ hN₂
    refine ⟨codeBefore hS hN₂ hN₁, ?_, ?_, ?_⟩
    · rw [codeBefore]
      exact CodingFunction.mem_code_self
    · simp only [codeBefore, CodingFunction.code_decode, Part.get_some]
    · simp_rw [hS.cpos_get_eq]
      rw [spec_cond_mk_get A (inr N) hN₁, specConditionAt_inflexibleCoe A N hN₁ hN₂]
  case inflexibleBot_spec =>
    intro A N hN₁ hN₂ ha
    simp_rw [hS.cpos_get_eq]
    rw [spec_cond_mk_get A (inr N) hN₁,
      specConditionAt_inflexibleBot A N hN₁ hN₂, pos_atomNearLitter_inl]

end ConNF
