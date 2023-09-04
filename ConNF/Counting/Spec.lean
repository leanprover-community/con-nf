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

noncomputable def specConditionAt (S : OrdSupport β) (hS : S.Strong) :
    (c : SupportCondition β) → c ∈ S → SpecCondition β
  | ⟨A, Sum.inl a⟩ => fun _ => SpecCondition.atom A ⟨pos a.1, A⟩
  | ⟨A, Sum.inr N⟩ => fun hN =>
      if h : Nonempty (InflexibleCoe A N.1) then
        SpecCondition.inflexibleCoe A h.some.path (codeBefore hS h.some hN)
      else if h : Nonempty (InflexibleBot A N.1) then
        SpecCondition.inflexibleBot A h.some.path ⟨pos h.some.a, h.some.path.B.cons (bot_lt_coe _)⟩
      else
        SpecCondition.flexible A

end ConNF
